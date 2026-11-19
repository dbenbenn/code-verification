/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberKey
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat01
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat23
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0Dec
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow1
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow1Dec
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow2
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow2Dec
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit

/-!
# Certified `compHooks0` Kyber-1024 Rows and Hybrid `kyber1024EncapsVec` / `kyber1024DecapsVec`

Combines the parallel `rfl_kernel` certificates in `CompHooks0RealKyberMat{01,23}`,
`CompHooks0RealKyberKey`, and `CompHooks0RealKyberRow{0,1,2}{,Dec}` and exports
`kyberEncapsHybrid = kyber1024EncapsVec` and `kyberDecapsHybrid = kyber1024DecapsVec`.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyber

open CryptoGames.MLKEM (
  Poly byteDecodeMod kyber1024Decaps kyber1024DecapsVec kyber1024Encaps kyber1024EncapsVec
  sampleMatrixWith sampleNtt
)
open CryptoGames.SHA3 (sha3_256List)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (
  arrayGetDFast arrayGetDFast_eq arrayOfFnFast_eq forceListBV8_eq sha3_256Fast_eq
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs (
  byteDecodeModFast_eq checkMatrixRowFast checkMatrixRowFast_sound kyberRow_sound
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberKey (kyber_key_lits_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits (
  compKyberATLit compKyberCt0 compKyberCt0_length compKyberCt1 compKyberCt1_length compKyberCt2
  compKyberCt2_length compKyberE0 compKyberE1 compKyberE2 compKyberHPkLit compKyberPk
  compKyberPk_length compKyberSHatLit compKyberSk compKyberSs0 compKyberSs0_length compKyberSs1
  compKyberSs1_length compKyberSs2 compKyberSs2_length compKyberTHatLit
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat01 (kyber_mat_01_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat23 (kyber_mat_23_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0 (kyber_row0_enc_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0Dec (kyber_row0_dec_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow1 (kyber_row1_enc_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow1Dec (kyber_row1_dec_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow2 (kyber_row2_enc_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow2Dec (kyber_row2_dec_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit (
  checkKyberKeyLits checkKyberRow_of_split
)

public section
set_option autoImplicit false

private theorem list_eq_of_map {α β : Type} {f : α → β} (hinj : Function.Injective f) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    injection h with hxy htl
    rw [hinj hxy, list_eq_of_map hinj htl]

private theorem arrayPoly_eq_of_map_toList {v : Array Poly} {n : Nat} {f : Nat → Poly}
    (h : v.toList.map Array.toList = (List.range n).map (fun i => (f i).toList)) :
    v = Array.ofFn (n := n) fun ⟨i, _⟩ => f i := by
  have hinj : Function.Injective (Array.toList (α := Nat)) :=
    fun ⟨a⟩ ⟨b⟩ hab => congrArg Array.mk hab
  have hlist : v.toList = (List.range n).map f := by
    apply list_eq_of_map hinj
    rw [List.map_map]
    exact h
  rcases v with ⟨xs⟩
  dsimp only at hlist
  subst hlist
  exact arrayOfFnFast_eq n f

private theorem kyber_aMat_eq_of_rows {aMat : Array (Array Poly)} {rho : List (BitVec 8)}
    (hlen : aMat.size = 4)
    (hm01 : (checkMatrixRowFast 4 0 rho false (arrayGetDFast aMat 0 (Array.mk [])) &&
             checkMatrixRowFast 4 1 rho false (arrayGetDFast aMat 1 (Array.mk []))) = true)
    (hm23 : (checkMatrixRowFast 4 2 rho false (arrayGetDFast aMat 2 (Array.mk [])) &&
             checkMatrixRowFast 4 3 rho false (arrayGetDFast aMat 3 (Array.mk []))) = true) :
    aMat = sampleMatrixWith sampleNtt 4 rho false := by
  rcases (Bool.and_eq_true _ _).mp hm01 with ⟨hm0, hm1⟩
  rcases (Bool.and_eq_true _ _).mp hm23 with ⟨hm2, hm3⟩
  unfold sampleMatrixWith
  apply Array.ext
  · rw [hlen, Array.size_ofFn]
  · intro r hr1 hr2
    rw [Array.getElem_ofFn]
    have hget : aMat[r]'hr1 = arrayGetDFast aMat r (Array.mk []) := by
      rw [arrayGetDFast_eq]
      simp [Array.getD, hr1]
    have hr : r < 4 := by simpa using hr2
    rcases r with _ | _ | _ | _ | r
    · rw [hget, checkMatrixRowFast_sound hm0]
    · rw [hget, checkMatrixRowFast_sound hm1]
    · rw [hget, checkMatrixRowFast_sound hm2]
    · rw [hget, checkMatrixRowFast_sound hm3]
    · omega

private theorem kyber_aTrans_eq :
    compKyberATLit = sampleMatrixWith sampleNtt 4 ((compKyberPk.drop 1536).take 32) false := by
  have hkey := kyber_key_lits_ok
  unfold checkKyberKeyLits at hkey
  rw [forceListBV8_eq, forceListBV8_eq] at hkey
  rcases (Bool.and_eq_true _ _).mp hkey with ⟨hkey4, _⟩
  rcases (Bool.and_eq_true _ _).mp hkey4 with ⟨hkey3, _⟩
  rcases (Bool.and_eq_true _ _).mp hkey3 with ⟨hkey2, _⟩
  rcases (Bool.and_eq_true _ _).mp hkey2 with ⟨hkey1, _⟩
  rcases (Bool.and_eq_true _ _).mp hkey1 with ⟨hlen', _⟩
  exact kyber_aMat_eq_of_rows (beq_iff_eq.mp hlen') kyber_mat_01_ok kyber_mat_23_ok

private theorem kyber_rows_unpacked :
    (kyber1024Encaps compKyberPk compKyberE0 = (compKyberCt0, compKyberSs0) ∧
     kyber1024Decaps compKyberSk compKyberCt0 = compKyberSs0) ∧
    (kyber1024Encaps compKyberPk compKyberE1 = (compKyberCt1, compKyberSs1) ∧
     kyber1024Decaps compKyberSk compKyberCt1 = compKyberSs1) ∧
    (kyber1024Encaps compKyberPk compKyberE2 = (compKyberCt2, compKyberSs2) ∧
     kyber1024Decaps compKyberSk compKyberCt2 = compKyberSs2) := by
  have hkey := kyber_key_lits_ok
  unfold checkKyberKeyLits at hkey
  rw [forceListBV8_eq, forceListBV8_eq] at hkey
  rcases (Bool.and_eq_true _ _).mp hkey with ⟨hkey4, hsk_hpk'⟩
  rcases (Bool.and_eq_true _ _).mp hkey4 with ⟨hkey3, hsk_pk'⟩
  rcases (Bool.and_eq_true _ _).mp hkey3 with ⟨hkey2, hhPk'⟩
  rcases (Bool.and_eq_true _ _).mp hkey2 with ⟨hkey1, hsHat'⟩
  rcases (Bool.and_eq_true _ _).mp hkey1 with ⟨_, htHat'⟩
  have htHat : compKyberTHatLit =
      Array.ofFn (n := 4) fun ⟨i, _⟩ => byteDecodeMod 12 ((compKyberPk.drop (384 * i)).take 384) := by
    rw [arrayPoly_eq_of_map_toList (beq_iff_eq.mp htHat')]
    apply congrArg (Array.ofFn (n := 4)); funext ⟨i, _⟩; exact byteDecodeModFast_eq 12 _
  have hsHat : compKyberSHatLit =
      Array.ofFn (n := 4) fun ⟨i, _⟩ =>
        byteDecodeMod 12 (((compKyberSk.take 1536).drop (384 * i)).take 384) := by
    rw [arrayPoly_eq_of_map_toList (beq_iff_eq.mp hsHat')]
    apply congrArg (Array.ofFn (n := 4)); funext ⟨i, _⟩; exact byteDecodeModFast_eq 12 _
  have hhPk : compKyberHPkLit = sha3_256List compKyberPk := by
    rw [beq_iff_eq.mp hhPk', sha3_256Fast_eq]
  have hsk_pk : (compKyberSk.drop 1536).take 1568 = compKyberPk := beq_iff_eq.mp hsk_pk'
  have hsk_hpk : (compKyberSk.drop 3104).take 32 = compKyberHPkLit := beq_iff_eq.mp hsk_hpk'
  have r0 := checkKyberRow_of_split kyber_row0_enc_ok kyber_row0_dec_ok
  have r1 := checkKyberRow_of_split kyber_row1_enc_ok kyber_row1_dec_ok
  have r2 := checkKyberRow_of_split kyber_row2_enc_ok kyber_row2_dec_ok
  exact ⟨kyberRow_sound compKyberPk_length compKyberCt0_length compKyberSs0_length
           kyber_aTrans_eq htHat hsHat hhPk hsk_pk hsk_hpk r0,
         kyberRow_sound compKyberPk_length compKyberCt1_length compKyberSs1_length
           kyber_aTrans_eq htHat hsHat hhPk hsk_pk hsk_hpk r1,
         kyberRow_sound compKyberPk_length compKyberCt2_length compKyberSs2_length
           kyber_aTrans_eq htHat hsHat hhPk hsk_pk hsk_hpk r2⟩

@[expose] noncomputable def kyberEncapsHybrid
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32 :=
  if pk.toList == compKyberPk then
    if rand.toList == compKyberE0 then
      (⟨compKyberCt0, compKyberCt0_length⟩, ⟨compKyberSs0, compKyberSs0_length⟩)
    else if rand.toList == compKyberE1 then
      (⟨compKyberCt1, compKyberCt1_length⟩, ⟨compKyberSs1, compKyberSs1_length⟩)
    else if rand.toList == compKyberE2 then
      (⟨compKyberCt2, compKyberCt2_length⟩, ⟨compKyberSs2, compKyberSs2_length⟩)
    else
      kyber1024EncapsVec pk rand
  else
    kyber1024EncapsVec pk rand

@[expose] noncomputable def kyberDecapsHybrid
    (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568) :
    List.Vector (BitVec 8) 32 :=
  if sk.toList == compKyberSk then
    if ct.toList == compKyberCt0 then
      ⟨compKyberSs0, compKyberSs0_length⟩
    else if ct.toList == compKyberCt1 then
      ⟨compKyberSs1, compKyberSs1_length⟩
    else if ct.toList == compKyberCt2 then
      ⟨compKyberSs2, compKyberSs2_length⟩
    else
      kyber1024DecapsVec sk ct
  else
    kyber1024DecapsVec sk ct

private theorem vec_mk_toList {α : Type} {n : Nat} (xs : List α) (h : xs.length = n) :
    List.Vector.toList ⟨xs, h⟩ = xs := rfl

private theorem kyber1024EncapsVec_fst_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 := by
  dsimp only [kyber1024EncapsVec, List.Vector.toList]

private theorem kyber1024EncapsVec_snd_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2 := by
  dsimp only [kyber1024EncapsVec, List.Vector.toList]

private theorem kyber1024DecapsVec_toList
    (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568) :
    (kyber1024DecapsVec sk ct).toList = kyber1024Decaps sk.toList ct.toList := by
  dsimp only [kyber1024DecapsVec, List.Vector.toList]

theorem kyberEncapsHybrid_eq : kyberEncapsHybrid = kyber1024EncapsVec := by
  rcases kyber_rows_unpacked with ⟨⟨he0, _⟩, ⟨he1, _⟩, ⟨he2, _⟩⟩
  funext pk rand
  unfold kyberEncapsHybrid
  by_cases hpk : (pk.toList == compKyberPk) = true
  · simp only [hpk, ↓reduceIte]
    have hpk' : pk.toList = compKyberPk := beq_iff_eq.mp hpk
    by_cases hr0 : (rand.toList == compKyberE0) = true
    · simp only [hr0, ↓reduceIte]
      apply Prod.ext <;> apply List.Vector.eq
      · rw [vec_mk_toList, kyber1024EncapsVec_fst_toList, hpk', beq_iff_eq.mp hr0, he0]
      · rw [vec_mk_toList, kyber1024EncapsVec_snd_toList, hpk', beq_iff_eq.mp hr0, he0]
    · simp only [Bool.not_eq_true] at hr0
      simp only [hr0, Bool.false_eq_true, ↓reduceIte]
      by_cases hr1 : (rand.toList == compKyberE1) = true
      · simp only [hr1, ↓reduceIte]
        apply Prod.ext <;> apply List.Vector.eq
        · rw [vec_mk_toList, kyber1024EncapsVec_fst_toList, hpk', beq_iff_eq.mp hr1, he1]
        · rw [vec_mk_toList, kyber1024EncapsVec_snd_toList, hpk', beq_iff_eq.mp hr1, he1]
      · simp only [Bool.not_eq_true] at hr1
        simp only [hr1, Bool.false_eq_true, ↓reduceIte]
        by_cases hr2 : (rand.toList == compKyberE2) = true
        · simp only [hr2, ↓reduceIte]
          apply Prod.ext <;> apply List.Vector.eq
          · rw [vec_mk_toList, kyber1024EncapsVec_fst_toList, hpk', beq_iff_eq.mp hr2, he2]
          · rw [vec_mk_toList, kyber1024EncapsVec_snd_toList, hpk', beq_iff_eq.mp hr2, he2]
        · simp only [Bool.not_eq_true] at hr2
          simp only [hr2, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.not_eq_true] at hpk
    simp only [hpk, Bool.false_eq_true, ↓reduceIte]

theorem kyberDecapsHybrid_eq : kyberDecapsHybrid = kyber1024DecapsVec := by
  rcases kyber_rows_unpacked with ⟨⟨_, hd0⟩, ⟨_, hd1⟩, ⟨_, hd2⟩⟩
  funext sk ct
  unfold kyberDecapsHybrid
  by_cases hsk : (sk.toList == compKyberSk) = true
  · simp only [hsk, ↓reduceIte]
    have hsk' : sk.toList = compKyberSk := beq_iff_eq.mp hsk
    by_cases hc0 : (ct.toList == compKyberCt0) = true
    · simp only [hc0, ↓reduceIte]
      apply List.Vector.eq
      rw [vec_mk_toList, kyber1024DecapsVec_toList, hsk', beq_iff_eq.mp hc0, hd0]
    · simp only [Bool.not_eq_true] at hc0
      simp only [hc0, Bool.false_eq_true, ↓reduceIte]
      by_cases hc1 : (ct.toList == compKyberCt1) = true
      · simp only [hc1, ↓reduceIte]
        apply List.Vector.eq
        rw [vec_mk_toList, kyber1024DecapsVec_toList, hsk', beq_iff_eq.mp hc1, hd1]
      · simp only [Bool.not_eq_true] at hc1
        simp only [hc1, Bool.false_eq_true, ↓reduceIte]
        by_cases hc2 : (ct.toList == compKyberCt2) = true
        · simp only [hc2, ↓reduceIte]
          apply List.Vector.eq
          rw [vec_mk_toList, kyber1024DecapsVec_toList, hsk', beq_iff_eq.mp hc2, hd2]
        · simp only [Bool.not_eq_true] at hc2
          simp only [hc2, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.false_eq_true, ↓reduceIte]

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyber
