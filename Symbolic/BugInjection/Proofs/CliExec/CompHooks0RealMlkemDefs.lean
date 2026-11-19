/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs -- proof-setup: allow-public-import

/-!
# Fast Precomputed-Matrix ML-KEM-768 Row Checker and Soundness Lemmas

Provides `mlkem768KeyPairGivenMat`, `mlkem768ValidPkFast`, `checkMlkemRowGivenMat`, and
`mlkemRowGivenMat_sound` so matrix sampling and key generation are certified in low-memory
`rfl_kernel` modules well under 16 GiB RSS.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs

open CryptoGames.MLKEM (
  Poly byteDecodeRaw byteEncode mlkem768Incremental mlkem768KeyPairWith mlkem768ValidPk
  mlkemQ polyAdd polyNtt sampleMatrixWith sampleNtt sampleVecCbd2 toByteVec vecDotNtt zeroPoly
)
open CryptoGames.SHA3 (sha3_256List sha3_512List)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (
  arrayGetDFast arrayGetDFast_eq arrayMapFast arrayMapFast_eq arrayOfFnFast arrayOfFnFast_eq
  forceListBV8 forceListBV8_eq sha3_256Fast sha3_256Fast_eq sha3_512Fast sha3_512Fast_eq
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs (
  byteDecodeRawFast byteDecodeRawFast_eq byteEncodeFast byteEncodeFast_eq checkMatrixRowFast
  checkMatrixRowFast_sound forceMatrix forceMatrix_eq forcePoly forcePoly_eq forcePolyVec
  forcePolyVec_eq polyAddFast polyAddFast_eq polyNttFast polyNttFast_eq
  sampleVecCbd2Fast sampleVecCbd2Fast_eq toByteVec_toList_of_length vecDotNttFast vecDotNttFast_eq
)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

@[expose] def mlkem768ValidPkFast (hdr ek : List (BitVec 8)) : Bool :=
  if hdr.length != 64 || ek.length != 1152 then false else
  forceListBV8 hdr fun hdr' =>
  forceListBV8 ek fun ek' =>
  let seed := hdr'.take 32
  let pkHash := (hdr'.drop 32).take 32
  let pk := ek' ++ seed
  let hashOk := sha3_256Fast pk == pkHash
  let domainOk := (List.range 3).all fun i =>
    forcePoly (byteDecodeRawFast 12 ((ek'.drop (384 * i)).take 384)) fun raw =>
    (List.range 256).all fun j => decide (arrayGetDFast raw j 0 < mlkemQ)
  hashOk && domainOk

theorem mlkem768ValidPkFast_eq (hdr ek : List (BitVec 8)) :
    mlkem768ValidPkFast hdr ek = mlkem768ValidPk hdr ek := by
  unfold mlkem768ValidPkFast mlkem768ValidPk
  simp only [forceListBV8_eq, forcePoly_eq, sha3_256Fast_eq, byteDecodeRawFast_eq, arrayGetDFast_eq]

@[expose] def mlkem768ValidPkDomainFast (ek : List (BitVec 8)) : Bool :=
  forceListBV8 ek fun ek' =>
  (List.range 3).all fun i =>
    forcePoly (byteDecodeRawFast 12 ((ek'.drop (384 * i)).take 384)) fun raw =>
    (List.range 256).all fun j => decide (arrayGetDFast raw j 0 < mlkemQ)

theorem mlkem768ValidPkDomainFast_eq (ek : List (BitVec 8)) :
    mlkem768ValidPkDomainFast ek =
      ((List.range 3).all fun i =>
        let raw := byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)
        (List.range 256).all fun j => decide (raw.getD j 0 < mlkemQ)) := by
  unfold mlkem768ValidPkDomainFast
  simp only [forceListBV8_eq, forcePoly_eq, byteDecodeRawFast_eq, arrayGetDFast_eq]

@[expose] def mlkem768KeyPairGivenMat (aMat : Array (Array Poly)) (seed64 : List (BitVec 8)) :
    List (BitVec 8) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) :=
  forceListBV8 (seed64.take 32) fun d =>
  forceListBV8 ((seed64.drop 32).take 32) fun z =>
  forceListBV8 (sha3_512Fast (d ++ [3#8])) fun g =>
  forceListBV8 (g.take 32) fun rho =>
  let sigma := (g.drop 32).take 32
  forceMatrix aMat fun aMat =>
  forcePolyVec (arrayMapFast polyNttFast (sampleVecCbd2Fast 3 sigma 0)) fun sHat =>
  forcePolyVec (arrayMapFast polyNttFast (sampleVecCbd2Fast 3 sigma 3)) fun eHat =>
  forcePolyVec (arrayOfFnFast 3 fun i =>
    polyAddFast (vecDotNttFast 3 (arrayGetDFast aMat i (Array.mk [])) sHat)
      (arrayGetDFast eHat i zeroPoly))
    fun tHat =>
  let dkPke :=
    ((List.range 3).map fun i => byteEncodeFast 12 (arrayGetDFast sHat i zeroPoly)).flatten
  let pk2 :=
    ((List.range 3).map fun i => byteEncodeFast 12 (arrayGetDFast tHat i zeroPoly)).flatten
  forceListBV8 (pk2 ++ rho) fun pk =>
  forceListBV8 (sha3_256Fast pk) fun hPk =>
  (forceListBV8 (dkPke ++ pk ++ hPk ++ z) id, rho, pk, hPk)

@[expose] def checkMlkemRowGivenMat (aMat : Array (Array Poly))
    (rhoLit seed dkExp : List (BitVec 8)) : Bool :=
  forceListBV8 seed fun s =>
  forceListBV8 dkExp fun dkExp =>
  let (dk, rho, pk, hPk) := mlkem768KeyPairGivenMat aMat s
  let hdr := (dkExp.drop 2304).take 64
  let ek := (dkExp.drop 1152).take 1152
  (aMat.toList.length == 3) &&
  (rho == rhoLit) &&
  (dk == dkExp) &&
  (hdr.length == 64) &&
  (ek.length == 1152) &&
  ((ek ++ hdr.take 32) == pk) &&
  (((hdr.drop 32).take 32) == hPk) &&
  mlkem768ValidPkDomainFast ek

theorem mlkem_aMat_eq_of_rows {aMat : Array (Array Poly)} {rho : List (BitVec 8)}
    (hlen : aMat.size = 3)
    (hm01 : (checkMatrixRowFast 3 0 rho true (arrayGetDFast aMat 0 (Array.mk [])) &&
             checkMatrixRowFast 3 1 rho true (arrayGetDFast aMat 1 (Array.mk []))) = true)
    (hm2 : checkMatrixRowFast 3 2 rho true (arrayGetDFast aMat 2 (Array.mk [])) = true) :
    aMat = sampleMatrixWith sampleNtt 3 rho true := by
  rcases (Bool.and_eq_true _ _).mp hm01 with ⟨hm0, hm1⟩
  unfold sampleMatrixWith
  apply Array.ext
  · rw [hlen, Array.size_ofFn]
  · intro r hr1 hr2
    rw [Array.getElem_ofFn]
    have hget : aMat[r]'hr1 = arrayGetDFast aMat r (Array.mk []) := by
      rw [arrayGetDFast_eq]
      simp [Array.getD, hr1]
    have hr : r < 3 := by simpa using hr2
    rcases r with _ | _ | _ | r
    · rw [hget, checkMatrixRowFast_sound hm0]
    · rw [hget, checkMatrixRowFast_sound hm1]
    · rw [hget, checkMatrixRowFast_sound hm2]
    · omega

theorem mlkemRowGivenMat_sound (seed : List.Vector (BitVec 8) 64)
    {aMat : Array (Array Poly)} {rhoLit dkExp : List (BitVec 8)}
    (hdk_len : dkExp.length = 2400)
    (hm01 : (checkMatrixRowFast 3 0 rhoLit true (arrayGetDFast aMat 0 (Array.mk [])) &&
             checkMatrixRowFast 3 1 rhoLit true (arrayGetDFast aMat 1 (Array.mk []))) = true)
    (hm2 : checkMatrixRowFast 3 2 rhoLit true (arrayGetDFast aMat 2 (Array.mk [])) = true)
    (hrow : checkMlkemRowGivenMat aMat rhoLit seed.toList dkExp = true) :
    (mlkem768Incremental.keyPair seed).toList = dkExp ∧
    mlkem768ValidPk
      ((dkExp.drop 2304).take 64)
      ((dkExp.drop 1152).take 1152) = true := by
  unfold checkMlkemRowGivenMat mlkem768KeyPairGivenMat at hrow
  simp only [forceListBV8_eq, forceMatrix_eq, forcePolyVec_eq, id_eq, Bool.and_eq_true] at hrow
  rcases hrow with ⟨⟨⟨⟨⟨⟨⟨hlen', hrho'⟩, hdk'⟩, hhdr_len'⟩, hek_len'⟩, hpk'⟩, hhpk'⟩, hdom⟩
  have hlen : aMat.size = 3 := beq_iff_eq.mp hlen'
  have haMat_lit : aMat = sampleMatrixWith sampleNtt 3 rhoLit true :=
    mlkem_aMat_eq_of_rows hlen hm01 hm2
  have hrho : (sha3_512List (seed.toList.take 32 ++ [3#8])).take 32 = rhoLit := by
    rw [← sha3_512Fast_eq]
    exact beq_iff_eq.mp hrho'
  have haMat :
      aMat = sampleMatrixWith sampleNtt 3 ((sha3_512List (seed.toList.take 32 ++ [3#8])).take 32) true := by
    rw [hrho, haMat_lit]
  have hempty : Array.mk ([] : List Poly) = #[] := rfl
  have hdk_eq : mlkem768KeyPairWith sampleNtt seed.toList = dkExp := by
    have hdk := beq_iff_eq.mp hdk'
    rw [hempty, arrayMapFast_eq, arrayMapFast_eq, arrayOfFnFast_eq] at hdk
    simp only [arrayGetDFast_eq, sha3_512Fast_eq, sha3_256Fast_eq, sampleVecCbd2Fast_eq,
      show polyNttFast = polyNtt from funext polyNttFast_eq,
      polyAddFast_eq, vecDotNttFast_eq, byteEncodeFast_eq] at hdk
    unfold mlkem768KeyPairWith
    dsimp only
    rw [← haMat]
    exact hdk
  refine ⟨?_, ?_⟩
  · change (toByteVec 2400 (mlkem768KeyPairWith sampleNtt seed.toList)).toList = dkExp
    rw [hdk_eq, toByteVec_toList_of_length hdk_len]
  · set hdr := (dkExp.drop 2304).take 64
    set ek := (dkExp.drop 1152).take 1152
    have hhdr_len : hdr.length = 64 := beq_iff_eq.mp hhdr_len'
    have hek_len : ek.length = 1152 := beq_iff_eq.mp hek_len'
    have hpk_eq := beq_iff_eq.mp hpk'
    have hhpk_eq := beq_iff_eq.mp hhpk'
    rw [sha3_256Fast_eq] at hhpk_eq
    rw [mlkem768ValidPkDomainFast_eq] at hdom
    unfold mlkem768ValidPk
    have hcond : (hdr.length != 64 || ek.length != 1152) = false := by
      simp [hhdr_len, hek_len]
    rw [hcond]
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hpk_eq, hhpk_eq, beq_self_eq_true, Bool.true_and]
    exact hdom

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs
