/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec

/-!
# FIPS 203 `mlkem768Encaps2Fips` and `EsWellFormed` Equivalence

Defines the FIPS 203 `mlkem768Encaps2Fips` over `ℤ_3329` and the `EsWellFormed` invariant, proves
preservation under `encaps1`, establishes `mlkem768Encaps2List_eq_fips_of_esWellFormed`, and
derives `indCpaEncryptWith` roundtrip corollaries.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemEncaps2Fips

open CryptoVerification.LibsignalSpqrV1 (Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ zeroPoly polyAdd polyNtt polyInvNtt vecDotNtt bytesToBits bitsToBytes
  byteEncode byteDecodeRaw byteDecodeMod compressAndEncode decodeAndDecompress samplePolyCbd2
  sampleVecCbd2 sampleNtt polyToCenteredI16Bytes bytesToPoly16 neonBarrettReduce16
  neonMontgomeryMul16 neonPolyNttMul16 neonInvNttMontgomery16 neonCompressSerialize4
  mlkem768Encaps1With mlkem768Encaps2List indCpaEncryptWith toByteVec mlkem768Incremental)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents PolyRepresentsMontInv polyAdd16 neonVecDotNtt3_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  PolyCanonical polyAdd_canonical vecDotNtt_canonical samplePolyCbd2_canonical polyNtt_canonical
  neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  toInt_add_of_bounds neonBarrettReduce16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  neonCompressSerialize4_eq_compressAndEncode decodeAndDecompress_poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE bytesToPoly16_packHalfwordsLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes (
  encapsStateBytes polyToCenteredI16Bytes_length encapsStateBytes_eq_append encapsStateBytes_length
  encapsStateBytes_rHat_slice encapsStateBytes_e2_slice toByteVec_eq_of_length mlkem768Encaps1With_eq)

private theorem getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α) (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by simp [Array.getD, hi]

private theorem polyAdd_getD (a b : Poly) {i : Nat} (hi : i < 256) :
    (polyAdd a b).getD i 0 = (a.getD i 0 + b.getD i 0) % mlkemQ := by rw [polyAdd, getD_ofFn _ _ _ hi]

private theorem polyBounded16_mono {A B : Int} {p : Poly16} (hAB : A ≤ B) (hp : PolyBounded16 A p) :
    PolyBounded16 B p := ⟨hp.1, fun i hi => by have := hp.2 i hi; omega⟩

/-! ## 1. Pure Textbook FIPS 203 `mlkem768Encaps2Fips` & `EsWellFormed` -/

/-- Reduce signed `i16` lanes of `p : Poly16` modulo `mlkemQ = 3329` into canonical `[0, 3328]` `Poly`. -/
@[expose] def poly16ToModQ (p : Poly16) : Poly := p.map fun x => (x.toInt % (mlkemQ : Int)).toNat

/-- Pure textbook FIPS 203 `encapsulate2` over `ℤ_3329` (`K = 3, d_v = 4`). -/
@[expose] def mlkem768Encaps2Fips (es ek : List (BitVec 8)) : List (BitVec 8) :=
  let tHat : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 ((ek.drop (384 * i)).take 384)
  let rHat : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    poly16ToModQ (bytesToPoly16 ((es.drop (512 * i)).take 512))
  let err2 : Poly := poly16ToModQ (bytesToPoly16 ((es.drop 1536).take 512))
  let msgPoly : Poly := decodeAndDecompress 1 ((es.drop 2048).take 32)
  compressAndEncode 4 (polyAdd (polyAdd (polyInvNtt (vecDotNtt 3 tHat rHat)) err2) msgPoly)

/-- Signed `i16` lane bounds on `rHat[0..2]` (`≤ 1664`) and `err2` (`≤ 2`) of an `EncapsState`. -/
@[expose] def EsWellFormed (es : List (BitVec 8)) : Prop :=
  (∀ j < 3, PolyBounded16 1664 (bytesToPoly16 ((es.drop (512 * j)).take 512))) ∧
  PolyBounded16 2 (bytesToPoly16 ((es.drop 1536).take 512))

@[simp] theorem mlkem768Encaps2Fips_length (es ek : List (BitVec 8)) :
    (mlkem768Encaps2Fips es ek).length = 128 := by
  simp [mlkem768Encaps2Fips, compressAndEncode, byteEncode, bitsToBytes]

theorem poly16ToModQ_canonical {p : Poly16} (hsz : p.size = 256) : PolyCanonical (poly16ToModQ p) :=
  ⟨by simp [poly16ToModQ, hsz], fun i hi => by
    rw [show (poly16ToModQ p).getD i 0 = ((p.getD i 0#16).toInt % (mlkemQ : Int)).toNat by
      simp [poly16ToModQ, Array.getD, hsz, hi]]
    dsimp [mlkemQ]; omega⟩

theorem poly16ToModQ_represents {p : Poly16} (hsz : p.size = 256) : PolyRepresents p (poly16ToModQ p) :=
  ⟨hsz, fun i hi => by
    rw [show (poly16ToModQ p).getD i 0 = ((p.getD i 0#16).toInt % (mlkemQ : Int)).toNat by
      simp [poly16ToModQ, Array.getD, hsz, hi]]
    dsimp [mlkemQ]; omega⟩

/-! ## 2. `polyToCenteredI16Bytes` Roundtrip & `EsWellFormed` Preservation on `encaps1` -/

private theorem centeredWord_spec (c : Nat) (hc : c < mlkemQ) :
    let s : Int := if c ≤ 1664 then (c : Int) else (c : Int) - 3329
    (BitVec.ofInt 16 s).toInt = s ∧ -1664 ≤ (BitVec.ofInt 16 s).toInt ∧
      (BitVec.ofInt 16 s).toInt ≤ 1664 ∧ ((BitVec.ofInt 16 s).toInt % (mlkemQ : Int)).toNat = c := by
  dsimp only [mlkemQ] at hc ⊢
  have htoInt : (BitVec.ofInt 16 (if c ≤ 1664 then (c : Int) else (c : Int) - 3329)).toInt =
      (if c ≤ 1664 then (c : Int) else (c : Int) - 3329) :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  refine ⟨htoInt, ?_, ?_, ?_⟩ <;> rw [htoInt] <;> omega

theorem bytesToPoly16_polyToCenteredI16Bytes_eq (p : Poly) :
    bytesToPoly16 (polyToCenteredI16Bytes p) =
      Array.ofFn (n := 256) fun ⟨i, _⟩ =>
        let c := p.getD i 0 % mlkemQ
        BitVec.ofInt 16 (if c ≤ 1664 then (c : Int) else (c : Int) - 3329) := by
  let f : Nat → BitVec 16 := fun i =>
    let c := p.getD i 0 % mlkemQ
    BitVec.ofInt 16 (if c ≤ 1664 then (c : Int) else (c : Int) - 3329)
  have hpack : polyToCenteredI16Bytes p = packHalfwordsLE ((List.range 256).map f) := by
    unfold polyToCenteredI16Bytes packHalfwordsLE; rw [List.map_map]; rfl
  rw [hpack, bytesToPoly16_packHalfwordsLE (by simp)]
  apply Array.ext
  · simp
  · intro i _ _; simp [f]

theorem polyBounded16_centered (p : Poly) :
    PolyBounded16 1664 (bytesToPoly16 (polyToCenteredI16Bytes p)) := by
  rw [bytesToPoly16_polyToCenteredI16Bytes_eq]
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_ofFn _ _ _ hi]; dsimp only
  have hs := centeredWord_spec (p.getD i 0 % mlkemQ) (Nat.mod_lt _ (by decide))
  exact ⟨hs.2.1, hs.2.2.1⟩

theorem polyBounded16_centered_cbd2 {e2 : Poly}
    (he2 : ∀ i < 256, e2.getD i 0 ∈ ({0, 1, 2, 3327, 3328} : List Nat)) :
    PolyBounded16 2 (bytesToPoly16 (polyToCenteredI16Bytes e2)) := by
  rw [bytesToPoly16_polyToCenteredI16Bytes_eq]
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_ofFn _ _ _ hi]; dsimp only
  have hmem : e2.getD i 0 ∈ ([0, 1, 2, 3327, 3328] : List Nat) := he2 i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rw [(centeredWord_spec (e2.getD i 0 % mlkemQ) (Nat.mod_lt _ (by decide))).1]
  dsimp only [mlkemQ]
  rcases hmem with h | h | h | h | h <;> rw [h] <;> omega

theorem poly16ToModQ_bytesToPoly16_centered {p : Poly} (hp : PolyCanonical p) :
    poly16ToModQ (bytesToPoly16 (polyToCenteredI16Bytes p)) = p := by
  rw [bytesToPoly16_polyToCenteredI16Bytes_eq]; unfold poly16ToModQ
  apply Array.ext
  · simp [hp.1]
  · intro i hi1 _
    have hi : i < 256 := by simpa using hi1
    simp only [Array.getElem_map, Array.getElem_ofFn, Nat.mod_eq_of_lt (hp.2 i hi),
      (centeredWord_spec (p.getD i 0) (hp.2 i hi)).2.2.2]
    simp [Array.getD, hp.1, hi]

private theorem bytesToBits_getD_le_one (bs : List (BitVec 8)) (k : Nat) :
    (bytesToBits bs).getD k 0 ≤ 1 := by
  unfold bytesToBits
  by_cases hk : k < 8 * bs.length
  · rw [getD_ofFn _ _ _ hk]; dsimp only; rw [Nat.and_one_is_mod]; omega
  · simp [Array.getD, hk]

theorem samplePolyCbd2_coeff_mem (bs : List (BitVec 8)) {i : Nat} (hi : i < 256) :
    (samplePolyCbd2 bs).getD i 0 ∈ ({0, 1, 2, 3327, 3328} : List Nat) := by
  change (samplePolyCbd2 bs).getD i 0 ∈ ([0, 1, 2, 3327, 3328] : List Nat)
  unfold samplePolyCbd2; rw [getD_ofFn _ _ _ hi]; dsimp only [mlkemQ]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have := bytesToBits_getD_le_one bs (4 * i)
  have := bytesToBits_getD_le_one bs (4 * i + 1)
  have := bytesToBits_getD_le_one bs (4 * i + 2)
  have := bytesToBits_getD_le_one bs (4 * i + 3)
  omega

theorem esWellFormed_encapsStateBytes (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8))
    (he2 : ∀ i < 256, e2.getD i 0 ∈ ({0, 1, 2, 3327, 3328} : List Nat)) :
    EsWellFormed (encapsStateBytes rHat e2 m) :=
  ⟨fun j hj => by rw [encapsStateBytes_rHat_slice rHat e2 m j hj]; exact polyBounded16_centered _,
   by rw [encapsStateBytes_e2_slice rHat e2 m]; exact polyBounded16_centered_cbd2 he2⟩

theorem esWellFormed_nonvacuous : ∃ es, EsWellFormed es :=
  ⟨encapsStateBytes #[zeroPoly, zeroPoly, zeroPoly] zeroPoly (List.replicate 32 0#8),
   esWellFormed_encapsStateBytes _ _ _ fun i hi => by simp [zeroPoly, Array.getD, hi]; decide⟩

theorem esWellFormed_of_encaps1With {sampler : List (BitVec 8) → Poly}
    {hdr rand ct1 es ss : List (BitVec 8)}
    (h : mlkem768Encaps1With sampler hdr rand = some (ct1, es, ss)) :
    EsWellFormed es := by
  by_cases hlt : hdr.length < 64
  · simp [mlkem768Encaps1With, hlt] at h
  · rw [mlkem768Encaps1With_eq sampler hdr rand (by omega)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, _⟩
    exact esWellFormed_encapsStateBytes _ _ _ fun _ hi => samplePolyCbd2_coeff_mem _ hi

private theorem encaps1_some_toList {hdr : Bytes} {rand : List.Vector (BitVec 8) 32}
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080}
    {ss : List.Vector (BitVec 8) 32}
    (h : mlkem768Incremental.encaps1 hdr rand = some (ct1, es, ss)) :
    ∃ ssL, mlkem768Encaps1With sampleNtt hdr rand.toList = some (ct1.toList, es.toList, ssL) := by
  unfold mlkem768Incremental at h; dsimp only at h
  rcases hw : mlkem768Encaps1With sampleNtt hdr rand.toList with _ | ⟨ct1L, esL, ssL⟩
  · simp [hw] at h
  · simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, _⟩
    have hge : 64 ≤ hdr.length := by
      by_contra hlt; simp [mlkem768Encaps1With, show hdr.length < 64 by omega] at hw
    have hw' := hw; rw [mlkem768Encaps1With_eq sampleNtt hdr rand.toList hge] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'; rcases hw' with ⟨hct_eq, hes_eq, _⟩
    have hc10 : ∀ p, (compressAndEncode 10 p).length = 320 := fun _ => by
      simp [compressAndEncode, byteEncode, bitsToBytes]
    have hct_len : ct1L.length = 960 := by rw [← hct_eq, show List.range 3 = [0, 1, 2] from rfl]; simp [hc10]
    have hes_len : esL.length = 2080 := by rw [← hes_eq]; exact encapsStateBytes_length _ _ (by simp)
    rw [toByteVec_eq_of_length hct_len, toByteVec_eq_of_length hes_len]
    exact ⟨ssL, rfl⟩

theorem esWellFormed_of_encaps1 {hdr : Bytes} {rand : List.Vector (BitVec 8) 32}
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (h : mlkem768Incremental.encaps1 hdr rand = some (ct1, es, ss)) : EsWellFormed es.toList := by
  obtain ⟨_, hw⟩ := encaps1_some_toList h; exact esWellFormed_of_encaps1With hw

/-! ## 3. Equivalence `mlkem768Encaps2List_eq_fips_of_esWellFormed` -/

private theorem byteDecodeRaw12_poly16_spec (bs : List (BitVec 8)) :
    PolyBounded16 4095 ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c) ∧
    PolyRepresents ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c) (byteDecodeMod 12 bs) := by
  have hsz_raw : (byteDecodeRaw 12 bs).size = 256 := by simp [byteDecodeRaw]
  have hsz : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).size = 256 := by simp [hsz_raw]
  refine ⟨⟨hsz, fun i hi => ?_⟩, ⟨hsz, fun i hi => ?_⟩⟩
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by omega) bs i hi
    have hmap : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by simp [Array.getD, hsz_raw, hi]
    rw [hmap, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by omega) bs i hi
    have hmap16 : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by simp [Array.getD, hsz_raw, hi]
    have hmapMod : (byteDecodeMod 12 bs).getD i 0 = (byteDecodeRaw 12 bs).getD i 0 % mlkemQ := by
      simp [byteDecodeMod, Array.getD, hsz_raw, hi]
    rw [hmap16, hmapMod, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    dsimp only [mlkemQ]; omega

private theorem polyAdd16_zero_left {p : Poly16} (hsz : p.size = 256) :
    polyAdd16 (Array.replicate 256 0#16) p = p := by
  unfold polyAdd16; apply Array.ext; · simp [hsz]
  · intro i _ _; simp [Array.getD, hsz]

private theorem encaps2_barrett_bounds (w : BitVec 16) :
    -3329 ≤ (neonBarrettReduce16 w).toInt ∧ (neonBarrettReduce16 w).toInt < 3329 := by
  have := neonBarrettReduce16_spec w
  omega

private theorem encaps2_lane_mod {x e m : BitVec 16} {xf ef mf : Nat}
    (hxb : -2496 ≤ x.toInt ∧ x.toInt ≤ 2496) (hxr : x.toInt % 3329 = (xf : Int) % 3329)
    (heb : -2 ≤ e.toInt ∧ e.toInt ≤ 2) (her : e.toInt % 3329 = (ef : Int) % 3329)
    (hmb : -3328 ≤ m.toInt ∧ m.toInt ≤ 3328) (hmr : m.toInt % 3329 = (mf : Int) % 3329) :
    (neonBarrettReduce16 (x + (e + m))).toInt % 3329 =
      ((((xf + ef) % mlkemQ + mf) % mlkemQ : Nat) : Int) % 3329 := by
  have hsum1 : (e + m).toInt = e.toInt + m.toInt :=
    toInt_add_of_bounds (by omega) (by omega)
  have hsum2 : (x + (e + m)).toInt = x.toInt + (e.toInt + m.toInt) := by
    rw [toInt_add_of_bounds (by rw [hsum1]; omega) (by rw [hsum1]; omega), hsum1]
  rw [(neonBarrettReduce16_spec (x + (e + m))).2.2, hsum2, Int.add_emod, hxr,
    Int.add_emod e.toInt, her, hmr]
  dsimp only [mlkemQ]; omega

private theorem encaps2_v_compress_eq {dot16 err2_16 msg16 : Poly16} {dotF err2F msgF : Poly}
    (hdot_b : PolyBounded16 6528 dot16) (hdot_r : PolyRepresentsMontInv dot16 dotF)
    (hdot_can : PolyCanonical dotF)
    (herr_b : PolyBounded16 2 err2_16) (herr_r : PolyRepresents err2_16 err2F)
    (hmsg_b : PolyBounded16 3328 msg16) (hmsg_r : PolyRepresents msg16 msgF) :
    neonCompressSerialize4
      (Array.ofFn (n := 256) fun ⟨i, _⟩ =>
        neonBarrettReduce16
          (neonMontgomeryMul16 ((neonInvNttMontgomery16 dot16).getD i 0#16) 1441#16 +
            (err2_16.getD i 0#16 + msg16.getD i 0#16))) =
      compressAndEncode 4 (polyAdd (polyAdd (polyInvNtt dotF) err2F) msgF) := by
  obtain ⟨_, hnorm_b, hnorm_r⟩ :=
    neonPolyInvNttFromMontInv16_spec (polyBounded16_mono (by omega) hdot_b) hdot_r hdot_can
  have hinv_sz : (neonInvNttMontgomery16 dot16).size = 256 := by
    simpa [neonPolyInvNttFromMontInv16] using hnorm_b.1
  apply neonCompressSerialize4_eq_compressAndEncode _ _ (polyAdd_canonical _ _).1
  · intro i hi
    rw [getD_ofFn _ _ _ hi]; dsimp only
    exact encaps2_barrett_bounds _
  · refine ⟨by simp, fun i hi => ?_⟩
    rw [getD_ofFn _ _ _ hi, polyAdd_getD _ _ hi, polyAdd_getD _ _ hi]; dsimp only
    have hnorm_get : (neonPolyInvNttFromMontInv16 dot16).getD i 0#16 =
        neonMontgomeryMul16 ((neonInvNttMontgomery16 dot16).getD i 0#16) 1441#16 := by
      simp [neonPolyInvNttFromMontInv16, Array.getD, hinv_sz, hi]
    have hnb := hnorm_b.2 i hi; rw [hnorm_get] at hnb
    have hnr := hnorm_r.2 i hi; rw [hnorm_get] at hnr
    exact encaps2_lane_mod hnb hnr (herr_b.2 i hi) (herr_r.2 i hi) (hmsg_b.2 i hi) (hmsg_r.2 i hi)

private theorem neonPolyNttMul16_size (lhs rhs : Poly16) :
    (neonPolyNttMul16 lhs rhs).size = 256 := by simp [neonPolyNttMul16]

private theorem fold3_polyAdd16 (f g : Fin 3 → Poly16) :
    (List.range 3).foldl
      (fun acc j =>
        let prod := neonPolyNttMul16 ((Array.ofFn f).getD j #[]) ((Array.ofFn g).getD j #[])
        Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + prod.getD i 0#16)
      (Array.replicate 256 0#16) =
    polyAdd16 (polyAdd16
      (neonPolyNttMul16 (f ⟨0, by omega⟩) (g ⟨0, by omega⟩))
      (neonPolyNttMul16 (f ⟨1, by omega⟩) (g ⟨1, by omega⟩)))
      (neonPolyNttMul16 (f ⟨2, by omega⟩) (g ⟨2, by omega⟩)) := by
  have hrange : List.range 3 = [0, 1, 2] := rfl
  rw [hrange, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    getD_ofFn _ 0 _ (by omega), getD_ofFn _ 1 _ (by omega), getD_ofFn _ 2 _ (by omega),
    getD_ofFn _ 0 _ (by omega), getD_ofFn _ 1 _ (by omega), getD_ofFn _ 2 _ (by omega)]
  have hstep (acc p : Poly16) :
      (Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + p.getD i 0#16) = polyAdd16 acc p := rfl
  dsimp only
  rw [hstep, hstep, hstep, polyAdd16_zero_left (neonPolyNttMul16_size _ _)]

theorem mlkem768Encaps2List_eq_fips_of_esWellFormed {es : List (BitVec 8)}
    (hes : EsWellFormed es) (ek : List (BitVec 8)) :
    mlkem768Encaps2List es ek = mlkem768Encaps2Fips es ek := by
  unfold mlkem768Encaps2List mlkem768Encaps2Fips; dsimp only
  have ht0 := byteDecodeRaw12_poly16_spec ((ek.drop (384 * 0)).take 384)
  have ht1 := byteDecodeRaw12_poly16_spec ((ek.drop (384 * 1)).take 384)
  have ht2 := byteDecodeRaw12_poly16_spec ((ek.drop (384 * 2)).take 384)
  have hr0 := hes.1 0 (by omega); have hr1 := hes.1 1 (by omega); have hr2 := hes.1 2 (by omega)
  let tHatF : Array Poly := Array.ofFn (n := 3) fun ⟨j, _⟩ => byteDecodeMod 12 ((ek.drop (384 * j)).take 384)
  let rHatF : Array Poly := Array.ofFn (n := 3) fun ⟨j, _⟩ =>
    poly16ToModQ (bytesToPoly16 ((es.drop (512 * j)).take 512))
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt3_spec (fa := tHatF) (fb := rHatF)
    ht0.1 ht1.1 ht2.1
    (polyBounded16_mono (by omega) hr0) (polyBounded16_mono (by omega) hr1)
    (polyBounded16_mono (by omega) hr2)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact ht0.2)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact ht1.2)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact ht2.2)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact poly16ToModQ_represents hr0.1)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact poly16ToModQ_represents hr1.1)
    (by rw [getD_ofFn _ _ _ (by omega)]; exact poly16ToModQ_represents hr2.1)
  have hfold := fold3_polyAdd16
    (fun ⟨i, _⟩ => (byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)).map fun c => BitVec.ofNat 16 c)
    (fun ⟨i, _⟩ => bytesToPoly16 ((es.drop (512 * i)).take 512))
  dsimp only at hfold
  obtain ⟨hmsg_b, hmsg_r⟩ := decodeAndDecompress_poly16_spec ((es.drop 2048).take 32) (Or.inl rfl)
    (fun i hi => byteDecodeRaw_lt_two_pow 1 (by omega) _ i hi)
  rw [hfold]
  exact encaps2_v_compress_eq hdot_b hdot_r (vecDotNtt_canonical 3 tHatF rHatF)
    hes.2 (poly16ToModQ_represents hes.2.1) hmsg_b hmsg_r

/-! ## 4. `mlkem768Incremental.encaps2` & `indCpaEncryptWith` Roundtrip Corollaries -/

theorem mlkem768Incremental_encaps2_eq_fips_of_esWellFormed {es : List.Vector (BitVec 8) 2080}
    (hes : EsWellFormed es.toList) (ek : List.Vector (BitVec 8) 1152) :
    mlkem768Incremental.encaps2 es ek = toByteVec 128 (mlkem768Encaps2Fips es.toList ek.toList) := by
  simp only [mlkem768Incremental, mlkem768Encaps2List_eq_fips_of_esWellFormed hes]

theorem mlkem768Incremental_encaps2_of_encaps1 {hdr : Bytes} {rand : List.Vector (BitVec 8) 32}
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (h1 : mlkem768Incremental.encaps1 hdr rand = some (ct1, es, ss)) (ek : List.Vector (BitVec 8) 1152) :
    mlkem768Incremental.encaps2 es ek = toByteVec 128 (mlkem768Encaps2Fips es.toList ek.toList) :=
  mlkem768Incremental_encaps2_eq_fips_of_esWellFormed (esWellFormed_of_encaps1 h1) ek

theorem mlkem768Encaps2Fips_encapsStateBytes {rHat : Array Poly} {e2 : Poly}
    (m ek : List (BitVec 8)) (hr_sz : rHat.size = 3)
    (hr_can : ∀ j < 3, PolyCanonical (rHat.getD j zeroPoly)) (he2_can : PolyCanonical e2) :
    mlkem768Encaps2Fips (encapsStateBytes rHat e2 m) ek =
      compressAndEncode 4
        (polyAdd (polyAdd (polyInvNtt (vecDotNtt 3
          (Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 ((ek.drop (384 * i)).take 384))
          rHat)) e2) (decodeAndDecompress 1 (m.take 32))) := by
  unfold mlkem768Encaps2Fips; dsimp only
  have hrHat_eq :
      (Array.ofFn (n := 3) fun ⟨i, _⟩ =>
        poly16ToModQ (bytesToPoly16 (((encapsStateBytes rHat e2 m).drop (512 * i)).take 512))) = rHat := by
    apply Array.ext
    · simp [hr_sz]
    · intro j hj1 hj2; have hj : j < 3 := by simpa using hj1
      simp only [Array.getElem_ofFn, encapsStateBytes_rHat_slice rHat e2 m j hj,
        poly16ToModQ_bytesToPoly16_centered (hr_can j hj)]
      simp [Array.getD, hj2]
  have he2_eq :
      poly16ToModQ (bytesToPoly16 (((encapsStateBytes rHat e2 m).drop 1536).take 512)) = e2 := by
    rw [encapsStateBytes_e2_slice rHat e2 m, poly16ToModQ_bytesToPoly16_centered he2_can]
  have hm_drop : (encapsStateBytes rHat e2 m).drop 2048 = m := by
    rw [encapsStateBytes_eq_append]
    let pfx := polyToCenteredI16Bytes (rHat.getD 0 zeroPoly) ++
      polyToCenteredI16Bytes (rHat.getD 1 zeroPoly) ++
      polyToCenteredI16Bytes (rHat.getD 2 zeroPoly) ++ polyToCenteredI16Bytes e2
    have hpfx : pfx.length = 2048 := by simp [pfx, polyToCenteredI16Bytes_length]
    change (pfx ++ m).drop 2048 = m; rw [← hpfx, List.drop_left]
  rw [hrHat_eq, he2_eq, hm_drop]

theorem mlkem768Encaps1With_encaps2Fips_eq_indCpaEncryptWith
    {sampler : List (BitVec 8) → Poly} {hdr rand32 ct1 es ss ek : List (BitVec 8)}
    (h1 : mlkem768Encaps1With sampler hdr rand32 = some (ct1, es, ss)) (hek : ek.length = 1152) :
    let m := rand32.take 32
    let hashed := sha3_512List (m ++ (hdr.drop 32).take 32)
    let coins := (hashed.drop 32).take 32
    let enc := indCpaEncryptWith sampler 3 10 4 (ek ++ hdr.take 32) m coins
    ct1 = enc.1 ∧ mlkem768Encaps2Fips es ek = enc.2.1 ∧ ss = hashed.take 32 := by
  dsimp only
  have hge : 64 ≤ hdr.length := by
    by_contra hlt; simp [mlkem768Encaps1With, show hdr.length < 64 by omega] at h1
  rw [mlkem768Encaps1With_eq sampler hdr rand32 hge] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1; rcases h1 with ⟨rfl, rfl, rfl⟩
  generalize sha3_512List (rand32.take 32 ++ (hdr.drop 32).take 32) = hashed
  let m := rand32.take 32
  let coins := (hashed.drop 32).take 32
  let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
  have hr_can : ∀ j < 3, PolyCanonical (rHat.getD j zeroPoly) := fun j hj => by
    have hj' : j < rHat.size := by simp [rHat, sampleVecCbd2, hj]
    rw [show rHat.getD j zeroPoly = rHat[j] by simp [Array.getD, hj']]
    simp only [rHat, Array.getElem_map, sampleVecCbd2, Array.getElem_ofFn]
    exact polyNtt_canonical (samplePolyCbd2_canonical _)
  have hfips := mlkem768Encaps2Fips_encapsStateBytes (rHat := rHat)
    (e2 := samplePolyCbd2 (shake256List 128 (coins ++ [6#8]))) m ek
    (by simp [rHat, sampleVecCbd2]) hr_can (samplePolyCbd2_canonical _)
  have hpk_tHat :
      (Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 (((ek ++ hdr.take 32).drop (384 * i)).take 384)) =
      (Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 ((ek.drop (384 * i)).take 384)) := by
    apply Array.ext
    · simp
    · intro i hi1 _; have hi : i < 3 := by simpa using hi1
      simp only [Array.getElem_ofFn]
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp [hek]; omega)]
  have hpk_rho : ((ek ++ hdr.take 32).drop (384 * 3)).take 32 = hdr.take 32 := by
    rw [show 384 * 3 = ek.length by omega, List.drop_left, List.take_take]; simp
  unfold indCpaEncryptWith; dsimp only
  rw [hpk_tHat, hpk_rho, show coins.take 32 = coins by simp [coins]]
  exact ⟨rfl, hfips, rfl⟩

theorem mlkem768Incremental_encaps_eq_indCpaEncryptWith {hdr : Bytes}
    {rand : List.Vector (BitVec 8) 32} {ct1 : List.Vector (BitVec 8) 960}
    {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (ek : List.Vector (BitVec 8) 1152)
    (h1 : mlkem768Incremental.encaps1 hdr rand = some (ct1, es, ss)) :
    let m := rand.toList.take 32
    let coins := ((sha3_512List (m ++ (hdr.drop 32).take 32)).drop 32).take 32
    let enc := indCpaEncryptWith sampleNtt 3 10 4 (ek.toList ++ hdr.take 32) m coins
    (ct1.toList, mlkem768Encaps2Fips es.toList ek.toList) = (enc.1, enc.2.1) ∧
    (ct1.toList, (mlkem768Incremental.encaps2 es ek).toList) = (enc.1, enc.2.1) := by
  dsimp only
  obtain ⟨_, hw⟩ := encaps1_some_toList h1
  obtain ⟨hc1, hc2, _⟩ := mlkem768Encaps1With_encaps2Fips_eq_indCpaEncryptWith hw ek.2
  have henc2 : (mlkem768Incremental.encaps2 es ek).toList = mlkem768Encaps2Fips es.toList ek.toList := by
    rw [mlkem768Incremental_encaps2_of_encaps1 h1 ek, toByteVec_eq_of_length (mlkem768Encaps2Fips_length _ _)]
  exact ⟨Prod.ext hc1 hc2, Prod.ext hc1 (henc2.trans hc2)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemEncaps2Fips
