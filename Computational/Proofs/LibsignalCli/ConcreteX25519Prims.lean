/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.LibsignalCli.StatementPqElfAnyKem
public import Computational.Proofs.LibsignalCli.StatementPqSecure -- proof-setup: allow-public-import
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.LibsignalCli.ConcreteX25519Group
import Computational.Proofs.LibsignalCli.ConcreteX25519Pow8
import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
import Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete Curve25519/XEdDSA Primitive Discharges & Abstract-to-Concrete Bridge (`ConcreteX25519Prims`)

**Checked by Lean.** Discharges all non-`kemKeyGen` fields of
`SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims (realUnreachedPrims kemKeyGen) realPEParams)`
(including `XeddsaCurveWitness` / `sig_corr` for `realXeddsaSign`, `realIsValidDhTriple`,
`realScalarMul`/`realScalarAdd`, AES-256 round-trip, and all `realPow8`/X25519 laws), and proves
the abstract-to-concrete bridge theorems `cliPqxdhSecurityForAnyKem_of_abstract` and
`cliPqxdhElfSecureAnyKem_of_abstract`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.LibsignalCli.ConcreteX25519Prims

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open Arm64.Process (ElfImage)
open CryptoGames.RFC7748 (X25519Pt x25519Dh x25519EncPt x25519EncT x25519DecT x25519Delta)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives ModelPrimsCryptoAssumptions
  CliPqxdhSecurityForAnyKem CliPqxdhSecurityForAbstract CliPqxdhAbstractBody
  modelPrims blockLevelPrims realPow8 realScalarMul realScalarAdd realUnreachedPrimsBase
  realXeddsaSign realIsValidDhTriple realUnreachedPrims
  toU8 ofU8 ofU8_toU8 toU8_length u8Vec vecU8 fitVec
  u8Vec_clampScalar25519
  modelPrims_sigVerify_eq_ref cryptoWellFormedPrimitivesδ_modelPrims)
open CryptoVerification.LibsignalCli (CliPqxdhElfSecureAnyKem)
open CryptoVerification.SignalSession (CliElfAddrs CliRun Inputs CliReachesSampleNttStuckElf
  cliRunElf realPEParams realCrypto)
open VerifiedLibraries.Common (p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven
  leBytesToNat natToLeBytes EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul
  encodeEd decodeEdRfc clampScalar clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  clampScalar_ratchet_clampScalar x25519PubFromSecretRef_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Pubkey_eq_edNatSmul edToMontU_edNeg_of_onCurve)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edBasepoint edOnCurve_edNeg edOnCurve_edAdd
  edAdd_comm edAdd_assoc edAdd_edZero edZero_edAdd edAdd_edNeg_self edNeg_edZero edNeg_edNeg
  edNatSmul edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_add edNatSmul_mul
  edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edNatSmul_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_cons)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  edOrderL_prime)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU montToEdwards_edToMontU montToEdwards_eq_some_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  edOnCurve_eq_of_edToMontU_eq edNatSmul_gcd_eq_zero edNatSmul_two_eq_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  encodeEd_length decodeEdRfc_encodeEd)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip (aes256Dec_aes256Enc)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 natOfBytesLE bytesOfNatLE bytesOfNatLE_length natOfBytesLE_bytesOfNatLE
  getD_toNat_eq_div_mod encodeScalarBytes decodeScalarBytes encodeScalarBytes_length
  natOfBytesLE_encodeScalarBytes clearSignBit32 clampedScalarZMod clampedScalarZMod_ne_zero)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  xeddsaSignRef XeddsaCurveWitness XeddsaCurveLaws)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip (xeddsaSignRef_correct)
open Computational.Proofs.LibsignalCli.ConcreteX25519Group (
  montLiftEd_eq_x25519MontToEdwards montLiftEd_one_eq_x25519MontToEdwards
  x25519Dh_commutes x25519RealizesDh_realCrypto x25519DecT_x25519EncT
  x25519EncT_ne_dummyKey x25519Dh_zero x25519Dh_kerUniform x25519Dh_base_fiber_prob_le)
open Computational.Proofs.LibsignalCli.ConcreteX25519Pow8 (
  scalarIsInRange_eq_decide_lt_p25519 realPow8_len realPow8_idemp
  realX25519_zero_iff realX25519_canon_base realX25519_canon_x25519
  realX25519_pow8_congr realX25519_congr_of_base_eq realX25519_canon_pow8_inj
  realX25519_inj_pow8 realX25519_pow8_base_len realX25519_ec_coll_bound)

/-! ## 1. Numeric Facts & Basic Byte/Scalar Helpers -/

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide +kernel

private theorem edOrderL_eq_l25519 : edOrderL = l25519 := by
  unfold edOrderL l25519; decide +kernel

private theorem two_lt_l25519 : 2 < l25519 := by
  unfold l25519; decide +kernel

private theorem edBasepoint_ne_edZero : edBasepoint ≠ edZero := by
  unfold edBasepoint edZero; decide +kernel

attribute [local irreducible] fpAdd fpSub fpMul fpNeg fpInv recoverXEven edSmul
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards

private theorem natToLeBytes_len (k n : Nat) : (natToLeBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k _ => simp [natToLeBytes]

private theorem u8Vec_toList_of_length {bs : List UInt8} (h : bs.length = 32) :
    (u8Vec 32 bs).toList = ofU8 bs := by
  unfold u8Vec fitVec
  change ((ofU8 bs ++ List.replicate 32 0#8).take 32) = ofU8 bs
  have hlen : (ofU8 bs).length = 32 := by simp [ofU8, h]
  rw [List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.take_of_length_le (Nat.le_of_eq hlen)]

private theorem u8Vec_toList_eq_ofU8_fitBytesRef (n : Nat) (bs : List UInt8) :
    (u8Vec n bs).toList = ofU8 (SignalPqxdh.fitBytesRef n bs) := by
  unfold u8Vec fitVec SignalPqxdh.fitBytesRef
  change ((ofU8 bs ++ List.replicate n 0#8).take n) =
    ofU8 (bs.take n ++ List.replicate (n - bs.length) 0)
  simp only [ofU8, List.map_append, List.map_take, List.map_replicate]
  rw [List.take_append, List.length_map, List.take_replicate]
  have hmin : min (n - bs.length) n = n - bs.length := Nat.min_eq_left (Nat.sub_le n bs.length)
  rw [hmin]
  rfl

private theorem leBytesToNat_ofU8 (bs : List UInt8) :
    leBytesToNat (ofU8 bs) = natOfBytesLE bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    change leBytesToNat (b.toBitVec :: ofU8 tl) = b.toNat + 256 * natOfBytesLE tl
    rw [leBytesToNat_cons, ih]
    have hb : b.toBitVec.toNat = b.toNat := rfl
    omega

private theorem natToLeBytes_succ (k n : Nat) :
    natToLeBytes (k + 1) n = BitVec.ofNat 8 (n % 256) :: natToLeBytes k (n / 256) := by
  unfold natToLeBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.pow_zero, Nat.div_one, List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.pow_succ, Nat.mul_comm _ 256, Nat.div_div_eq_div_mul]

private theorem toU8_natToLeBytes (k n : Nat) :
    toU8 (natToLeBytes k n) = bytesOfNatLE k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [natToLeBytes_succ, bytesOfNatLE]
    have hcons : ∀ (x : BitVec 8) (xs : List (BitVec 8)),
        toU8 (x :: xs) = UInt8.ofBitVec x :: toU8 xs := fun _ _ => rfl
    rw [hcons, ih]
    rfl

private theorem list32_take31_append_getD31 {l : List UInt8} (hl : l.length = 32) :
    l.take 31 ++ [l.getD 31 0] = l := by
  refine List.ext_getElem (by simp [hl]) fun i hi1 hi2 => ?_
  have hi32 : i < 32 := by omega
  by_cases h31 : i < 31
  · rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_take]
  · have hi_eq : i = 31 := by omega
    subst hi_eq
    rw [List.getElem_append_right (by simp [hl])]
    simp only [List.length_take, hl, Nat.min_eq_left (by decide : 31 ≤ 32), Nat.sub_self,
      List.getElem_singleton]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    rfl

/-! ## 2. `realScalarAdd` / `realScalarMul` ZMod Bridge -/

theorem realScalarMul_len (a b : List UInt8) : (realScalarMul a b).length = 32 := by
  unfold realScalarMul
  rw [toU8_length, natToLeBytes_len]

theorem realScalarAdd_len (a b : List UInt8) : (realScalarAdd a b).length = 32 := by
  unfold realScalarAdd
  rw [toU8_length, natToLeBytes_len]

private theorem realScalarAdd_encodeScalarBytes (x y : ZMod l25519) :
    realScalarAdd (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x + y) := by
  unfold realScalarAdd
  rw [u8Vec_toList_of_length (encodeScalarBytes_length x),
      u8Vec_toList_of_length (encodeScalarBytes_length y),
      leBytesToNat_ofU8, leBytesToNat_ofU8,
      natOfBytesLE_encodeScalarBytes, natOfBytesLE_encodeScalarBytes,
      edOrderL_eq_l25519, toU8_natToLeBytes]
  unfold encodeScalarBytes
  rw [ZMod.val_add]

private theorem realScalarMul_encodeScalarBytes (x y : ZMod l25519) :
    realScalarMul (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x * y) := by
  unfold realScalarMul
  rw [u8Vec_toList_of_length (encodeScalarBytes_length x),
      u8Vec_toList_of_length (encodeScalarBytes_length y),
      leBytesToNat_ofU8, leBytesToNat_ofU8,
      natOfBytesLE_encodeScalarBytes, natOfBytesLE_encodeScalarBytes,
      edOrderL_eq_l25519, toU8_natToLeBytes]
  unfold encodeScalarBytes
  rw [ZMod.val_mul]

/-! ## 3. `XeddsaCurveWitness` & `sig_corr` for `realUnreachedPrims kemKeyGen` -/

private def representsEdReal (x : ZMod l25519) (pt : EdPoint) : Prop :=
  pt = edNatSmul x.val edBasepoint

private noncomputable def compressEdReal (x : ZMod l25519) : List UInt8 :=
  toU8 (encodeEd (edNatSmul x.val edBasepoint))

private noncomputable def edSignReal (x : ZMod l25519) : UInt8 :=
  UInt8.ofNat ((edNatSmul x.val edBasepoint).x % 2)

private theorem edNatSmul_mod_edOrderL {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (n : Nat) :
    edNatSmul n P = edNatSmul (n % edOrderL) P := by
  conv_lhs => rw [← Nat.mod_add_div n edOrderL]
  rw [edNatSmul_add (n % edOrderL) (edOrderL * (n / edOrderL)) hP,
      Nat.mul_comm edOrderL (n / edOrderL),
      edNatSmul_mul (n / edOrderL) edOrderL hP,
      hL, edNatSmul_edZero, edAdd_edZero (edOnCurve_edNatSmul _ hP)]

private theorem edNatSmul_zmod_mul {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a b : ZMod l25519) :
    edNatSmul (a * b).val P = edNatSmul a.val (edNatSmul b.val P) := by
  have hmod : (a.val * b.val) % l25519 = (a.val * b.val) % edOrderL :=
    congrArg ((a.val * b.val) % ·) edOrderL_eq_l25519.symm
  rw [ZMod.val_mul, hmod, ← edNatSmul_mod_edOrderL hP hL, edNatSmul_mul a.val b.val hP]

private theorem edNatSmul_zmod_neg {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a : ZMod l25519) :
    edNatSmul (-a).val P = edNeg (edNatSmul a.val P) := by
  have hsum : edAdd (edNatSmul a.val P) (edNatSmul (-a).val P) = edZero := by
    rw [← edNatSmul_add a.val (-a).val hP, edNatSmul_mod_edOrderL hP hL, edOrderL_eq_l25519]
    have hmod : (a.val + (-a).val) % l25519 = (a + (-a)).val := (ZMod.val_add a (-a)).symm
    rw [hmod, add_neg_cancel, ZMod.val_zero]; rfl
  have h1 := congrArg (edAdd (edNeg (edNatSmul a.val P))) hsum
  have haP := edOnCurve_edNatSmul a.val hP
  have hnaP := edOnCurve_edNatSmul (-a).val hP
  rw [← edAdd_assoc (edOnCurve_edNeg haP) haP hnaP,
      edAdd_comm (edNeg (edNatSmul a.val P)) (edNatSmul a.val P),
      edAdd_edNeg_self haP, edZero_edAdd hnaP, edAdd_edZero (edOnCurve_edNeg haP)] at h1
  exact h1

private theorem edNatSmul_ne_edZero_of_zmod_ne_zero {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a : ZMod l25519} (ha : a ≠ 0) :
    edNatSmul a.val P ≠ edZero := by
  intro h0
  have ha_pos : 0 < a.val := Nat.pos_of_ne_zero (fun hv => ha ((ZMod.val_eq_zero a).mp hv))
  have ha_lt : a.val < edOrderL := by rw [edOrderL_eq_l25519]; exact a.val_lt
  have hgcd : Nat.gcd a.val edOrderL = 1 := by
    have hprime : Nat.Prime edOrderL := Nat.prime_def.mpr edOrderL_prime
    have hndvd : ¬ (edOrderL ∣ a.val) := Nat.not_dvd_of_pos_of_lt ha_pos ha_lt
    exact (Nat.Prime.coprime_iff_not_dvd hprime).mpr hndvd |>.symm
  have h1 := edNatSmul_gcd_eq_zero hP h0 hL
  rw [hgcd, edNatSmul_one hP] at h1
  exact hne h1

private theorem edNatSmul_zmod_inj {P : EdPoint} (hP : edOnCurve P = true)
    (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero) {a b : ZMod l25519}
    (h : edNatSmul a.val P = edNatSmul b.val P) : a = b := by
  by_contra hab
  have hsub_ne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hsub0 : edNatSmul (a - b).val P = edZero := by
    have hval : (a - b).val = (a.val + (-b).val) % l25519 := by
      rw [sub_eq_add_neg, ZMod.val_add]
    have hmod : (a.val + (-b).val) % l25519 = (a.val + (-b).val) % edOrderL :=
      congrArg ((a.val + (-b).val) % ·) edOrderL_eq_l25519.symm
    rw [hval, hmod, ← edNatSmul_mod_edOrderL hP hL,
        edNatSmul_add a.val (-b).val hP, edNatSmul_zmod_neg hP hL b, h,
        edAdd_edNeg_self (edOnCurve_edNatSmul b.val hP)]
  exact edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL hsub_ne hsub0

private theorem ratchet_clampScalar_toList_eq_clampScalarBytes (v : List.Vector (BitVec 8) 32) :
    (CryptoGames.Ratchet.clampScalar v).toList = clampScalarBytes v.toList := by
  rcases v with ⟨bs, hbs⟩
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hbs; done)
  rfl

private theorem clampScalar_ratchet_u8Vec_mod_edOrderL (sk : List UInt8) :
    clampScalar (CryptoGames.Ratchet.clampScalar (u8Vec 32 sk)).toList % edOrderL =
      (clampedScalarZMod sk).val := by
  rw [clampScalar_ratchet_clampScalar]
  unfold clampScalar clampedScalarZMod
  have htake : List.take 32 (u8Vec 32 sk).toList = (u8Vec 32 sk).toList :=
    List.take_of_length_le (by simp)
  have hbytes : clampScalarBytes (u8Vec 32 sk).toList =
      ofU8 (SignalPqxdh.clampScalar25519 sk) := by
    rw [← u8Vec_toList_of_length (SignalPqxdh.clampScalar25519_length sk),
        u8Vec_clampScalar25519 sk]
    exact (ratchet_clampScalar_toList_eq_clampScalarBytes (u8Vec 32 sk)).symm
  rw [htake, hbytes, leBytesToNat_ofU8, edOrderL_eq_l25519]
  unfold decodeScalarBytes
  rw [ZMod.val_natCast]

private theorem modelPrims_realPE_x25519Base_eq (X : UnreachedPqxdhPrimitives) (sk : List UInt8) :
    (modelPrims X realPEParams).x25519Base sk =
      toU8 (natToLeBytes 32 (edToMontU (edNatSmul (clampedScalarZMod sk).val edBasepoint))) := by
  dsimp only [modelPrims, blockLevelPrims, realPEParams, realCrypto]
  unfold vecU8
  rw [x25519PubFromSecretRef_toList, x25519Pubkey_eq_edNatSmul,
      edNatSmul_mod_edOrderL edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint,
      clampScalar_ratchet_u8Vec_mod_edOrderL sk]

private theorem edSignReal_bool (x : ZMod l25519) : edSignReal x = 0 ∨ edSignReal x = 1 := by
  unfold edSignReal
  rcases Nat.mod_two_eq_zero_or_one (edNatSmul x.val edBasepoint).x with h0 | h1
  · rw [h0]; exact Or.inl rfl
  · rw [h1]; exact Or.inr rfl

private theorem two_ne_zero_zmod_l25519 : (2 : ZMod l25519) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [show (2 : ZMod l25519) = ((2 : ℕ) : ZMod l25519) from rfl,
      ZMod.val_natCast_of_lt two_lt_l25519, ZMod.val_zero] at hv
  omega

private theorem edNatSmul_zmod_x_ne_zero {x : ZMod l25519} (hx : x ≠ 0) :
    (edNatSmul x.val edBasepoint).x ≠ 0 := by
  intro hx0
  have h_on := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have h20 : edNatSmul 2 (edNatSmul x.val edBasepoint) = edZero :=
    (edNatSmul_two_eq_zero_iff h_on).mpr hx0
  have h2z : edNatSmul ((2 : ZMod l25519) * x).val edBasepoint = edZero := by
    have h2v : (2 : ZMod l25519).val = 2 := ZMod.val_natCast_of_lt two_lt_l25519
    rw [edNatSmul_zmod_mul edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint, h2v]
    exact h20
  have : Fact (Nat.Prime l25519) := ⟨by rw [← edOrderL_eq_l25519]; exact Nat.prime_def.mpr edOrderL_prime⟩
  exact edNatSmul_ne_edZero_of_zmod_ne_zero edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint (mul_ne_zero two_ne_zero_zmod_l25519 hx) h2z

private theorem edSignReal_neg (x : ZMod l25519) (hx : x ≠ 0) :
    edSignReal (-x) = 1 - edSignReal x := by
  unfold edSignReal
  rw [edNatSmul_zmod_neg edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint x]
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have hQx_lt : Q.x < p25519 := edOnCurve_x_lt hQ_on
  have hQx_ne : Q.x ≠ 0 := edNatSmul_zmod_x_ne_zero hx
  have hQx_mod : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQx_lt]; exact hQx_ne
  dsimp only [edNeg]
  rw [fpNeg_mod_two_of_ne_zero hQx_mod, Nat.mod_eq_of_lt hQx_lt]
  rcases Nat.mod_two_eq_zero_or_one Q.x with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

private theorem compressEdReal_eq_bytesOfNatLE (x : ZMod l25519) :
    let Q := edNatSmul x.val edBasepoint
    compressEdReal x = bytesOfNatLE 32 (Q.y + (Q.x % 2) * 2 ^ 255) := by
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  unfold compressEdReal encodeEd
  dsimp only []
  rw [Nat.mod_eq_of_lt (edOnCurve_x_lt hQ_on), Nat.mod_eq_of_lt (edOnCurve_y_lt hQ_on),
      toU8_natToLeBytes]

private theorem compressEdReal_signBit_and_clear (x : ZMod l25519) :
    ((compressEdReal x).getD 31 0 &&& 0x80) >>> 7 = edSignReal x ∧
      clearSignBit32 (compressEdReal x) = toU8 (natToLeBytes 32 (edNatSmul x.val edBasepoint).y) := by
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have hy_lt : Q.y < p25519 := edOnCurve_y_lt hQ_on
  have hy_255 : Q.y < 2 ^ 255 := lt_trans hy_lt p25519_lt_two_pow_255
  have h255 : 2 ^ 255 = 128 * 256 ^ 31 := by decide
  have hy_div_lt : Q.y / 256 ^ 31 < 128 := by omega
  set s := Q.x % 2
  have hs_lt : s < 2 := Nat.mod_lt Q.x (by decide)
  let n := Q.y + s * 2 ^ 255
  have hn_lt : n < 256 ^ 32 := by
    have h256 : 256 ^ 32 = 256 * 256 ^ 31 := by decide
    omega
  have hc_eq : compressEdReal x = bytesOfNatLE 32 n := compressEdReal_eq_bytesOfNatLE x
  have htake31 : (bytesOfNatLE 32 n).take 31 = (bytesOfNatLE 32 Q.y).take 31 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    have hi31 : i < 31 := by simp at hi1; exact hi1
    have h1 := getD_toNat_eq_div_mod (bytesOfNatLE 32 n) i
    have h2 := getD_toNat_eq_div_mod (bytesOfNatLE 32 Q.y) i
    rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt hn_lt] at h1
    rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega : Q.y < 256 ^ 32)] at h2
    have hpow_dvd : 256 ^ i * 256 ∣ 2 ^ 255 := by
      rw [h255]
      have heq : 31 = (i + 1) + (30 - i) := by omega
      rw [heq, Nat.pow_add, Nat.pow_succ]
      exact Nat.dvd_trans (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ 128)
    rcases hpow_dvd with ⟨m, hm⟩
    have hdiv_mod : (n / 256 ^ i) % 256 = (Q.y / 256 ^ i) % 256 := by
      dsimp only [n]
      have hrw : Q.y + s * 2 ^ 255 = Q.y + 256 ^ i * (256 * (s * m)) := by rw [hm]; ring
      rw [hrw, Nat.add_mul_div_left _ _ (by positivity : 0 < 256 ^ i), Nat.add_mul_mod_self_left]
    rw [List.getElem_take, List.getElem_take]
    apply UInt8.toNat_inj.mp
    have hg1 : ((bytesOfNatLE 32 n)[i]'(by simp; omega)).toNat = (n / 256 ^ i) % 256 := by
      rw [← h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
    have hg2 : ((bytesOfNatLE 32 Q.y)[i]'(by simp; omega)).toNat = (Q.y / 256 ^ i) % 256 := by
      rw [← h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
    exact hg1.trans (hdiv_mod.trans hg2.symm)
  have hb31_n : ((bytesOfNatLE 32 n).getD 31 0).toNat = Q.y / 256 ^ 31 + s * 128 := by
    rw [getD_toNat_eq_div_mod, natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt hn_lt]
    dsimp only [n]
    have hrw : Q.y + s * 2 ^ 255 = Q.y + 256 ^ 31 * (s * 128) := by rw [h255]; ring
    rw [hrw, Nat.add_mul_div_left _ _ (by decide : 0 < 256 ^ 31),
        Nat.mod_eq_of_lt (by omega : Q.y / 256 ^ 31 + s * 128 < 256)]
  have hb31_y : ((bytesOfNatLE 32 Q.y).getD 31 0).toNat = Q.y / 256 ^ 31 := by
    rw [getD_toNat_eq_div_mod, natOfBytesLE_bytesOfNatLE,
        Nat.mod_eq_of_lt (by omega : Q.y < 256 ^ 32),
        Nat.mod_eq_of_lt (by omega : Q.y / 256 ^ 31 < 256)]
  have hbit_and_clear :
      ∀ (lo : Fin 128) (sg : Fin 2),
        ((UInt8.ofNat (lo.val + sg.val * 128) &&& 0x80) >>> 7) = UInt8.ofNat sg.val ∧
        (UInt8.ofNat (lo.val + sg.val * 128) &&& 0x7F) = UInt8.ofNat lo.val := by
    decide
  have hui8 : UInt8.size = 256 := rfl
  have hb31_eq_ofNat : (bytesOfNatLE 32 n).getD 31 0 = UInt8.ofNat (Q.y / 256 ^ 31 + s * 128) := by
    apply UInt8.toNat_inj.mp
    rw [hb31_n, UInt8.toNat_ofNat_of_lt' (by omega : Q.y / 256 ^ 31 + s * 128 < UInt8.size)]
  have hy31_eq_ofNat : (bytesOfNatLE 32 Q.y).getD 31 0 = UInt8.ofNat (Q.y / 256 ^ 31) := by
    apply UInt8.toNat_inj.mp
    rw [hb31_y, UInt8.toNat_ofNat_of_lt' (by omega : Q.y / 256 ^ 31 < UInt8.size)]
  obtain ⟨hbit, hclr⟩ := hbit_and_clear ⟨Q.y / 256 ^ 31, hy_div_lt⟩ ⟨s, hs_lt⟩
  constructor
  · rw [hc_eq, hb31_eq_ofNat]; exact hbit
  · unfold clearSignBit32
    rw [hc_eq, htake31, hb31_eq_ofNat, hclr, ← hy31_eq_ofNat,
        list32_take31_append_getD31 (bytesOfNatLE_length 32 Q.y), toU8_natToLeBytes]

private theorem montToEdwards_edToMontU_even {A : EdPoint}
    (hA : edOnCurve A = true) (hne : A ≠ edZero) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (edToMontU A)) 0 =
      some (if A.x % 2 == 1 then edNeg A else A) := by
  rcases Nat.mod_two_eq_zero_or_one A.x with hx0 | hx1
  · have hb : (A.x % 2 == 1) = false := by rw [hx0]; rfl
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hm := montToEdwards_edToMontU hA hne
    rwa [hx0] at hm
  · have hb : (A.x % 2 == 1) = true := by rw [hx1]; rfl
    rw [hb]; simp only [↓reduceIte]
    have hneg_on : edOnCurve (edNeg A) = true := edOnCurve_edNeg hA
    have hneg_ne : edNeg A ≠ edZero := by
      intro h0; have h1 := congrArg edNeg h0
      rw [edNeg_edNeg hA, edNeg_edZero] at h1; exact hne h1
    have hx_lt : A.x < p25519 := edOnCurve_x_lt hA
    have hx_mod_ne : A.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hx_lt]; omega
    have hneg_even : (edNeg A).x % 2 = 0 := by
      dsimp only [edNeg]
      rw [fpNeg_mod_two_of_ne_zero hx_mod_ne, Nat.mod_eq_of_lt hx_lt, hx1]
    have hm := montToEdwards_edToMontU hneg_on hneg_ne
    rwa [edToMontU_edNeg_of_onCurve hA, hneg_even] at hm

private theorem montToEdwards_one_of_zero {bs : List (BitVec 8)} {P : EdPoint}
    (h0 : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 = some P) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 1 =
      some (edNeg P) := by
  rcases (montToEdwards_eq_some_iff bs 0 P).mp h0 with ⟨hne, xEven, hrec, rfl⟩
  exact (montToEdwards_eq_some_iff bs 1 _).mpr ⟨hne, xEven, hrec, by
    dsimp only [edNeg]
    congr 1
    exact Nat.mod_eq_of_lt (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field.fpMul_lt _ _)⟩

private theorem xeddsaReal_dsmb_represents (X : UnreachedPqxdhPrimitives)
    (h : ZMod l25519) {y : ZMod l25519} {pt : EdPoint} (s : ZMod l25519)
    (hpt : representsEdReal y pt) :
    representsEdReal (h * y + s)
      ((modelPrims X realPEParams).doubleScalarMulBasepoint
        (encodeScalarBytes h) pt (encodeScalarBytes s)) := by
  unfold representsEdReal at hpt ⊢
  dsimp only [modelPrims, blockLevelPrims]
  have hh_nat : leBytesToNat (u8Vec 32 (encodeScalarBytes h)).toList = h.val := by
    rw [u8Vec_toList_of_length (encodeScalarBytes_length h), leBytesToNat_ofU8,
        natOfBytesLE_encodeScalarBytes]
  have hs_nat : leBytesToNat (u8Vec 32 (encodeScalarBytes s)).toList = s.val := by
    rw [u8Vec_toList_of_length (encodeScalarBytes_length s), leBytesToNat_ofU8,
        natOfBytesLE_encodeScalarBytes]
  have hh_lt : h.val < 2 ^ 256 :=
    lt_trans h.val_lt (by rw [← edOrderL_eq_l25519]; exact edOrderL_lt_two_pow_256)
  have hs_lt : s.val < 2 ^ 256 :=
    lt_trans s.val_lt (by rw [← edOrderL_eq_l25519]; exact edOrderL_lt_two_pow_256)
  rw [hh_nat, hs_nat, hpt,
      edSmul_eq_edNatSmul hh_lt (edOnCurve_edNatSmul y.val edOnCurve_edBasepoint),
      edSmul_eq_edNatSmul hs_lt edOnCurve_edBasepoint,
      ← edNatSmul_zmod_mul edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint h y,
      ← edNatSmul_add (h * y).val s.val edOnCurve_edBasepoint,
      edNatSmul_mod_edOrderL edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint,
      edOrderL_eq_l25519, ← ZMod.val_add]

private theorem compressEdReal_inj : Function.Injective compressEdReal := by
  intro x1 x2 h
  have hbv : encodeEd (edNatSmul x1.val edBasepoint) =
      encodeEd (edNatSmul x2.val edBasepoint) := by
    unfold compressEdReal at h
    have h1 := congrArg ofU8 h
    rwa [ofU8_toU8, ofU8_toU8] at h1
  have hdec := congrArg decodeEdRfc hbv
  rw [decodeEdRfc_encodeEd (edOnCurve_edNatSmul x1.val edOnCurve_edBasepoint),
      decodeEdRfc_encodeEd (edOnCurve_edNatSmul x2.val edOnCurve_edBasepoint)] at hdec
  exact edNatSmul_zmod_inj edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint (Option.some.inj hdec)

private theorem compressEdReal_inRange (x : ZMod l25519) :
    SignalPqxdh.scalarIsInRange (clearSignBit32 (compressEdReal x)) = true := by
  rw [(compressEdReal_signBit_and_clear x).2]
  have hy_lt : (edNatSmul x.val edBasepoint).y < p25519 :=
    edOnCurve_y_lt (edOnCurve_edNatSmul x.val edOnCurve_edBasepoint)
  have hlen : (toU8 (natToLeBytes 32 (edNatSmul x.val edBasepoint).y)).length = 32 := by
    rw [toU8_length, natToLeBytes_len]
  rw [scalarIsInRange_eq_decide_lt_p25519 hlen, decide_eq_true_eq, ofU8_toU8,
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec.leBytesToNat_natToLeBytes_of_lt
        (lt_trans hy_lt (lt_trans p25519_lt_two_pow_255 (by decide)))]
  exact hy_lt

private theorem xeddsaReal_montToEd_base (X : UnreachedPqxdhPrimitives)
    (sk : List UInt8) (b : UInt8) (hb : b = 0 ∨ b = 1) :
    ∃ pt, (modelPrims X realPEParams).montToEd ((modelPrims X realPEParams).x25519Base sk) b = some pt ∧
      representsEdReal
        (if b == edSignReal (clampedScalarZMod sk) then clampedScalarZMod sk
         else -clampedScalarZMod sk) pt := by
  set a := clampedScalarZMod sk
  have ha_ne : a ≠ 0 := clampedScalarZMod_ne_zero sk
  set Q := edNatSmul a.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul a.val edOnCurve_edBasepoint
  have hQ_ne : Q ≠ edZero := edNatSmul_ne_edZero_of_zmod_ne_zero edOnCurve_edBasepoint
    edBasepoint_ne_edZero edNatSmul_edOrderL_edBasepoint ha_ne
  have hbase := modelPrims_realPE_x25519Base_eq X sk
  have hu8_list : (u8Vec 32 ((modelPrims X realPEParams).x25519Base sk)).toList =
      natToLeBytes 32 (edToMontU Q) := by
    rw [hbase, u8Vec_toList_of_length (by rw [toU8_length, natToLeBytes_len]), ofU8_toU8]
  have hlift0 : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (edToMontU Q)) 0 =
      some (if Q.x % 2 == 1 then edNeg Q else Q) :=
    montToEdwards_edToMontU_even hQ_on hQ_ne
  change ∃ pt : EdPoint,
    SignalPqxdh.montLiftEd (u8Vec 32 ((modelPrims X realPEParams).x25519Base sk)).toList b.toBitVec =
      some pt ∧ _
  rw [hu8_list]
  have hneg_rep : representsEdReal (-a) (edNeg Q) := by
    unfold representsEdReal
    exact (edNatSmul_zmod_neg edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint a).symm
  have hsign0 : Q.x % 2 = 0 → edSignReal a = 0 := fun hx0 => by
    unfold edSignReal; change UInt8.ofNat (Q.x % 2) = 0; rw [hx0]; rfl
  have hsign1 : Q.x % 2 = 1 → edSignReal a = 1 := fun hx1 => by
    unfold edSignReal; change UInt8.ofNat (Q.x % 2) = 1; rw [hx1]; rfl
  rcases hb with rfl | rfl
  · have hb0 : (0 : UInt8).toBitVec = 0#8 := rfl
    rw [hb0, montLiftEd_eq_x25519MontToEdwards, hlift0]
    refine ⟨if Q.x % 2 == 1 then edNeg Q else Q, rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one Q.x with hx0 | hx1
    · rw [hsign0 hx0, hx0]; rfl
    · rw [hsign1 hx1, hx1]; exact hneg_rep
  · have hb1 : (1 : UInt8).toBitVec = 1#8 := rfl
    rw [hb1, montLiftEd_one_eq_x25519MontToEdwards, montToEdwards_one_of_zero hlift0]
    refine ⟨edNeg (if Q.x % 2 == 1 then edNeg Q else Q), rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one Q.x with hx0 | hx1
    · rw [hsign0 hx0, hx0]; exact hneg_rep
    · rw [hsign1 hx1, hx1]
      simp only [beq_self_eq_true, ↓reduceIte, edNeg_edNeg hQ_on]
      rfl

private noncomputable def xeddsaCurveWitness_realUnreachedPrims
    (kemKeyGen : List UInt8 → List UInt8 × List UInt8) :
    XeddsaCurveWitness (modelPrims (realUnreachedPrims kemKeyGen) realPEParams) where
  x25519Base_len := fun sk => by
    rw [modelPrims_realPE_x25519Base_eq, toU8_length, natToLeBytes_len]
  scalarMod_eq := fun bs => by
    dsimp only [modelPrims, blockLevelPrims]
    rw [u8Vec_toList_eq_ofU8_fitBytesRef, leBytesToNat_ofU8, edOrderL_eq_l25519,
        toU8_natToLeBytes]
    unfold encodeScalarBytes decodeScalarBytes
    rw [ZMod.val_natCast]
  scalarWide_eq := fun w => by
    dsimp only [modelPrims, blockLevelPrims]
    rw [u8Vec_toList_eq_ofU8_fitBytesRef, leBytesToNat_ofU8, edOrderL_eq_l25519,
        toU8_natToLeBytes]
    unfold encodeScalarBytes decodeScalarBytes
    rw [ZMod.val_natCast]
  scalarAdd_eq := realScalarAdd_encodeScalarBytes
  scalarMul_eq := realScalarMul_encodeScalarBytes
  RepresentsEd := representsEdReal
  compressEd := compressEdReal
  edSign := edSignReal
  edNeg_represents := fun {x pt} hpt => by
    unfold representsEdReal at hpt ⊢
    dsimp only [modelPrims, blockLevelPrims]
    rw [hpt, ← edNatSmul_zmod_neg edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint x]
  dsmb_represents := xeddsaReal_dsmb_represents (realUnreachedPrims kemKeyGen)
  compress_of_represents := fun {_ _} hpt => by
    unfold representsEdReal at hpt; subst hpt; rfl
  compressEd_inj := compressEdReal_inj
  compressEd_len := fun x => by
    unfold compressEdReal; rw [toU8_length, encodeEd_length]
  compressEd_inRange := compressEdReal_inRange
  edSign_bool := edSignReal_bool
  edSign_neg := edSignReal_neg
  compressEd_signBit := fun x => (compressEdReal_signBit_and_clear x).1
  montToEd_base := xeddsaReal_montToEd_base (realUnreachedPrims kemKeyGen)
  x25519Base_eq_of_clamped_pm := fun u1 u2 hpm => by
    rw [modelPrims_realPE_x25519Base_eq, modelPrims_realPE_x25519Base_eq]
    rcases hpm with h | h
    · rw [h]
    · rw [h, edNatSmul_zmod_neg edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint,
          edToMontU_edNeg_of_onCurve (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)]

private theorem realXeddsaSign_eq_xeddsaSignRef (kemKeyGen : List UInt8 → List UInt8 × List UInt8) :
    realXeddsaSign = xeddsaSignRef (modelPrims (realUnreachedPrims kemKeyGen) realPEParams) :=
  rfl

/-- `realIsValidDhTriple` agrees with `SignalPqxdh.isValidDhTripleRef` on `modelPrims (realUnreachedPrims kemKeyGen) realPEParams`. -/
theorem realIsValidDhTriple_iff_ref (kemKeyGen : List UInt8 → List UInt8 × List UInt8)
    (A B Z : List UInt8) :
    realIsValidDhTriple A B Z = true ↔
      SignalPqxdh.isValidDhTripleRef (modelPrims (realUnreachedPrims kemKeyGen) realPEParams) A B Z := by
  unfold realIsValidDhTriple
  exact Iff.of_eq (@decide_eq_true_eq _ (Classical.propDecidable _))

theorem realXeddsaSign_correct (kemKeyGen : List UInt8 → List UInt8 × List UInt8)
    (sk msg r : List UInt8) :
    (modelPrims (realUnreachedPrims kemKeyGen) realPEParams).sigVerify
        ((realUnreachedPrims kemKeyGen).sigPkGen sk) msg (realXeddsaSign sk msg r) = true := by
  rw [modelPrims_sigVerify_eq_ref, realXeddsaSign_eq_xeddsaSignRef kemKeyGen]
  exact xeddsaSignRef_correct ⟨xeddsaCurveWitness_realUnreachedPrims kemKeyGen⟩ sk msg r

/-! ## 4. Full `CryptoWellFormedPrimitivesδ` Discharge & Abstract-to-Concrete Bridge -/

/-- Discharges all 55 non-`kemKeyGen` fields of `SignalPqxdh.CryptoWellFormedPrimitivesδ` at
`modelPrims (realUnreachedPrims kemKeyGen) realPEParams`, taking only the two Kyber-1024
`kemKeyGen` hypotheses (`_hKemValid` and `_hKemColl`). -/
theorem cryptoWellFormedPrimitivesδ_realUnreachedPrims
    (kemKeyGen : List UInt8 → List UInt8 × List UInt8)
    (hKemValid : ∀ seed, (kemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
      (kemKeyGen seed).2.length = 3168)
    (hKemColl : ∀ targetPk,
      𝒟[do let (pk, _) ← SignalPqxdh.sampleKemKeyGen (modelPrims (realUnreachedPrims kemKeyGen) realPEParams)
           pure (pk == targetPk)] {true} ≤ 1 / (2 : ℝ≥0∞) ^ 255) :
    SignalPqxdh.CryptoWellFormedPrimitivesδ
      (modelPrims (realUnreachedPrims kemKeyGen) realPEParams) := by
  have hAssump : ModelPrimsCryptoAssumptions (realUnreachedPrims kemKeyGen) realPEParams :=
    { x25519_zero_iff := realX25519_zero_iff _
      canon_base := realX25519_canon_base _
      canon_x25519 := realX25519_canon_x25519 _
      pow8_idemp := realPow8_idemp
      isValidDhTriple_eq_ref := realIsValidDhTriple_iff_ref kemKeyGen
      x25519_pow8_congr := realX25519_pow8_congr _
      x25519_congr_of_base_eq := realX25519_congr_of_base_eq _
      canon_pow8_inj := realX25519_canon_pow8_inj _
      pow8_len := realPow8_len
      ec_coll_bound := realX25519_ec_coll_bound _
      x25519_inj_pow8 := realX25519_inj_pow8 _
      pow8_base_len := realX25519_pow8_base_len _
      sigPkGen_eq_x25519Base := rfl
      scalarMul_len := realScalarMul_len
      scalarAdd_len := realScalarAdd_len
      kemKeyGen_len := hKemValid
      sig_corr := realXeddsaSign_correct kemKeyGen
      kem_coll_bound := fun targetPk => by
        have hne : (1 / (2 : ℝ≥0∞) ^ 255) ≠ ⊤ := by
          rw [one_div]; exact ENNReal.inv_ne_top.mpr (by positivity)
        have hr := ENNReal.toReal_mono hne (hKemColl targetPk)
        simpa [ENNReal.toReal_div, ENNReal.toReal_pow] using hr }
  exact cryptoWellFormedPrimitivesδ_modelPrims
    (realUnreachedPrims kemKeyGen) realPEParams hAssump
    x25519Dh_commutes x25519RealizesDh_realCrypto aes256Dec_aes256Enc

/-- Generic abstract-to-concrete bridge: instantiating `CliPqxdhSecurityForAbstract` at the concrete
Curve25519 subgroup `X25519Pt`, `realPEParams`, and `realUnreachedPrims kemKeyGen`, and discharging
all seven session group premises plus the 55 non-`kemKeyGen` primitive laws, yields the concrete
KEM-generic statement `CliPqxdhSecurityForAnyKem`. -/
theorem cliPqxdhSecurityForAnyKem_of_abstract
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRunsNew : (CliRun → (List UInt8 → List UInt8 × List UInt8) →
        Option (Inputs → Prop) → Prop) → Prop)
    (ForRunsOld : (CliRun → UnreachedPqxdhPrimitives → PEParams →
        Option (Inputs → Prop) → Prop) → Prop)
    (hRuns : ∀ B1 B2,
      (∀ run k exc?, B1 run (realUnreachedPrims k) realPEParams exc? → B2 run k exc?) →
      ForRunsOld B1 → ForRunsNew B2)
    (hOld : CliPqxdhSecurityForAbstract (Pt := X25519Pt) S ℓ ForRunsOld) :
    CliPqxdhSecurityForAnyKem S ℓ ForRunsNew := by
  rcases hOld with ⟨L_cli, RK, D, reds, hCostRK, hSimRK, hSlotD, ⟨hCostL, hCostReds⟩, hForOld⟩
  refine ⟨L_cli x25519DecT x25519EncT, RK, D,
    fun P qep => reds P realPEParams.C realPEParams.Q.K qep x25519DecT x25519EncT,
    hCostRK, hSimRK, hSlotD,
    ⟨fun b qStart qDR => hCostL x25519DecT x25519EncT b qStart qDR,
     fun P qep => hCostReds P realPEParams.C realPEParams.Q.K qep x25519DecT x25519EncT⟩,
    ?_⟩
  refine hRuns _ _ (fun run kemKeyGen exc? hB => ?_) hForOld
  intro X P hKemValid hKemColl δ_kem hKemBin qep hℓ b qStart qs hq32 A hA
  exact hB
    (cryptoWellFormedPrimitivesδ_realUnreachedPrims kemKeyGen hKemValid hKemColl)
    δ_kem hKemBin
    x25519Dh x25519EncPt x25519EncT x25519DecT qep hℓ
    x25519Dh_commutes x25519RealizesDh_realCrypto
    x25519DecT_x25519EncT x25519EncT_ne_dummyKey
    x25519Dh_zero x25519Dh_kerUniform
    b qStart qs hq32 x25519Delta x25519Dh_base_fiber_prob_le A hA

/-- ELF-direct specialization of `cliPqxdhSecurityForAnyKem_of_abstract`: the abstract-group ELF
security statement at `Pt := X25519Pt` implies the KEM-generic concrete X25519 statement
`CliPqxdhElfSecureAnyKem`. -/
theorem cliPqxdhElfSecureAnyKem_of_abstract
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) (addrs : CliElfAddrs)
    (hOld : CliPqxdhSecurityForAbstract (Pt := X25519Pt) S ℓ fun Bound =>
      ∀ (X : UnreachedPqxdhPrimitives),
        Bound (cliRunElf elf addrs) X realPEParams
          (some (CliReachesSampleNttStuckElf elf addrs))) :
    CliPqxdhElfSecureAnyKem S ℓ elf addrs :=
  cliPqxdhSecurityForAnyKem_of_abstract S ℓ _ _
    (fun _ _ hImp hOldRun kemKeyGen => hImp _ kemKeyGen _ (hOldRun (realUnreachedPrims kemKeyGen)))
    hOld

end Computational.Proofs.LibsignalCli.ConcreteX25519Prims
