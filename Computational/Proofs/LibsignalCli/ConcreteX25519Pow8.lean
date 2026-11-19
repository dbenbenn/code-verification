/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.LibsignalCli.ConcreteX25519Group
import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Concrete X25519 Subgroup Projection (`realPow8`) & Canonical-Key Proofs (`ConcreteX25519Pow8`)

**Checked by Lean.** Discharges all Curve25519 `realPow8`, `isCanonical`, `x25519`, and base-point
collision fields of `ModelPrimsSharedAssumptions (realUnreachedPrims kemKeyGen) realPEParams`
directly against `realPEParams` and `realPow8` (`StatementPqElf.lean`), for arbitrary `kemKeyGen`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.LibsignalCli.ConcreteX25519Pow8

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (vec32)
open CryptoGames.RFC7748 (X25519Pt x25519Dh x25519BasePt x25519EncPt x25519EncT x25519Delta
  x25519 x25519Basepoint x25519Pubkey x25519Ref x25519PubFromSecretRef x25519Ladder decodeU255)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives modelPrims blockLevelPrims
  realPow8 realUnreachedPrims toU8 ofU8 toU8_ofU8 ofU8_toU8 toU8_length ofU8_length
  u8Vec vecU8 fitVec ofU8_word256ToBytes length_word256ToBytes u8Vec_clampScalar25519
  pubKey_clampScalar_toList_of_libX25519Rel)
open CryptoVerification.SignalSession (realPEParams)
open VerifiedLibraries.Common (p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven
  leBytesToNat natToLeBytes EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul
  clampScalar clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (isCanonicalX25519 lowOrderUs
  clampScalar_ratchet_clampScalar x25519Ref_toList x25519PubFromSecretRef_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Ladder_mod x25519Ladder_zero x25519Ladder_edToMontU x25519Ladder_twToMontU
  clampScalar_eight_mul clampScalar_lt_two_pow_255 x25519Pubkey_eq_edNatSmul
  x25519_eq_zero_iff_lowOrder x25519Pubkey_not_lowOrder isCanonicalX25519_x25519
  x25519_uCoord_congr edToMontU_edNeg_of_onCurve)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpMul_lt fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg
  edOnCurve_edAdd edAdd_comm edAdd_assoc edAdd_edZero edZero_edAdd edAdd_edNeg_self
  edNeg_edZero edNeg_edNeg edNatSmul edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one
  edNatSmul_add edNatSmul_mul edNatSmul_edAdd edSmul_eq_edNatSmul edOrderL_lt_two_pow_256
  edNatSmul_edOrderL_edBasepoint edNatSmul_mod_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_cons leBytesToNat_natToLeBytes_of_lt)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  twistOrderL edOrderL_odd twistOrderL_odd two_pow_252_lt_edOrderL two_pow_252_lt_twistOrderL
  edOrderL_prime twistOrderL_prime gcd_sixteen_mul_odd_prime)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  montRHS edToMontU edToMontU_lt edToMontU_edNeg edToMontU_edBasepoint
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero montToEdwards_some_edToMontU
  montToEdwards_edToMontU montToEdwards_eq_none_iff_raw montToEdwards_eq_some_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  FpIsSquare edToMontU_eq_zero_iff edOnCurve_montRHS_isSquare
  twZero twOnCurve twAdd twNeg twNatSmul twToMontU twToMontU_lt
  twOnCurve_x_lt twOnCurve_twNeg twOnCurve_twAdd twAdd_comm twAdd_assoc
  twAdd_twZero twZero_twAdd twAdd_twNeg_self twOnCurve_twNatSmul twNatSmul_twZero
  twNatSmul_add twNatSmul_mul twToMontU_eq_zero_iff twOnCurve_montRHS_not_isSquare
  mont_lift_dichotomy)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  twToMontU_twNeg edOnCurve_eq_of_edToMontU_eq edNatSmul_gcd_eq_zero edNatSmul_two_eq_zero_iff
  edNatSmul_eight_mul_edOrderL twOnCurve_eq_of_twToMontU_eq twNatSmul_gcd_eq_zero
  twNatSmul_two_eq_zero_iff twNatSmul_four_mul_twistOrderL)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 two_pow_252_lt_l25519 natOfBytesLE bytesOfNatLE bytesOfNatLE_length
  natOfBytesLE_bytesOfNatLE bytesOfNatLE_natOfBytesLE getD_toNat_eq_div_mod
  clampedScalarZMod clampedScalarZMod_ne_zero)
open Computational.Proofs.LibsignalCli.ConcreteX25519Group (
  montLiftEd_eq_x25519MontToEdwards isCanonicalX25519_basepoint
  x25519RealizesDh_realCrypto x25519Dh_base_fiber_card x25519Dh_dh_val x25519BasePt_val)

/-! ## 1. Numeric Constants & Irreducibility Guards -/

private def eEd : Nat := 3 * edOrderL + 1
private def eTw : Nat := 3 * twistOrderL + 1
private def qEd : Nat := ((3 * edOrderL + 1) / 8) * 3
private def qTw : Nat := ((3 * twistOrderL + 1) / 4) * 3

private theorem twistOrderL_spec_eq : CryptoGames.RFC7748.twistOrderL = twistOrderL := by
  unfold CryptoGames.RFC7748.twistOrderL twistOrderL; decide +kernel

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide +kernel

private theorem p25519_lt_256_pow_32 : p25519 < 256 ^ 32 := by
  unfold p25519; decide +kernel

private theorem edOrderL_eq_l25519 : edOrderL = l25519 := by
  unfold edOrderL l25519; decide +kernel

private theorem eight_lt_edOrderL : 8 < edOrderL := by
  unfold edOrderL; decide +kernel

private theorem eight_lt_twistOrderL : 8 < twistOrderL := by
  unfold twistOrderL; decide +kernel

private theorem eEd_lt_two_pow_255 : eEd < 2 ^ 255 := by
  unfold eEd edOrderL; decide +kernel

private theorem eTw_lt_two_pow_255 : eTw < 2 ^ 255 := by
  unfold eTw twistOrderL; decide +kernel

private theorem eEd_div_eight : eEd = 8 * ((3 * edOrderL + 1) / 8) := by
  unfold eEd edOrderL; decide +kernel

private theorem eTw_div_four : eTw = 4 * ((3 * twistOrderL + 1) / 4) := by
  unfold eTw twistOrderL; decide +kernel

private theorem eEd_sq_eq : eEd * eEd = qEd * (8 * edOrderL) + eEd := by
  unfold eEd qEd edOrderL; decide +kernel

private theorem eTw_sq_eq : eTw * eTw = qTw * (4 * twistOrderL) + eTw := by
  unfold eTw qTw twistOrderL; decide +kernel

private theorem edBasepoint_ne_edZero : edBasepoint ≠ edZero := by
  unfold edBasepoint edZero; decide +kernel

private theorem p25519_decomp :
    p25519 = 0xED + 256 * (256 ^ 30 - 1) + 256 ^ 31 * 0x7F := by
  unfold p25519; decide +kernel

private theorem x25519Ladder_lt_p25519 (k u : Nat) : x25519Ladder k u < p25519 :=
  fpMul_lt _ _

attribute [local irreducible] fpAdd fpSub fpMul fpNeg fpInv recoverXEven edSmul x25519Ladder
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards

/-! ## 2. Basic Byte / Scalar / Curve Helpers -/

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

private theorem decodeU255_natToLeBytes_of_lt_p {u : Nat} (hu : u < p25519) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
      (natToLeBytes 32 u) = u := by
  unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
  rw [List.take_of_length_le (by rw [natToLeBytes_len]),
      leBytesToNat_natToLeBytes_of_lt (lt_trans hu p25519_lt_256_pow_32),
      Nat.mod_eq_of_lt (lt_trans hu p25519_lt_two_pow_255)]

private theorem natOfBytesLE_replicate_ff :
    ∀ n : Nat, natOfBytesLE (List.replicate n (0xFF : UInt8)) = 256 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ]
    change (0xFF : UInt8).toNat + 256 * natOfBytesLE (List.replicate n (0xFF : UInt8)) =
      256 ^ (n + 1) - 1
    rw [natOfBytesLE_replicate_ff n]
    have hpos : 1 ≤ 256 ^ n := Nat.one_le_pow n 256 (by decide)
    have hff : (0xFF : UInt8).toNat = 255 := rfl
    rw [hff, Nat.pow_succ]
    omega

private theorem natOfBytesLE_append (l1 l2 : List UInt8) :
    natOfBytesLE (l1 ++ l2) = natOfBytesLE l1 + 256 ^ l1.length * natOfBytesLE l2 := by
  induction l1 with
  | nil => simp [natOfBytesLE]
  | cons b tl ih =>
    simp only [List.cons_append, List.length_cons, natOfBytesLE, ih, Nat.pow_succ]
    ring

private theorem natOfBytesLE_lt_pow (bs : List UInt8) : natOfBytesLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [natOfBytesLE]
  | cons b tl ih =>
    simp only [natOfBytesLE, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := b.toBitVec.isLt
    omega

/-- Direct characterization of `SignalPqxdh.scalarIsInRange` on 32-byte lists. -/
theorem scalarIsInRange_eq_decide_lt_p25519 {pk : List UInt8} (hlen : pk.length = 32) :
    SignalPqxdh.scalarIsInRange pk = decide (leBytesToNat (ofU8 pk) < p25519) := by
  rw [leBytesToNat_ofU8]
  set b0 : UInt8 := pk.getD 0 0
  set mid : List UInt8 := (pk.drop 1).take 30
  set b31 : UInt8 := pk.getD 31 0
  have hmid_len : mid.length = 30 := by simp [mid, hlen]
  have hpk_split : pk = [b0] ++ mid ++ [b31] := by
    refine List.ext_getElem (by simp [hmid_len, hlen]) fun i hi1 hi2 => ?_
    have hi32 : i < 32 := by omega
    by_cases h0 : i = 0
    · subst h0
      simp only [List.cons_append, List.nil_append, List.getElem_cons_zero]
      rw [show b0 = pk.getD 0 0 from rfl, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]; rfl
    · by_cases h31 : i = 31
      · subst h31
        simp only [List.cons_append, List.nil_append]
        have hlen_m : (mid ++ [b31])[30]'(by simp [hmid_len]) = b31 := by
          rw [List.getElem_append_right (by omega)]
          simp [hmid_len]
        change pk[31] = (mid ++ [b31])[30]'(by simp [hmid_len])
        rw [hlen_m]
        rw [show b31 = pk.getD 31 0 from rfl, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)]; rfl
      · simp only [List.cons_append, List.nil_append]
        have him : i - 1 < mid.length := by omega
        have hstep : ([b0] ++ (mid ++ [b31]))[i]'(by simp [hmid_len]; omega) =
            (mid ++ [b31])[i - 1]'(by simp [hmid_len]; omega) := by
          cases i with
          | zero => contradiction
          | succ j => rfl
        rw [List.getElem_append_left him] at hstep
        simp only [List.cons_append, List.nil_append] at hstep
        rw [hstep]
        simp only [mid, List.getElem_take, List.getElem_drop]
        congr 1; omega
  have hu : natOfBytesLE pk = b0.toNat + 256 * natOfBytesLE mid + 256 ^ 31 * b31.toNat := by
    conv_lhs => rw [hpk_split]
    rw [natOfBytesLE_append, natOfBytesLE_append]
    simp only [List.length_append, List.length_cons, List.length_nil, hmid_len]
    change (b0.toNat + 256 * 0 + 256 ^ 1 * natOfBytesLE mid) +
      256 ^ (1 + 30) * (b31.toNat + 256 * 0) = _
    ring
  have hb0_lt : b0.toNat < 256 := b0.toBitVec.isLt
  have hmid_lt : natOfBytesLE mid < 256 ^ 30 := by
    simpa [hmid_len] using natOfBytesLE_lt_pow mid
  have hb31_lt : b31.toNat < 256 := b31.toBitVec.isLt
  have hmid_eq : (mid == List.replicate 30 (0xFF : UInt8)) = true ↔
      natOfBytesLE mid = 256 ^ 30 - 1 := by
    rw [beq_iff_eq]
    constructor
    · intro h; rw [h]; exact natOfBytesLE_replicate_ff 30
    · intro hm
      have h1 := bytesOfNatLE_natOfBytesLE mid
      have h2 := bytesOfNatLE_natOfBytesLE (List.replicate 30 (0xFF : UInt8))
      rw [hmid_len] at h1
      rw [List.length_replicate, natOfBytesLE_replicate_ff 30] at h2
      rw [← h1, hm, h2]
  have h80_iff : ((b31 &&& 0x80) == 0) = true ↔ b31.toNat < 128 := by
    have h : ∀ b : UInt8, ((b &&& 0x80) == 0) = decide (b.toNat < 128) := by decide
    rw [h, decide_eq_true_eq]
  have h7f_iff : ((b31 &&& 0x7F) == 0x7F) = true ↔ b31.toNat = 127 ∨ b31.toNat = 255 := by
    have h : ∀ b : UInt8, ((b &&& 0x7F) == 0x7F) = decide (b.toNat = 127 ∨ b.toNat = 255) := by
      decide
    rw [h, decide_eq_true_eq]
  have hed_iff : decide (b0 ≥ (0xED : UInt8)) = true ↔ b0.toNat ≥ 237 := by
    have h : ∀ b : UInt8, decide (b ≥ (0xED : UInt8)) = decide (b.toNat ≥ 237) := by decide
    rw [h, decide_eq_true_eq]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  unfold SignalPqxdh.scalarIsInRange
  change (((b31 &&& 0x80) == 0) &&
    !(decide (b0 ≥ (0xED : UInt8)) && (mid == List.replicate 30 0xFF) &&
      ((b31 &&& 0x7F) == 0x7F))) = true ↔ _
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      Bool.and_eq_true, Bool.and_eq_true, h80_iff, hed_iff, hmid_eq, h7f_iff]
  rw [hu, p25519_decomp]
  have h0xED : (0xED : Nat) = 237 := rfl
  have h0x7F : (0x7F : Nat) = 127 := rfl
  have hpow31 : 256 ^ 31 = 256 * 256 ^ 30 := by rw [Nat.pow_succ]; ring
  have hpow30 : 1 ≤ 256 ^ 30 := Nat.one_le_pow 30 256 (by decide)
  have hsub : 256 * (256 ^ 30 - 1) + 256 = 256 * 256 ^ 30 := by omega
  rw [h0xED, h0x7F]
  constructor
  · rintro ⟨h128, hnot⟩
    by_cases h127 : b31.toNat < 127
    · rw [hpow31]; nlinarith
    · have hb31_127 : b31.toNat = 127 := by omega
      by_cases hmid_max : natOfBytesLE mid = 256 ^ 30 - 1
      · have hnot_ed : ¬ (b0.toNat ≥ 237) := fun hed => hnot ⟨⟨hed, hmid_max⟩, Or.inl hb31_127⟩
        omega
      · have hmid_le : natOfBytesLE mid + 1 ≤ 256 ^ 30 - 1 := by omega
        rw [hpow31]; nlinarith
  · intro hlt
    have h128 : b31.toNat < 128 := by
      by_contra hge
      rw [hpow31] at hlt; nlinarith
    refine ⟨h128, fun ⟨⟨hed, hmid_max⟩, h7f⟩ => ?_⟩
    rcases h7f with h127 | h255
    · omega
    · omega

private theorem blockLevelPrims_eq_upd (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    blockLevelPrims X W =
      { blockLevelPrims X W with
        isTorsionFree := fun P => edSmul edOrderL P == edZero } := rfl

private theorem upd_isTorsionFree (B : SignalPqxdh.Primitives)
    (f : EdPoint → Bool) (P : EdPoint) :
    ({ B with isTorsionFree := f } : SignalPqxdh.Primitives).isTorsionFree P = f P := rfl

private theorem blockLevelPrims_isTorsionFree (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (P : EdPoint) :
    (blockLevelPrims X W).isTorsionFree P = (edSmul edOrderL P == edZero) :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.isTorsionFree P)
    (blockLevelPrims_eq_upd X W)).trans (upd_isTorsionFree _ _ P)

private theorem blockLevelPrims_eq_upd_mont (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    blockLevelPrims X W =
      { blockLevelPrims X W with
        montToEd := fun pk s => SignalPqxdh.montLiftEd (u8Vec 32 pk).toList s.toBitVec } := rfl

private theorem upd_montToEd (B : SignalPqxdh.Primitives)
    (f : List UInt8 → UInt8 → Option EdPoint) (pk : List UInt8) (s : UInt8) :
    ({ B with montToEd := f } : SignalPqxdh.Primitives).montToEd pk s = f pk s := rfl

private theorem blockLevelPrims_montToEd (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk : List UInt8) (s : UInt8) :
    (blockLevelPrims X W).montToEd pk s =
      SignalPqxdh.montLiftEd (u8Vec 32 pk).toList s.toBitVec :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.montToEd pk s)
    (blockLevelPrims_eq_upd_mont X W)).trans (upd_montToEd _ _ pk s)

private theorem isCanonicalRef_eq_if_opt (B : SignalPqxdh.Primitives) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef B pk =
      if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk then
        Option.casesOn (B.montToEd pk 0) false B.isTorsionFree
      else false := by
  rw [SignalPqxdh.isCanonicalRef.eq_def]
  split
  · cases B.montToEd pk 0 <;> rfl
  · rfl

private theorem match_none_some_eq_casesOn (m : Option EdPoint) (f : EdPoint → Bool) :
    (match m with | none => false | some P => f P) = Option.casesOn m false f := by
  cases m <;> rfl

private theorem match_edPoint_eq_true (m : Option EdPoint) (f : EdPoint → Bool)
    (h : (match m with | none => false | some Q => f Q) = true) :
    ∃ P, m = some P ∧ f P = true := by
  cases m with
  | none => cases h
  | some P => exact ⟨P, rfl, h⟩

private theorem isCanonicalX25519_fun_eq :
    isCanonicalX25519 = fun bs =>
      (bs.length == 32 && decide (leBytesToNat bs < p25519)) &&
      match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
      | none => false
      | some P => edSmul edOrderL P == edZero := rfl

private theorem isCanonicalX25519_def (bs : List (BitVec 8)) :
    isCanonicalX25519 bs =
      ((bs.length == 32 && decide (leBytesToNat bs < p25519)) &&
      match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
      | none => false
      | some P => edSmul edOrderL P == edZero) :=
  congrFun isCanonicalX25519_fun_eq bs

private theorem match_edPoint_of_some (m : Option EdPoint) (P : EdPoint) (f : EdPoint → Bool) :
    m = some P → f P = true → (match m with | none => false | some Q => f Q) = true := by
  rintro rfl hf
  exact hf

private theorem isCanonicalX25519_eq_true_iff (bs : List (BitVec 8)) :
    isCanonicalX25519 bs = true ↔
      bs.length = 32 ∧ leBytesToNat bs < p25519 ∧
      ∃ P, LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 = some P ∧
        edSmul edOrderL P = edZero := by
  constructor
  · intro h
    rw [isCanonicalX25519_def] at h
    obtain ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨hlen, hlt⟩ := (Bool.and_eq_true _ _).mp hhead
    obtain ⟨P, hm, heq⟩ := match_edPoint_eq_true _ (fun P => edSmul edOrderL P == edZero) htail
    exact ⟨beq_iff_eq.mp hlen, of_decide_eq_true hlt, P, hm, beq_iff_eq.mp heq⟩
  · rintro ⟨hlen, hlt, P, hm, heq⟩
    rw [isCanonicalX25519_def]
    have hhead : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = true :=
      (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen, decide_eq_true hlt⟩
    have htail : (match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
        | none => false | some P => edSmul edOrderL P == edZero) = true :=
      match_edPoint_of_some _ P (fun P => edSmul edOrderL P == edZero) hm (beq_iff_eq.mpr heq)
    exact (Bool.and_eq_true _ _).mpr ⟨hhead, htail⟩

private theorem isCanonical_eq_blockLevel_aux (B : SignalPqxdh.Primitives)
    (sv h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
    let M : SignalPqxdh.Primitives :=
      { B1 with sigVerify := sv, isCanonical := SignalPqxdh.isCanonicalRef B1,
                hkdfDerive96 := h96, rootCreateChain := rcc, chainKdfSeed := cks,
                chainKdfNext := ckn, deriveMsgKeys := dmk, aeadEnc := ae, aeadDec := ad }
    M.isCanonical pk = SignalPqxdh.isCanonicalRef B pk := rfl

/-- Closed equivalence between `(modelPrims X W).isCanonical` and `isCanonicalX25519`. -/
theorem modelPrims_isCanonical_eq_isCanonicalX25519
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    (modelPrims X W).isCanonical pk = isCanonicalX25519 (ofU8 pk) := by
  have hmp : (modelPrims X W).isCanonical pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims X W) pk := by
    rw [modelPrims.eq_1]
    exact isCanonical_eq_blockLevel_aux (blockLevelPrims X W) _ _ _ _ _ _ _ _ pk
  rw [hmp, isCanonicalRef_eq_if_opt, isCanonicalX25519_def,
      match_none_some_eq_casesOn _ (fun P => edSmul edOrderL P == edZero)]
  by_cases hlen : pk.length = 32
  · have hlen_pk : (pk.length == 32) = true := beq_iff_eq.mpr hlen
    have hlen_of : ((ofU8 pk).length == 32) = true := by rw [ofU8_length, hlen]; rfl
    have hsc := scalarIsInRange_eq_decide_lt_p25519 hlen
    have h80_of_lt : leBytesToNat (ofU8 pk) < p25519 → ((pk.getD 31 0 &&& 0x80) == 0) = true := by
      intro hlt
      rw [leBytesToNat_ofU8] at hlt
      have hn255 : natOfBytesLE pk < 2 ^ 255 := lt_trans hlt p25519_lt_two_pow_255
      have hb31 := getD_toNat_eq_div_mod pk 31
      have hlt32 : natOfBytesLE pk < 256 ^ 32 := lt_trans hn255 (by decide)
      rw [Nat.mod_eq_of_lt (by omega : natOfBytesLE pk / 256 ^ 31 < 256)] at hb31
      have h128 : (pk.getD 31 0).toNat < 128 := by
        have h255 : 2 ^ 255 = 128 * 256 ^ 31 := by decide
        omega
      have hc : ∀ b : UInt8, b.toNat < 128 → ((b &&& 0x80) == 0) = true := by decide
      exact hc _ h128
    rw [hlen_pk, hlen_of, hsc]
    by_cases hlt : leBytesToNat (ofU8 pk) < p25519
    · have h80 := h80_of_lt hlt
      rw [h80, decide_eq_true hlt]
      have hcond_l : ((true && true && true) = true) := rfl
      rw [ite_eq_left hcond_l, show (true && true) = true from rfl, Bool.true_and]
      rw [blockLevelPrims_montToEd X W pk 0]
      have h0 : (0 : UInt8).toBitVec = 0#8 := rfl
      rw [h0, u8Vec_toList_of_length hlen, montLiftEd_eq_x25519MontToEdwards,
          funext (blockLevelPrims_isTorsionFree X W)]
    · rw [decide_eq_false hlt]
      have hcond_f : ¬ (((true && ((pk.getD 31 0 &&& 0x80) == 0) && false) = true)) := by
        cases ((pk.getD 31 0 &&& 0x80) == 0) <;> decide
      rw [ite_eq_right hcond_f, show (true && false) = false from rfl, Bool.false_and]
  · have hlen_pk : (pk.length == 32) = false := beq_eq_false_iff_ne.mpr hlen
    have hlen_of : ((ofU8 pk).length == 32) = false :=
      beq_eq_false_iff_ne.mpr (by rw [ofU8_length]; exact hlen)
    rw [hlen_pk, hlen_of]
    have hcond_f : ¬ (((false && ((pk.getD 31 0 &&& 0x80) == 0) &&
        SignalPqxdh.scalarIsInRange pk) = true)) := by
      cases ((pk.getD 31 0 &&& 0x80) == 0) <;> cases SignalPqxdh.scalarIsInRange pk <;> decide
    rw [ite_eq_right hcond_f, Bool.false_and, Bool.false_and]

/-! ## 3. Curve / Twist Arithmetic Helpers -/

private theorem montToEdwards_congr_mod_p {bs1 bs2 : List (BitVec 8)}
    (hu : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs1 % p25519 =
          LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs2 % p25519) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs1 0 =
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs2 0 := by
  cases hm2 : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs2 0 with
  | none =>
    rw [montToEdwards_eq_none_iff_raw] at hm2 ⊢
    rwa [hu]
  | some P =>
    rw [montToEdwards_eq_some_iff] at hm2 ⊢
    rwa [hu]

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

private theorem montToEdwards_isSome_of_edOnCurve {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) :
    (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (edToMontU P)) 0).isSome = true := by
  rw [montToEdwards_edToMontU_even hP hne]; rfl

private theorem montToEdwards_none_of_twOnCurve {P : EdPoint}
    (hP : twOnCurve P = true) (hPx : P.x ≠ 0) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (twToMontU P)) 0 = none := by
  cases hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (twToMontU P)) 0 with
  | none => rfl
  | some R =>
    exfalso
    have hR_on : edOnCurve R = true := montToEdwards_some_onCurve hm
    have huR : edToMontU R = twToMontU P := by
      have h1 := montToEdwards_some_edToMontU hm
      rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt P), Nat.mod_eq_of_lt (twToMontU_lt P)] at h1
      exact h1
    have hu_ne0 : twToMontU P ≠ 0 := mt (twToMontU_eq_zero_iff hP).mp hPx
    have hRx_ne : R.x ≠ 0 := mt (edToMontU_eq_zero_iff hR_on).mpr (huR.trans_ne hu_ne0)
    have hsq : FpIsSquare (Fp.ofNat (montRHS (twToMontU P))) :=
      huR ▸ edOnCurve_montRHS_isSquare hR_on hRx_ne
    exact twOnCurve_montRHS_not_isSquare hP hPx hsq

private theorem edNatSmul_mod_edOrderL {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (n : Nat) :
    edNatSmul n P = edNatSmul (n % edOrderL) P := by
  conv_lhs => rw [← Nat.mod_add_div n edOrderL]
  rw [edNatSmul_add (n % edOrderL) (edOrderL * (n / edOrderL)) hP,
      Nat.mul_comm edOrderL (n / edOrderL),
      edNatSmul_mul (n / edOrderL) edOrderL hP,
      hL, edNatSmul_edZero, edAdd_edZero (edOnCurve_edNatSmul _ hP)]

private theorem twNatSmul_mod_twistOrderL {P : EdPoint} (hP : twOnCurve P = true)
    (hL : twNatSmul twistOrderL P = twZero) (n : Nat) :
    twNatSmul n P = twNatSmul (n % twistOrderL) P := by
  conv_lhs => rw [← Nat.mod_add_div n twistOrderL]
  rw [twNatSmul_add (n % twistOrderL) (twistOrderL * (n / twistOrderL)) hP,
      Nat.mul_comm twistOrderL (n / twistOrderL),
      twNatSmul_mul (n / twistOrderL) twistOrderL hP,
      hL, twNatSmul_twZero, twAdd_twZero (twOnCurve_twNatSmul _ hP)]

private theorem twNeg_twAdd_eq {P Q : EdPoint} (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    twNeg (twAdd P Q) = twAdd (twNeg P) (twNeg Q) := by
  have hPQ := twOnCurve_twAdd hP hQ
  have hR := twOnCurve_twAdd (twOnCurve_twNeg hP) (twOnCurve_twNeg hQ)
  have hsum : twAdd (twAdd P Q) (twAdd (twNeg P) (twNeg Q)) = twZero := by
    rw [twAdd_assoc hP hQ hR,
        ← twAdd_assoc hQ (twOnCurve_twNeg hP) (twOnCurve_twNeg hQ),
        twAdd_comm Q (twNeg P),
        twAdd_assoc (twOnCurve_twNeg hP) hQ (twOnCurve_twNeg hQ),
        twAdd_twNeg_self hQ, twAdd_twZero (twOnCurve_twNeg hP), twAdd_twNeg_self hP]
  have h1 := congrArg (twAdd (twNeg (twAdd P Q))) hsum
  rw [← twAdd_assoc (twOnCurve_twNeg hPQ) hPQ hR,
      twAdd_comm (twNeg (twAdd P Q)) (twAdd P Q),
      twAdd_twNeg_self hPQ, twZero_twAdd hR, twAdd_twZero (twOnCurve_twNeg hPQ)] at h1
  exact h1.symm

private theorem twNatSmul_twNeg (n : Nat) {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul n (twNeg P) = twNeg (twNatSmul n P) := by
  induction n with
  | zero => exact edNeg_edZero.symm
  | succ k ih =>
    simp only [twNatSmul]
    rw [ih, twNeg_twAdd_eq hP (twOnCurve_twNatSmul k hP)]

private theorem edNatSmul_edNeg_all (n : Nat) (P : EdPoint) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero => exact edNeg_edZero.symm
  | succ k ih =>
    simp only [edNatSmul]
    rw [ih, ← LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards.edNeg_edAdd P (edNatSmul k P)]

private theorem edOnCurve_eq_or_edNeg_of_edToMontU_eq {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : edToMontU P = edToMontU Q) :
    P = Q ∨ P = edNeg Q := by
  by_cases hpar : P.x % 2 = Q.x % 2
  · exact Or.inl (edOnCurve_eq_of_edToMontU_eq hP hQ hPx hQx hu hpar)
  · right
    have hQ_lt : Q.x < p25519 := edOnCurve_x_lt hQ
    have hQ_mod_ne : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQ_lt]; exact hQx
    have hNegQx : (edNeg Q).x ≠ 0 := by
      dsimp only [edNeg]; unfold fpNeg
      rw [Nat.mod_eq_of_lt hQ_lt, Nat.mod_eq_of_lt (by omega)]; omega
    have hNegPar : P.x % 2 = (edNeg Q).x % 2 := by
      dsimp only [edNeg]
      rw [fpNeg_mod_two_of_ne_zero hQ_mod_ne, Nat.mod_eq_of_lt hQ_lt]
      rcases Nat.mod_two_eq_zero_or_one P.x with h0 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one Q.x with q0 | q1 <;> omega
    exact edOnCurve_eq_of_edToMontU_eq hP (edOnCurve_edNeg hQ) hPx hNegQx
      (hu.trans (edToMontU_edNeg Q).symm) hNegPar

private theorem twOnCurve_eq_or_twNeg_of_twToMontU_eq {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : twToMontU P = twToMontU Q) :
    P = Q ∨ P = twNeg Q := by
  by_cases hpar : P.x % 2 = Q.x % 2
  · exact Or.inl (twOnCurve_eq_of_twToMontU_eq hP hQ hPx hQx hu hpar)
  · right
    have hQ_lt : Q.x < p25519 := twOnCurve_x_lt hQ
    have hQ_mod_ne : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQ_lt]; exact hQx
    have hNegQx : (twNeg Q).x ≠ 0 := by
      dsimp only [twNeg, edNeg]; unfold fpNeg
      rw [Nat.mod_eq_of_lt hQ_lt, Nat.mod_eq_of_lt (by omega)]; omega
    have hNegPar : P.x % 2 = (twNeg Q).x % 2 := by
      dsimp only [twNeg, edNeg]
      rw [fpNeg_mod_two_of_ne_zero hQ_mod_ne, Nat.mod_eq_of_lt hQ_lt]
      rcases Nat.mod_two_eq_zero_or_one P.x with h0 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one Q.x with q0 | q1 <;> omega
    exact twOnCurve_eq_of_twToMontU_eq hP (twOnCurve_twNeg hQ) hPx hNegQx
      (hu.trans (twToMontU_twNeg Q).symm) hNegPar

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

private theorem edToMontU_edNatSmul_eq_iff {P : EdPoint} (hP : edOnCurve P = true)
    (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a b : ZMod l25519} (ha : a ≠ 0) (hb : b ≠ 0) :
    edToMontU (edNatSmul a.val P) = edToMontU (edNatSmul b.val P) ↔ a = b ∨ a = -b := by
  constructor
  · intro hu
    have hPa_on := edOnCurve_edNatSmul a.val hP
    have hPb_on := edOnCurve_edNatSmul b.val hP
    have hPa_x : (edNatSmul a.val P).x ≠ 0 := by
      intro hx0
      have h2 := (edNatSmul_two_eq_zero_iff hPa_on).mpr hx0
      rw [← edNatSmul_mul 2 a.val hP, edNatSmul_mod_edOrderL hP hL, edOrderL_eq_l25519] at h2
      have h2v : (2 * a.val) % l25519 = ((2 : ZMod l25519) * a).val := by
        rw [ZMod.val_mul, show (2 : ZMod l25519).val = 2 from
          ZMod.val_natCast_of_lt (by unfold l25519; decide +kernel)]
      rw [h2v] at h2
      have h2ne : (2 : ZMod l25519) ≠ 0 := by
        intro h20; have hv := congrArg ZMod.val h20
        rw [show (2 : ZMod l25519).val = 2 from
              ZMod.val_natCast_of_lt (by unfold l25519; decide +kernel),
            ZMod.val_zero] at hv; omega
      have : Fact (Nat.Prime l25519) := ⟨by rw [← edOrderL_eq_l25519]; exact Nat.prime_def.mpr edOrderL_prime⟩
      exact edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL (mul_ne_zero h2ne ha) h2
    have hPb_x : (edNatSmul b.val P).x ≠ 0 := by
      intro hx0
      have h2 := (edNatSmul_two_eq_zero_iff hPb_on).mpr hx0
      rw [← edNatSmul_mul 2 b.val hP, edNatSmul_mod_edOrderL hP hL, edOrderL_eq_l25519] at h2
      have h2v : (2 * b.val) % l25519 = ((2 : ZMod l25519) * b).val := by
        rw [ZMod.val_mul, show (2 : ZMod l25519).val = 2 from
          ZMod.val_natCast_of_lt (by unfold l25519; decide +kernel)]
      rw [h2v] at h2
      have h2ne : (2 : ZMod l25519) ≠ 0 := by
        intro h20; have hv := congrArg ZMod.val h20
        rw [show (2 : ZMod l25519).val = 2 from
              ZMod.val_natCast_of_lt (by unfold l25519; decide +kernel),
            ZMod.val_zero] at hv; omega
      have : Fact (Nat.Prime l25519) := ⟨by rw [← edOrderL_eq_l25519]; exact Nat.prime_def.mpr edOrderL_prime⟩
      exact edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL (mul_ne_zero h2ne hb) h2
    rcases edOnCurve_eq_or_edNeg_of_edToMontU_eq hPa_on hPb_on hPa_x hPb_x hu with h | h
    · exact Or.inl (edNatSmul_zmod_inj hP hne hL h)
    · rw [← edNatSmul_zmod_neg hP hL b] at h
      exact Or.inr (edNatSmul_zmod_inj hP hne hL h)
  · rintro (rfl | rfl)
    · rfl
    · rw [edNatSmul_zmod_neg hP hL b, edToMontU_edNeg]

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
  unfold SignalPqxdh.XeddsaRom.PrimeL25519.decodeScalarBytes
  rw [ZMod.val_natCast]

private theorem modelPrims_realPE_x25519_of_len32 (X : UnreachedPqxdhPrimitives)
    (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X realPEParams).x25519 a pk =
      toU8 (x25519 (CryptoGames.Ratchet.clampScalar (u8Vec 32 a)).toList (ofU8 pk)) := by
  dsimp only [modelPrims, blockLevelPrims, realPEParams,
    CryptoVerification.SignalSession.realCrypto]
  unfold vecU8
  rw [x25519Ref_toList, u8Vec_toList_of_length hpk]

private theorem modelPrims_realPE_x25519Base_eq (X : UnreachedPqxdhPrimitives) (sk : List UInt8) :
    (modelPrims X realPEParams).x25519Base sk =
      toU8 (natToLeBytes 32 (edToMontU (edNatSmul (clampedScalarZMod sk).val edBasepoint))) := by
  dsimp only [modelPrims, blockLevelPrims, realPEParams,
    CryptoVerification.SignalSession.realCrypto]
  unfold vecU8
  rw [x25519PubFromSecretRef_toList, x25519Pubkey_eq_edNatSmul,
      edNatSmul_mod_edOrderL edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint,
      clampScalar_ratchet_u8Vec_mod_edOrderL sk]

/-! ## 4. Structural Characterization & Laws of `realPow8` -/

private theorem realPow8_natToLeBytes_zero :
    realPow8 (toU8 (natToLeBytes 32 0)) = toU8 (natToLeBytes 32 0) := by
  unfold realPow8
  have hlen : (toU8 (natToLeBytes 32 0)).length == 32 := by
    rw [toU8_length, natToLeBytes_len]; rfl
  rw [hlen]; simp only [↓reduceIte, ofU8_toU8]
  rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, x25519Ladder_zero]

/-- `realPow8` always returns 32 bytes. -/
theorem realPow8_len (pk : List UInt8) : (realPow8 pk).length = 32 := by
  unfold realPow8
  split
  · rw [toU8_length, natToLeBytes_len]
  · simp

private theorem realPow8_spec_32 {pk : List UInt8} (hpk : pk.length = 32) :
    ∃ u : Nat,
      u < p25519 ∧
      realPow8 pk = toU8 (natToLeBytes 32 u) ∧
      realPow8 (realPow8 pk) = realPow8 pk ∧
      (∀ s : List (BitVec 8), x25519 s (natToLeBytes 32 u) = x25519 s (ofU8 pk)) ∧
      (u = 0 ∨
       (∃ Q : EdPoint, edOnCurve Q = true ∧ Q.x ≠ 0 ∧ edNatSmul edOrderL Q = edZero ∧
         edToMontU Q = u) ∨
       (∃ Q : EdPoint, twOnCurve Q = true ∧ Q.x ≠ 0 ∧ twNatSmul twistOrderL Q = twZero ∧
         twToMontU Q = u)) := by
  let bs := ofU8 pk
  let u1 := LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs % p25519
  have hu1_lt : u1 < p25519 := Nat.mod_lt _ p25519_pos
  have hp8_eq : realPow8 pk = toU8 (natToLeBytes 32
      (x25519Ladder
        (match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
         | some _ => eEd | none => eTw) u1)) := by
    unfold realPow8
    rw [beq_iff_eq.mpr hpk]; simp only [↓reduceIte]
    rw [montLiftEd_eq_x25519MontToEdwards, twistOrderL_spec_eq]
    change toU8 (natToLeBytes 32 (x25519Ladder
      (match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
       | some _ => eEd | none => eTw)
      (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs))) = _
    rw [x25519Ladder_mod]
  by_cases hu0 : u1 = 0
  · refine ⟨0, p25519_pos, ?_, ?_, ?_, Or.inl rfl⟩
    · rw [hp8_eq, hu0, x25519Ladder_zero]
    · rw [hp8_eq, hu0, x25519Ladder_zero, realPow8_natToLeBytes_zero]
    · intro s
      apply x25519_uCoord_congr
      rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, Nat.zero_mod]
      exact hu0.symm
  · have hu1_pos : 0 < u1 := Nat.pos_of_ne_zero hu0
    rcases mont_lift_dichotomy hu1_pos hu1_lt with
      ⟨P, hP, hPx, huP⟩ | ⟨P, hP, hPx, huP⟩
    · have hP_ne0 : P ≠ edZero := fun h0 => hPx (congrArg EdPoint.x h0)
      have hmont_some :
          (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0).isSome =
            true := by
        have hc := montToEdwards_congr_mod_p (bs1 := bs) (bs2 := natToLeBytes 32 (edToMontU P))
          (by rw [decodeU255_natToLeBytes_of_lt_p (edToMontU_lt P),
                  Nat.mod_eq_of_lt (edToMontU_lt P)]; exact huP.symm)
        rw [hc]; exact montToEdwards_isSome_of_edOnCurve hP hP_ne0
      obtain ⟨Pm, hPm⟩ := Option.isSome_iff_exists.mp hmont_some
      let Q := edNatSmul eEd P
      have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul eEd hP
      have hQ_ord : edNatSmul edOrderL Q = edZero := by
        dsimp only [Q]
        rw [← edNatSmul_mul edOrderL eEd hP, eEd_div_eight,
            show edOrderL * (8 * ((3 * edOrderL + 1) / 8)) =
              ((3 * edOrderL + 1) / 8) * (8 * edOrderL) by ring,
            edNatSmul_mul _ (8 * edOrderL) hP,
            edNatSmul_eight_mul_edOrderL hP, edNatSmul_edZero]
      have hp8_Q : realPow8 pk = toU8 (natToLeBytes 32 (edToMontU Q)) := by
        rw [hp8_eq, hPm, ← huP, x25519Ladder_edToMontU eEd_lt_two_pow_255 hP]
      have hx_Q : ∀ s : List (BitVec 8),
          x25519 s (natToLeBytes 32 (edToMontU Q)) = x25519 s bs := by
        intro s
        obtain ⟨m, hk, _, _⟩ := clampScalar_eight_mul s
        have hx_rhs : x25519 s bs = natToLeBytes 32 (edToMontU (edNatSmul (clampScalar s) P)) := by
          have hc := x25519_uCoord_congr s bs (natToLeBytes 32 (edToMontU P))
            (by rw [decodeU255_natToLeBytes_of_lt_p (edToMontU_lt P),
                    Nat.mod_eq_of_lt (edToMontU_lt P)]; exact huP.symm)
          rw [hc]; unfold x25519
          rw [decodeU255_natToLeBytes_of_lt_p (edToMontU_lt P),
              x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s) hP]
        have hx_lhs : x25519 s (natToLeBytes 32 (edToMontU Q)) =
            natToLeBytes 32 (edToMontU (edNatSmul (clampScalar s * eEd) P)) := by
          unfold x25519
          rw [decodeU255_natToLeBytes_of_lt_p (edToMontU_lt Q),
              x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s) hQ_on,
              ← edNatSmul_mul (clampScalar s) eEd hP]
        rw [hx_lhs, hx_rhs, hk]
        have hexp : 8 * m * eEd = 3 * m * (8 * edOrderL) + 8 * m := by unfold eEd; ring
        rw [hexp, edNatSmul_add _ _ hP, edNatSmul_mul (3 * m) (8 * edOrderL) hP,
            edNatSmul_eight_mul_edOrderL hP, edNatSmul_edZero,
            edZero_edAdd (edOnCurve_edNatSmul _ hP)]
      by_cases hQx : Q.x = 0
      · have huQ0 : edToMontU Q = 0 := (edToMontU_eq_zero_iff hQ_on).mpr hQx
        refine ⟨0, p25519_pos, hp8_Q.trans (by rw [huQ0]), ?_, ?_, Or.inl rfl⟩
        · rw [hp8_Q, huQ0, realPow8_natToLeBytes_zero]
        · intro s; rw [← huQ0]; exact hx_Q s
      · have hQ_ne0 : Q ≠ edZero := fun h0 => hQx (congrArg EdPoint.x h0)
        refine ⟨edToMontU Q, edToMontU_lt Q, hp8_Q, ?_, hx_Q,
          Or.inr (Or.inl ⟨Q, hQ_on, hQx, hQ_ord, rfl⟩)⟩
        rw [hp8_Q]
        unfold realPow8
        have hlenQ : (toU8 (natToLeBytes 32 (edToMontU Q))).length == 32 := by
          rw [toU8_length, natToLeBytes_len]; rfl
        rw [hlenQ]; simp only [↓reduceIte, ofU8_toU8]
        rw [montLiftEd_eq_x25519MontToEdwards, twistOrderL_spec_eq]
        obtain ⟨Qm, hQm⟩ := Option.isSome_iff_exists.mp (montToEdwards_isSome_of_edOnCurve hQ_on hQ_ne0)
        rw [hQm]
        change toU8 (natToLeBytes 32 (x25519Ladder eEd
          (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
            (natToLeBytes 32 (edToMontU Q))))) = _
        rw [decodeU255_natToLeBytes_of_lt_p (edToMontU_lt Q),
            x25519Ladder_edToMontU eEd_lt_two_pow_255 hQ_on,
            ← edNatSmul_mul eEd eEd hP, eEd_sq_eq,
            edNatSmul_add _ _ hP, edNatSmul_mul qEd (8 * edOrderL) hP,
            edNatSmul_eight_mul_edOrderL hP, edNatSmul_edZero, edZero_edAdd hQ_on]
    · have hmont_none :
          LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 = none := by
        have hc := montToEdwards_congr_mod_p (bs1 := bs) (bs2 := natToLeBytes 32 (twToMontU P))
          (by rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt P),
                  Nat.mod_eq_of_lt (twToMontU_lt P)]; exact huP.symm)
        rw [hc]; exact montToEdwards_none_of_twOnCurve hP hPx
      let Q := twNatSmul eTw P
      have hQ_on : twOnCurve Q = true := twOnCurve_twNatSmul eTw hP
      have hQ_ord : twNatSmul twistOrderL Q = twZero := by
        dsimp only [Q]
        rw [← twNatSmul_mul twistOrderL eTw hP, eTw_div_four,
            show twistOrderL * (4 * ((3 * twistOrderL + 1) / 4)) =
              ((3 * twistOrderL + 1) / 4) * (4 * twistOrderL) by ring,
            twNatSmul_mul _ (4 * twistOrderL) hP,
            twNatSmul_four_mul_twistOrderL hP, twNatSmul_twZero]
      have hp8_Q : realPow8 pk = toU8 (natToLeBytes 32 (twToMontU Q)) := by
        rw [hp8_eq, hmont_none, ← huP, x25519Ladder_twToMontU eTw_lt_two_pow_255 hP]
      have hx_Q : ∀ s : List (BitVec 8),
          x25519 s (natToLeBytes 32 (twToMontU Q)) = x25519 s bs := by
        intro s
        obtain ⟨m, hk, _, _⟩ := clampScalar_eight_mul s
        have hx_rhs : x25519 s bs = natToLeBytes 32 (twToMontU (twNatSmul (clampScalar s) P)) := by
          have hc := x25519_uCoord_congr s bs (natToLeBytes 32 (twToMontU P))
            (by rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt P),
                    Nat.mod_eq_of_lt (twToMontU_lt P)]; exact huP.symm)
          rw [hc]; unfold x25519
          rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt P),
              x25519Ladder_twToMontU (clampScalar_lt_two_pow_255 s) hP]
        have hx_lhs : x25519 s (natToLeBytes 32 (twToMontU Q)) =
            natToLeBytes 32 (twToMontU (twNatSmul (clampScalar s * eTw) P)) := by
          unfold x25519
          rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt Q),
              x25519Ladder_twToMontU (clampScalar_lt_two_pow_255 s) hQ_on,
              ← twNatSmul_mul (clampScalar s) eTw hP]
        rw [hx_lhs, hx_rhs, hk]
        have hexp : 8 * m * eTw = 6 * m * (4 * twistOrderL) + 8 * m := by unfold eTw; ring
        rw [hexp, twNatSmul_add _ _ hP, twNatSmul_mul (6 * m) (4 * twistOrderL) hP,
            twNatSmul_four_mul_twistOrderL hP, twNatSmul_twZero,
            twZero_twAdd (twOnCurve_twNatSmul _ hP)]
      by_cases hQx : Q.x = 0
      · have huQ0 : twToMontU Q = 0 := (twToMontU_eq_zero_iff hQ_on).mpr hQx
        refine ⟨0, p25519_pos, hp8_Q.trans (by rw [huQ0]), ?_, ?_, Or.inl rfl⟩
        · rw [hp8_Q, huQ0, realPow8_natToLeBytes_zero]
        · intro s; rw [← huQ0]; exact hx_Q s
      · refine ⟨twToMontU Q, twToMontU_lt Q, hp8_Q, ?_, hx_Q,
          Or.inr (Or.inr ⟨Q, hQ_on, hQx, hQ_ord, rfl⟩)⟩
        rw [hp8_Q]
        unfold realPow8
        have hlenQ : (toU8 (natToLeBytes 32 (twToMontU Q))).length == 32 := by
          rw [toU8_length, natToLeBytes_len]; rfl
        rw [hlenQ]; simp only [↓reduceIte, ofU8_toU8]
        rw [montLiftEd_eq_x25519MontToEdwards, twistOrderL_spec_eq,
            montToEdwards_none_of_twOnCurve hQ_on hQx]
        change toU8 (natToLeBytes 32 (x25519Ladder eTw
          (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
            (natToLeBytes 32 (twToMontU Q))))) = _
        rw [decodeU255_natToLeBytes_of_lt_p (twToMontU_lt Q),
            x25519Ladder_twToMontU eTw_lt_two_pow_255 hQ_on,
            ← twNatSmul_mul eTw eTw hP, eTw_sq_eq,
            twNatSmul_add _ _ hP, twNatSmul_mul qTw (4 * twistOrderL) hP,
            twNatSmul_four_mul_twistOrderL hP, twNatSmul_twZero, twZero_twAdd hQ_on]

/-- `realPow8` is idempotent on all byte strings. -/
theorem realPow8_idemp (pk : List UInt8) : realPow8 (realPow8 pk) = realPow8 pk := by
  by_cases hpk : pk.length = 32
  · exact (realPow8_spec_32 hpk).choose_spec.2.2.1
  · have hp1 : realPow8 pk = toU8 (natToLeBytes 32 0) := by
      unfold realPow8
      rw [beq_eq_false_iff_ne.mpr hpk]
      simp only [Bool.false_eq_true, ↓reduceIte]
      decide
    rw [hp1, realPow8_natToLeBytes_zero]

/-- `realPow8` fixes every canonical prime-order Curve25519 public key. -/
theorem realPow8_of_isCanonicalX25519 {pk : List UInt8}
    (h : isCanonicalX25519 (ofU8 pk) = true) :
    realPow8 pk = pk := by
  obtain ⟨hlen_of, hlt_p, P, hmont, hmont_cond⟩ := (isCanonicalX25519_eq_true_iff _).mp h
  have hlen : pk.length = 32 := by simpa using hlen_of
  have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
  have huP : edToMontU P = leBytesToNat (ofU8 pk) := by
    have h1 := montToEdwards_some_edToMontU hmont
    unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 at h1
    rw [List.take_of_length_le (Nat.le_of_eq hlen_of),
        Nat.mod_eq_of_lt (lt_trans hlt_p p25519_lt_two_pow_255),
        Nat.mod_eq_of_lt hlt_p] at h1
    exact h1
  unfold realPow8
  rw [beq_iff_eq.mpr hlen]; simp only [↓reduceIte]
  rw [montLiftEd_eq_x25519MontToEdwards, twistOrderL_spec_eq, hmont]
  change toU8 (natToLeBytes 32 (x25519Ladder eEd
    (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 (ofU8 pk)))) = pk
  rw [← x25519Ladder_mod, ← montToEdwards_some_edToMontU hmont,
      x25519Ladder_edToMontU eEd_lt_two_pow_255 hP_on]
  have heEd_P : edNatSmul eEd P = P := by
    unfold eEd
    rw [edNatSmul_add (3 * edOrderL) 1 hP_on, edNatSmul_mul 3 edOrderL hP_on,
        hP_ord, edNatSmul_edZero, edNatSmul_one hP_on, edZero_edAdd hP_on]
  rw [heEd_P, huP, leBytesToNat_ofU8, toU8_natToLeBytes, ← hlen, bytesOfNatLE_natOfBytesLE]

private theorem modelPrims_realPE_x25519_realPow8 (X : UnreachedPqxdhPrimitives)
    (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X realPEParams).x25519 a (realPow8 pk) = (modelPrims X realPEParams).x25519 a pk := by
  obtain ⟨u, _, hp8, _, hx, _⟩ := realPow8_spec_32 hpk
  rw [modelPrims_realPE_x25519_of_len32 X a (realPow8 pk) (realPow8_len pk),
      modelPrims_realPE_x25519_of_len32 X a pk hpk,
      hp8, ofU8_toU8, hx]

/-! ## 5. Exported `ModelPrimsSharedAssumptions` Discharges (for arbitrary `kemKeyGen`) -/

theorem realX25519_zero_iff (X : UnreachedPqxdhPrimitives) (a1 a2 pk : List UInt8)
    (_ha1 : a1.length = 32) (_ha2 : a2.length = 32) (hpk : pk.length = 32) :
    (modelPrims X realPEParams).x25519 a1 pk = List.replicate 32 0 ↔
      (modelPrims X realPEParams).x25519 a2 pk = List.replicate 32 0 := by
  rw [modelPrims_realPE_x25519_of_len32 X a1 pk hpk,
      modelPrims_realPE_x25519_of_len32 X a2 pk hpk]
  have h0_iff : ∀ bs : List (BitVec 8),
      toU8 bs = List.replicate 32 (0 : UInt8) ↔ bs = List.replicate 32 0#8 := by
    intro bs
    constructor
    · intro h
      have h1 := congrArg ofU8 h
      rw [ofU8_toU8] at h1
      exact h1.trans (by decide)
    · rintro rfl; decide
  rw [h0_iff, h0_iff, x25519_eq_zero_iff_lowOrder, x25519_eq_zero_iff_lowOrder]

theorem realX25519_canon_base (X : UnreachedPqxdhPrimitives) (e : List UInt8) (_he : e.length = 32) :
    (modelPrims X realPEParams).isCanonical ((modelPrims X realPEParams).x25519Base e) = true := by
  rw [modelPrims_isCanonical_eq_isCanonicalX25519]
  dsimp only [modelPrims, blockLevelPrims, realPEParams,
    CryptoVerification.SignalSession.realCrypto]
  unfold vecU8
  rw [ofU8_toU8, x25519PubFromSecretRef_toList]
  exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint

theorem realX25519_canon_x25519 (X : UnreachedPqxdhPrimitives) (a pk : List UInt8)
    (_ha : a.length = 32) (hcan : (modelPrims X realPEParams).isCanonical pk = true) :
    (modelPrims X realPEParams).isCanonical ((modelPrims X realPEParams).x25519 a pk) = true := by
  rw [modelPrims_isCanonical_eq_isCanonicalX25519] at hcan ⊢
  have hlen : pk.length = 32 := by
    have hlen_of := ((isCanonicalX25519_eq_true_iff _).mp hcan).1
    simpa using hlen_of
  rw [modelPrims_realPE_x25519_of_len32 X a pk hlen, ofU8_toU8]
  exact isCanonicalX25519_x25519 hcan

theorem realX25519_pow8_congr (X : UnreachedPqxdhPrimitives) (a pk1 pk2 : List UInt8)
    (_ha : a.length = 32) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hpow : realPow8 pk1 = realPow8 pk2) :
    (modelPrims X realPEParams).x25519 a pk1 = (modelPrims X realPEParams).x25519 a pk2 := by
  rw [← modelPrims_realPE_x25519_realPow8 X a pk1 h1, hpow,
      modelPrims_realPE_x25519_realPow8 X a pk2 h2]

theorem realX25519_congr_of_base_eq (X : UnreachedPqxdhPrimitives) (a1 a2 pk : List UInt8)
    (_ha1 : a1.length = 32) (_ha2 : a2.length = 32)
    (hcan : (modelPrims X realPEParams).isCanonical pk = true)
    (hbase : (modelPrims X realPEParams).x25519Base a1 =
      (modelPrims X realPEParams).x25519Base a2) :
    (modelPrims X realPEParams).x25519 a1 pk = (modelPrims X realPEParams).x25519 a2 pk := by
  rw [modelPrims_isCanonical_eq_isCanonicalX25519] at hcan
  obtain ⟨hlen_of, _, P, hmont, hmont_cond⟩ := (isCanonicalX25519_eq_true_iff _).mp hcan
  have hpk : pk.length = 32 := by simpa using hlen_of
  have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
  have hP_ne : P ≠ edZero := montToEdwards_some_ne_edZero hmont
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
  have huP : edToMontU P =
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 (ofU8 pk) % p25519 :=
    montToEdwards_some_edToMontU hmont
  rw [modelPrims_realPE_x25519Base_eq, modelPrims_realPE_x25519Base_eq] at hbase
  have hu_base : edToMontU (edNatSmul (clampedScalarZMod a1).val edBasepoint) =
      edToMontU (edNatSmul (clampedScalarZMod a2).val edBasepoint) := by
    have hbv := congrArg (fun l => leBytesToNat (ofU8 l)) hbase
    rwa [ofU8_toU8, ofU8_toU8,
         leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32),
         leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32)] at hbv
  have hpm := (edToMontU_edNatSmul_eq_iff edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint (clampedScalarZMod_ne_zero a1)
    (clampedScalarZMod_ne_zero a2)).mp hu_base
  have hu_P : edToMontU (edNatSmul (clampedScalarZMod a1).val P) =
      edToMontU (edNatSmul (clampedScalarZMod a2).val P) :=
    (edToMontU_edNatSmul_eq_iff hP_on hP_ne hP_ord
      (clampedScalarZMod_ne_zero a1) (clampedScalarZMod_ne_zero a2)).mpr hpm
  have hx_eval : ∀ a : List UInt8,
      (modelPrims X realPEParams).x25519 a pk =
        toU8 (natToLeBytes 32 (edToMontU (edNatSmul (clampedScalarZMod a).val P))) := by
    intro a
    rw [modelPrims_realPE_x25519_of_len32 X a pk hpk]
    unfold x25519
    rw [← x25519Ladder_mod, ← huP,
        x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 _) hP_on,
        edNatSmul_mod_edOrderL hP_on hP_ord, clampScalar_ratchet_u8Vec_mod_edOrderL a]
  rw [hx_eval a1, hx_eval a2, hu_P]

theorem realX25519_canon_pow8_inj (X : UnreachedPqxdhPrimitives) (pk1 pk2 : List UInt8)
    (h1 : (modelPrims X realPEParams).isCanonical pk1 = true)
    (h2 : (modelPrims X realPEParams).isCanonical pk2 = true)
    (hpow : realPow8 pk1 = realPow8 pk2) : pk1 = pk2 := by
  rw [modelPrims_isCanonical_eq_isCanonicalX25519] at h1 h2
  rwa [realPow8_of_isCanonicalX25519 h1, realPow8_of_isCanonicalX25519 h2] at hpow

theorem realX25519_inj_pow8 (X : UnreachedPqxdhPrimitives) (a pk1 pk2 : List UInt8)
    (_ha : a.length = 32) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hx : (modelPrims X realPEParams).x25519 a pk1 =
      (modelPrims X realPEParams).x25519 a pk2) :
    realPow8 pk1 = realPow8 pk2 := by
  obtain ⟨u1, hu1_lt, hp8_1, _, hx1, hcls1⟩ := realPow8_spec_32 h1
  obtain ⟨u2, hu2_lt, hp8_2, _, hx2, hcls2⟩ := realPow8_spec_32 h2
  rw [hp8_1, hp8_2]
  set s := (CryptoGames.Ratchet.clampScalar (u8Vec 32 a)).toList
  have hxs : x25519 s (natToLeBytes 32 u1) = x25519 s (natToLeBytes 32 u2) := by
    rw [hx1, hx2]
    have hbv := congrArg ofU8 hx
    rw [modelPrims_realPE_x25519_of_len32 X a pk1 h1,
        modelPrims_realPE_x25519_of_len32 X a pk2 h2,
        ofU8_toU8, ofU8_toU8] at hbv
    exact hbv
  obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul s
  have hk_lt255 : clampScalar s < 2 ^ 255 := clampScalar_lt_two_pow_255 s
  have hv_eq : x25519Ladder (clampScalar s) u1 = x25519Ladder (clampScalar s) u2 := by
    unfold x25519 at hxs
    rw [decodeU255_natToLeBytes_of_lt_p hu1_lt, decodeU255_natToLeBytes_of_lt_p hu2_lt] at hxs
    have hl := congrArg leBytesToNat hxs
    have hv1 : x25519Ladder (clampScalar s) u1 < 256 ^ 32 :=
      lt_trans (x25519Ladder_lt_p25519 _ _) p25519_lt_256_pow_32
    have hv2 : x25519Ladder (clampScalar s) u2 < 256 ^ 32 :=
      lt_trans (x25519Ladder_lt_p25519 _ _) p25519_lt_256_pow_32
    rwa [leBytesToNat_natToLeBytes_of_lt hv1, leBytesToNat_natToLeBytes_of_lt hv2] at hl
  have hEd_smul_ne : ∀ {Q : EdPoint}, edOnCurve Q = true → Q.x ≠ 0 →
      edNatSmul edOrderL Q = edZero → (edNatSmul (8 * m) Q).x ≠ 0 := by
    intro Q hQ hQx hQL hRx0
    have h2 : edNatSmul 2 (edNatSmul (8 * m) Q) = edZero :=
      (edNatSmul_two_eq_zero_iff (edOnCurve_edNatSmul _ hQ)).mpr hRx0
    rw [← edNatSmul_mul 2 (8 * m) hQ, show 2 * (8 * m) = 16 * m by omega] at h2
    have hgcd := gcd_sixteen_mul_odd_prime edOrderL_prime edOrderL_odd hm0
      (lt_trans hm_lt two_pow_252_lt_edOrderL)
    have h1Q := edNatSmul_gcd_eq_zero hQ h2 hQL
    rw [hgcd, edNatSmul_one hQ] at h1Q
    exact hQx (congrArg EdPoint.x h1Q)
  have hTw_smul_ne : ∀ {Q : EdPoint}, twOnCurve Q = true → Q.x ≠ 0 →
      twNatSmul twistOrderL Q = twZero → (twNatSmul (8 * m) Q).x ≠ 0 := by
    intro Q hQ hQx hQL hRx0
    have h2 : twNatSmul 2 (twNatSmul (8 * m) Q) = twZero :=
      (twNatSmul_two_eq_zero_iff (twOnCurve_twNatSmul _ hQ)).mpr hRx0
    rw [← twNatSmul_mul 2 (8 * m) hQ, show 2 * (8 * m) = 16 * m by omega] at h2
    have hgcd := gcd_sixteen_mul_odd_prime twistOrderL_prime twistOrderL_odd hm0
      (lt_trans hm_lt two_pow_252_lt_twistOrderL)
    have h1Q := twNatSmul_gcd_eq_zero hQ h2 hQL
    rw [hgcd] at h1Q
    have hQ0 : Q = twZero := (twAdd_twZero hQ).symm.trans h1Q
    exact hQx (congrArg EdPoint.x hQ0)
  suffices hu_eq : u1 = u2 by rw [hu_eq]
  rcases hcls1 with rfl | ⟨Q1, hQ1, hQ1x, hQ1L, rfl⟩ | ⟨Q1, hQ1, hQ1x, hQ1L, rfl⟩ <;>
    rcases hcls2 with rfl | ⟨Q2, hQ2, hQ2x, hQ2L, rfl⟩ | ⟨Q2, hQ2, hQ2x, hQ2L, rfl⟩
  · rfl
  · exfalso
    rw [x25519Ladder_zero, x25519Ladder_edToMontU hk_lt255 hQ2, hk] at hv_eq
    exact hEd_smul_ne hQ2 hQ2x hQ2L
      ((edToMontU_eq_zero_iff (edOnCurve_edNatSmul _ hQ2)).mp hv_eq.symm)
  · exfalso
    rw [x25519Ladder_zero, x25519Ladder_twToMontU hk_lt255 hQ2, hk] at hv_eq
    exact hTw_smul_ne hQ2 hQ2x hQ2L
      ((twToMontU_eq_zero_iff (twOnCurve_twNatSmul _ hQ2)).mp hv_eq.symm)
  · exfalso
    rw [x25519Ladder_edToMontU hk_lt255 hQ1, x25519Ladder_zero, hk] at hv_eq
    exact hEd_smul_ne hQ1 hQ1x hQ1L
      ((edToMontU_eq_zero_iff (edOnCurve_edNatSmul _ hQ1)).mp hv_eq)
  · rw [x25519Ladder_edToMontU hk_lt255 hQ1, x25519Ladder_edToMontU hk_lt255 hQ2, hk] at hv_eq
    have : Fact (Nat.Prime edOrderL) := ⟨Nat.prime_def.mpr edOrderL_prime⟩
    let cEd : ZMod edOrderL := ((8 * m : Nat) : ZMod edOrderL)
    have hcEd_ne : cEd ≠ 0 := by
      dsimp only [cEd]; rw [Nat.cast_mul]
      refine mul_ne_zero ?_ ?_
      · intro h8
        have hv := congrArg ZMod.val h8
        change ((8 : ℕ) : ZMod edOrderL).val = (0 : ZMod edOrderL).val at hv
        rw [ZMod.val_natCast_of_lt eight_lt_edOrderL, ZMod.val_zero] at hv
        omega
      · intro hm
        have hv := congrArg ZMod.val hm
        rw [ZMod.val_natCast_of_lt (lt_trans hm_lt two_pow_252_lt_edOrderL), ZMod.val_zero] at hv
        omega
    let d := cEd⁻¹.val
    have hd_mod : (d * (8 * m)) % edOrderL = 1 := by
      have hmul : cEd⁻¹ * cEd = 1 := inv_mul_cancel₀ hcEd_ne
      have hv := congrArg ZMod.val hmul
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod] at hv
      have h1v : (1 : ZMod edOrderL).val = 1 := by
        change ((1 : ℕ) : ZMod edOrderL).val = 1
        exact ZMod.val_natCast_of_lt edOrderL_prime.1
      exact hv.trans h1v
    have hinv_ed : ∀ {Q : EdPoint}, edOnCurve Q = true → edNatSmul edOrderL Q = edZero →
        edNatSmul d (edNatSmul (8 * m) Q) = Q := by
      intro Q hQ hQL
      rw [← edNatSmul_mul d (8 * m) hQ, edNatSmul_mod_edOrderL hQ hQL, hd_mod, edNatSmul_one hQ]
    rcases edOnCurve_eq_or_edNeg_of_edToMontU_eq
        (edOnCurve_edNatSmul _ hQ1) (edOnCurve_edNatSmul _ hQ2)
        (hEd_smul_ne hQ1 hQ1x hQ1L) (hEd_smul_ne hQ2 hQ2x hQ2L) hv_eq with hR | hRneg
    · have hQ_eq : Q1 = Q2 := by rw [← hinv_ed hQ1 hQ1L, hR, hinv_ed hQ2 hQ2L]
      rw [hQ_eq]
    · have hQ_eq : Q1 = edNeg Q2 := by
        rw [← hinv_ed hQ1 hQ1L, hRneg, edNatSmul_edNeg_all, hinv_ed hQ2 hQ2L]
      rw [hQ_eq, edToMontU_edNeg_of_onCurve hQ2]
  · exfalso
    rw [x25519Ladder_edToMontU hk_lt255 hQ1, x25519Ladder_twToMontU hk_lt255 hQ2, hk] at hv_eq
    have hsq := edOnCurve_montRHS_isSquare (edOnCurve_edNatSmul _ hQ1) (hEd_smul_ne hQ1 hQ1x hQ1L)
    rw [hv_eq] at hsq
    exact twOnCurve_montRHS_not_isSquare (twOnCurve_twNatSmul _ hQ2)
      (hTw_smul_ne hQ2 hQ2x hQ2L) hsq
  · exfalso
    rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_zero, hk] at hv_eq
    exact hTw_smul_ne hQ1 hQ1x hQ1L
      ((twToMontU_eq_zero_iff (twOnCurve_twNatSmul _ hQ1)).mp hv_eq)
  · exfalso
    rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_edToMontU hk_lt255 hQ2, hk] at hv_eq
    have hsq := edOnCurve_montRHS_isSquare (edOnCurve_edNatSmul _ hQ2) (hEd_smul_ne hQ2 hQ2x hQ2L)
    rw [← hv_eq] at hsq
    exact twOnCurve_montRHS_not_isSquare (twOnCurve_twNatSmul _ hQ1)
      (hTw_smul_ne hQ1 hQ1x hQ1L) hsq
  · rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_twToMontU hk_lt255 hQ2, hk] at hv_eq
    have : Fact (Nat.Prime twistOrderL) := ⟨Nat.prime_def.mpr twistOrderL_prime⟩
    let cTw : ZMod twistOrderL := ((8 * m : Nat) : ZMod twistOrderL)
    have hcTw_ne : cTw ≠ 0 := by
      dsimp only [cTw]; rw [Nat.cast_mul]
      refine mul_ne_zero ?_ ?_
      · intro h8
        have hv := congrArg ZMod.val h8
        change ((8 : ℕ) : ZMod twistOrderL).val = (0 : ZMod twistOrderL).val at hv
        rw [ZMod.val_natCast_of_lt eight_lt_twistOrderL, ZMod.val_zero] at hv
        omega
      · intro hm
        have hv := congrArg ZMod.val hm
        rw [ZMod.val_natCast_of_lt (lt_trans hm_lt two_pow_252_lt_twistOrderL), ZMod.val_zero] at hv
        omega
    let d := cTw⁻¹.val
    have hd_mod : (d * (8 * m)) % twistOrderL = 1 := by
      have hmul : cTw⁻¹ * cTw = 1 := inv_mul_cancel₀ hcTw_ne
      have hv := congrArg ZMod.val hmul
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod] at hv
      have h1v : (1 : ZMod twistOrderL).val = 1 := by
        change ((1 : ℕ) : ZMod twistOrderL).val = 1
        exact ZMod.val_natCast_of_lt twistOrderL_prime.1
      exact hv.trans h1v
    have hinv_tw : ∀ {Q : EdPoint}, twOnCurve Q = true → twNatSmul twistOrderL Q = twZero →
        twNatSmul d (twNatSmul (8 * m) Q) = Q := by
      intro Q hQ hQL
      rw [← twNatSmul_mul d (8 * m) hQ, twNatSmul_mod_twistOrderL hQ hQL, hd_mod]
      exact twAdd_twZero hQ
    rcases twOnCurve_eq_or_twNeg_of_twToMontU_eq
        (twOnCurve_twNatSmul _ hQ1) (twOnCurve_twNatSmul _ hQ2)
        (hTw_smul_ne hQ1 hQ1x hQ1L) (hTw_smul_ne hQ2 hQ2x hQ2L) hv_eq with hR | hRneg
    · have hQ_eq : Q1 = Q2 := by rw [← hinv_tw hQ1 hQ1L, hR, hinv_tw hQ2 hQ2L]
      rw [hQ_eq]
    · have hQ_eq : Q1 = twNeg Q2 := by
        rw [← hinv_tw hQ1 hQ1L, hRneg, twNatSmul_twNeg d (twOnCurve_twNatSmul _ hQ2),
            hinv_tw hQ2 hQ2L]
      rw [hQ_eq, twToMontU_twNeg]

theorem realX25519_pow8_base_len (X : UnreachedPqxdhPrimitives) (p e : List UInt8)
    (_he : e.length = 32)
    (hpow : realPow8 p = realPow8 ((modelPrims X realPEParams).x25519Base e)) :
    p.length = 32 := by
  by_cases hp : p.length = 32
  · exact hp
  · exfalso
    have hp0 : realPow8 p = List.replicate 32 0 := by
      unfold realPow8; rw [beq_eq_false_iff_ne.mpr hp]; rfl
    have hcan : isCanonicalX25519 (ofU8 ((modelPrims X realPEParams).x25519Base e)) = true := by
      dsimp only [modelPrims, blockLevelPrims, realPEParams,
        CryptoVerification.SignalSession.realCrypto]
      unfold vecU8
      rw [ofU8_toU8, x25519PubFromSecretRef_toList]
      exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint
    rw [hp0, realPow8_of_isCanonicalX25519 hcan] at hpow
    dsimp only [modelPrims, blockLevelPrims, realPEParams,
      CryptoVerification.SignalSession.realCrypto] at hpow
    unfold vecU8 at hpow
    rw [x25519PubFromSecretRef_toList] at hpow
    have hbv := congrArg ofU8 hpow
    rw [ofU8_toU8] at hbv
    have hz : ofU8 (List.replicate 32 (0 : UInt8)) = natToLeBytes 32 0 := by decide
    rw [hz] at hbv
    have hdec := congrArg
      (fun l => LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 l % p25519)
      hbv.symm
    rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, Nat.zero_mod] at hdec
    exact x25519Pubkey_not_lowOrder _ (hdec ▸ (by simp [lowOrderUs] : 0 ∈ lowOrderUs))

/-- Base-point `realPow8` collision bound (`≤ 1 / 2 ^ 250` in `ℝ≥0∞`) derived directly from
`ConcreteX25519Group.x25519Dh_base_fiber_card`. -/
theorem realX25519_ec_coll_bound_ennreal (X : UnreachedPqxdhPrimitives) (targetPk : List UInt8) :
    𝒟[do
        let sk ← SignalPqxdh.sampleScalar32
        pure (realPow8 ((modelPrims X realPEParams).x25519Base sk) == realPow8 targetPk)] {true}
      ≤ 1 / (2 : ℝ≥0∞) ^ 250 := by
  have hbase_eq_dh : ∀ w : BitVec 256,
      realPow8 ((modelPrims X realPEParams).x25519Base (SignalPqxdh.word256ToBytes w)) =
        toU8 (x25519EncPt (x25519Dh.dh w x25519Dh.base)) := by
    intro w
    have hcan : isCanonicalX25519
        (ofU8 ((modelPrims X realPEParams).x25519Base (SignalPqxdh.word256ToBytes w))) = true := by
      dsimp only [modelPrims, blockLevelPrims, realPEParams,
        CryptoVerification.SignalSession.realCrypto]
      unfold vecU8
      rw [ofU8_toU8, x25519PubFromSecretRef_toList]
      exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint
    rw [realPow8_of_isCanonicalX25519 hcan]
    dsimp only [modelPrims, blockLevelPrims]
    unfold vecU8
    let kw : List.Vector (BitVec 8) 32 := ⟨keyToBytes32 w, by simp [keyToBytes32]⟩
    have hu : u8Vec 32 (SignalPqxdh.word256ToBytes w) = kw := by
      apply List.Vector.eq
      change (u8Vec 32 (SignalPqxdh.word256ToBytes w)).toList = keyToBytes32 w
      rw [u8Vec_toList_of_length (length_word256ToBytes w), ofU8_word256ToBytes]
    rw [hu, pubKey_clampScalar_toList_of_libX25519Rel x25519RealizesDh_realCrypto]
    change toU8 (x25519EncPt (x25519Dh.dh (CryptoGames.HKDF.bytesToKey32 (keyToBytes32 w))
      x25519Dh.base)) = _
    rw [CryptoVerification.E2E.bytesToKey32_keyToBytes32]
  let f : BitVec 256 → Bool := fun w =>
    toU8 (x25519EncPt (x25519Dh.dh w x25519Dh.base)) == realPow8 targetPk
  have hexpr :
      (do
        let sk ← SignalPqxdh.sampleScalar32
        pure (realPow8 ((modelPrims X realPEParams).x25519Base sk) == realPow8 targetPk)) =
      (f <$> ($ᵗ BitVec 256)) := by
    simp only [SignalPqxdh.sampleScalar32, SignalPqxdh.sampleBytes32,
      bind_pure_comp, Functor.map_map, hbase_eq_dh]
    rfl
  rw [hexpr, evalDist_map _ (measurable_of_countable f),
      Measure.map_apply (measurable_of_countable f) (MeasurableSet.singleton true)]
  have hpre : f ⁻¹' {true} = {w : BitVec 256 | f w = true} := rfl
  rw [hpre, ← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample,
      Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_of_le_mul
  have hcard : (Finset.univ.filter (fun w : BitVec 256 => f w = true)).card ≤ 64 := by
    by_cases hne : (Finset.univ.filter (fun w : BitVec 256 => f w = true)).Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      have hfw0 : f w0 = true := (Finset.mem_filter.mp hw0).2
      let Qt : X25519Pt := x25519Dh.dh w0 x25519Dh.base
      have htgt : realPow8 targetPk = toU8 (x25519EncPt Qt) := (beq_iff_eq.mp hfw0).symm
      refine le_trans (Finset.card_le_card ?_) (x25519Dh_base_fiber_card Qt)
      intro w hw
      have hfw : f w = true := (Finset.mem_filter.mp hw).2
      dsimp only [f] at hfw
      rw [htgt] at hfw
      have henc : x25519EncPt (x25519Dh.dh w x25519Dh.base) = x25519EncPt Qt := by
        have h1 := congrArg ofU8 (beq_iff_eq.mp hfw)
        rwa [ofU8_toU8, ofU8_toU8] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, x25519RealizesDh_realCrypto.1.enc_injective henc⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le 64
  calc ((Finset.univ.filter (fun w : BitVec 256 => f w = true)).card : ℝ≥0∞)
      ≤ ((64 : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard
    _ = (2 : ℝ≥0∞) ^ 6 := by norm_num
    _ = (1 / (2 : ℝ≥0∞) ^ 250) * (2 : ℝ≥0∞) ^ 256 := by
      rw [one_div, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 250 * 2 ^ 6 by rw [← pow_add],
          ENNReal.inv_mul_cancel_left (by simp) (by simp)]

theorem realX25519_ec_coll_bound (X : UnreachedPqxdhPrimitives) (targetPk : List UInt8) :
    (𝒟[do
        let sk ← SignalPqxdh.sampleScalar32
        pure (realPow8 ((modelPrims X realPEParams).x25519Base sk) == realPow8 targetPk)]
      {true}).toReal ≤ 1 / (2 : ℝ) ^ 250 := by
  have h := realX25519_ec_coll_bound_ennreal X targetPk
  have hne : (1 / (2 : ℝ≥0∞) ^ 250) ≠ ⊤ := by
    rw [one_div]; exact ENNReal.inv_ne_top.mpr (by positivity)
  have hr := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_div, ENNReal.toReal_pow] using hr

end Computational.Proofs.LibsignalCli.ConcreteX25519Pow8
