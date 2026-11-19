/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.DH.X25519Group
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.SignalPqxdh.CwfPrimitives
import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Concrete X25519 Subgroup Proofs (`ConcreteX25519Group`)

**Checked by Lean.** Proves all seven session/CKA Diffie–Hellman premises for the concrete
Curve25519 prime-order x-only subgroup (`X25519Pt`, `x25519Dh`, `x25519EncPt`, `x25519EncT`,
`x25519DecT`, `x25519Delta = 1 / 2 ^ 250`) against `realPEParams.C`:
1. `x25519Dh_commutes` (`x25519Dh.Commutes`),
2. `x25519RealizesDh_realCrypto` (`X25519RealizesDh realPEParams.C x25519Dh x25519EncPt x25519EncT`),
3. `x25519DecT_x25519EncT` (`∀ T, x25519DecT (x25519EncT T) = some T`),
4. `x25519EncT_ne_dummyKey` (`∀ T, x25519EncT T ≠ dummyKey`),
5. `x25519Dh_zero` (`∀ x, x25519Dh.dh x 0 = 0`),
6. `x25519Dh_kerUniform` (`DhKerUniform x25519Dh`),
7. `x25519Dh_base_fiber_prob_le` (`∀ Q, Pr[x25519Dh.dh x x25519Dh.base = Q] ≤ x25519Delta`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.LibsignalCli.ConcreteX25519Group

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames.CKA (DHFun clamp256 x25519Base)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey vec32)
open CryptoGames.RFC7748 (X25519Pt x25519ZeroKey x25519BaseKey isX25519SubgroupKey
  x25519BasePt x25519Dh x25519EncT x25519EncPt x25519DecT x25519Delta
  x25519 x25519Basepoint x25519Pubkey x25519Ref x25519PubFromSecretRef x25519Ladder decodeU255)
open CryptoVerification.E2E (DhKerUniform u8Vec ofU8 ofU8_word256ToBytes length_word256ToBytes
  u8Vec_clampScalar25519 fitVec)
open CryptoVerification.SignalSession (realPEParams)
open VerifiedLibraries.Common (p25519 edOrderL fpNeg fpInv recoverXEven leBytesToNat natToLeBytes
  EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul clampScalar clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (isCanonicalX25519
  clampScalar_ratchet_clampScalar clampScalarBytes_ratchet_clampScalar x25519Ref_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Ladder_mod x25519Ladder_zero x25519Ladder_edToMontU
  clampScalar_eight_mul clampScalar_lt_two_pow_255 x25519Pubkey_eq_edNatSmul
  x25519Ref_comm isCanonicalX25519_x25519 edToMontU_edNeg_of_onCurve)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  edOnCurve_x_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg edOnCurve_edAdd
  edOnCurve_edNatSmul edAdd_comm edAdd_assoc edAdd_edZero edZero_edAdd edAdd_edNeg_self
  edNeg_edZero edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_mul edNatSmul_add
  edNatSmul_edAdd edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edNatSmul_edOrderL_edBasepoint
  edNatSmul_mod_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_cons leBytesToNat_natToLeBytes_of_lt natToLeBytes_leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  edOrderL_prime edOrderL_odd two_pow_252_lt_edOrderL gcd_sixteen_mul_odd_prime)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_lt edToMontU_edNeg edToMontU_edBasepoint
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero montToEdwards_some_edToMontU
  montToEdwards_edToMontU edNatSmul_edBasepoint_eq_edZero_iff
  montToEdwards_eq_none_iff_raw montToEdwards_eq_some_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  edToMontU_eq_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  edOnCurve_eq_of_edToMontU_eq edNatSmul_gcd_eq_zero edNatSmul_two_eq_zero_iff)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 two_pow_252_lt_l25519 natOfBytesLE bytesOfNatLE bytesOfNatLE_natOfBytesLE
  clampedScalarZMod clampedScalarZMod_ne_zero natOfBytesLE_clampScalar25519_bounds
  eight_ne_zero_zmod_l25519)
open SpecTests.SignalPqxdh (cwfC cwfC_clamp cwfC_word_eq)

/-! ## 1. Numeric Facts & Irreducibility Guards -/

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide +kernel

private theorem p25519_lt_256_pow_32 : p25519 < 256 ^ 32 := by
  unfold p25519; decide +kernel

private theorem nine_lt_p25519 : 9 < p25519 := by
  unfold p25519; decide +kernel

private theorem not_ff32_lt_p25519 : ¬ (256 ^ 32 - 1 < p25519) := by
  unfold p25519; decide +kernel

private theorem edOrderL_eq_l25519 : edOrderL = l25519 := by
  unfold edOrderL l25519; decide +kernel

private theorem two_lt_l25519 : 2 < l25519 := by
  unfold l25519; decide +kernel

private theorem edBasepoint_x_even : edBasepoint.x % 2 = 0 := by
  unfold edBasepoint; decide +kernel

private theorem edBasepoint_ne_edZero : edBasepoint ≠ edZero := by
  unfold edBasepoint edZero; decide +kernel

private theorem x25519Base_eq_basepoint : x25519Basepoint = x25519Base := by
  rfl

attribute [local irreducible] VerifiedLibraries.Common.fpAdd VerifiedLibraries.Common.fpSub
  VerifiedLibraries.Common.fpMul fpNeg fpInv recoverXEven edSmul x25519Ladder

/-! ## 2. Equivalence of `isX25519SubgroupKey` with `0^32 ∨ isCanonicalX25519` -/

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

private def montLiftEdWith (recFn : Nat → Option Nat) (u p1 : Nat) (signOdd : Bool) :
    Option EdPoint :=
  if u == p1 then none
  else
    let y := VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
      (fpInv (VerifiedLibraries.Common.fpAdd u 1))
    (recFn y).map fun xEven => ⟨if signOdd then fpNeg xEven else xEven, y⟩

private theorem montLiftEdWith_of_eq (recFn : Nat → Option Nat) (u : Nat) (signOdd : Bool) :
    montLiftEdWith recFn u u signOdd = none := by
  unfold montLiftEdWith; simp

private theorem montLiftEdWith_of_ne_none (recFn : Nat → Option Nat) {u p1 : Nat} (signOdd : Bool)
    (hne : u ≠ p1)
    (hrec : recFn (VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
      (fpInv (VerifiedLibraries.Common.fpAdd u 1))) = none) :
    montLiftEdWith recFn u p1 signOdd = none := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
    (fpInv (VerifiedLibraries.Common.fpAdd u 1)))).map _ = none
  rw [hrec]; rfl

private theorem montLiftEdWith_of_ne_some (recFn : Nat → Option Nat) {u p1 xEven : Nat}
    (signOdd : Bool) (hne : u ≠ p1)
    (hrec : recFn (VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
      (fpInv (VerifiedLibraries.Common.fpAdd u 1))) = some xEven) :
    montLiftEdWith recFn u p1 signOdd =
      some ⟨if signOdd then fpNeg xEven else xEven,
        VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
          (fpInv (VerifiedLibraries.Common.fpAdd u 1))⟩ := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (VerifiedLibraries.Common.fpMul (VerifiedLibraries.Common.fpSub u 1)
    (fpInv (VerifiedLibraries.Common.fpAdd u 1)))).map _ = _
  rw [hrec]; rfl

private theorem decodeU255_eq (bs : List (BitVec 8)) :
    decodeU255 bs = leBytesToNat (bs.take 32) % (2 ^ 255) := rfl

private theorem montLiftEd_eq_liftWith (bs : List (BitVec 8)) (s : BitVec 8) :
    SignalPqxdh.montLiftEd bs s =
      montLiftEdWith recoverXEven
        ((leBytesToNat (bs.take 32) % (2 ^ 255)) % p25519) (p25519 - 1)
        ((s &&& 1#8) == 1#8) :=
  rfl

theorem montLiftEd_eq_x25519MontToEdwards (bs : List (BitVec 8)) :
    SignalPqxdh.montLiftEd bs 0#8 =
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 := by
  rw [montLiftEd_eq_liftWith, ← decodeU255_eq]
  cases hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
  | none =>
    rcases (montToEdwards_eq_none_iff_raw bs 0).mp hm with hup | ⟨hne, hrec⟩
    · rw [hup]; exact montLiftEdWith_of_eq _ _ _
    · exact montLiftEdWith_of_ne_none _ _ hne hrec
  | some P =>
    rcases (montToEdwards_eq_some_iff bs 0 P).mp hm with ⟨hne, xEven, hrec, rfl⟩
    rw [montLiftEdWith_of_ne_some _ _ hne hrec]
    rfl

theorem montLiftEd_one_eq_x25519MontToEdwards (bs : List (BitVec 8)) :
    SignalPqxdh.montLiftEd bs 1#8 =
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 1 := by
  rw [montLiftEd_eq_liftWith, ← decodeU255_eq]
  cases hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 1 with
  | none =>
    rcases (montToEdwards_eq_none_iff_raw bs 1).mp hm with hup | ⟨hne, hrec⟩
    · rw [hup]; exact montLiftEdWith_of_eq _ _ _
    · exact montLiftEdWith_of_ne_none _ _ hne hrec
  | some P =>
    rcases (montToEdwards_eq_some_iff bs 1 P).mp hm with ⟨hne, xEven, hrec, rfl⟩
    rw [montLiftEdWith_of_ne_some _ _ hne hrec]
    rfl

private theorem isX25519SubgroupKey_eq (pk : PublicKey) :
    isX25519SubgroupKey pk = (pk == x25519ZeroKey || isCanonicalX25519 pk.bytes.toList) := by
  unfold isX25519SubgroupKey isCanonicalX25519
  have hlen : pk.bytes.toList.length = 32 := pk.bytes.2
  rw [hlen, beq_self_eq_true, Bool.true_and, montLiftEd_eq_x25519MontToEdwards]
  cases LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
    pk.bytes.toList 0 <;> rfl

private theorem isX25519SubgroupKey_iff (pk : PublicKey) :
    isX25519SubgroupKey pk = true ↔
      pk = x25519ZeroKey ∨ isCanonicalX25519 pk.bytes.toList = true := by
  have h := isX25519SubgroupKey_eq pk
  have hbeq : (pk == x25519ZeroKey) = true ↔ pk = x25519ZeroKey := beq_iff_eq
  rw [h, Bool.or_eq_true, hbeq]

theorem isCanonicalX25519_basepoint : isCanonicalX25519 x25519Basepoint = true := by
  unfold isCanonicalX25519 x25519Basepoint
  have h9_256 : 9 < 256 ^ 32 := by decide
  rw [natToLeBytes_len, leBytesToNat_natToLeBytes_of_lt h9_256]
  have hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 9) 0 = some edBasepoint := by
    rw [← edToMontU_edBasepoint]
    have h := montToEdwards_edToMontU edOnCurve_edBasepoint edBasepoint_ne_edZero
    rwa [edBasepoint_x_even] at h
  rw [hm]
  have hord : (edSmul edOrderL edBasepoint == edZero) = true := by
    rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint,
        edNatSmul_edOrderL_edBasepoint]
    rfl
  simp [nine_lt_p25519, hord]

theorem isX25519SubgroupKey_baseKey : isX25519SubgroupKey x25519BaseKey = true :=
  (isX25519SubgroupKey_iff _).mpr (Or.inr isCanonicalX25519_basepoint)

private theorem dite_x25519Pt_val_pos {p : Prop} [Decidable p] (f : p → X25519Pt)
    (g : ¬p → X25519Pt) (hp : p) : (dite p f g).val = (f hp).val := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hp hn

theorem x25519BasePt_val : x25519BasePt.val = x25519BaseKey :=
  dite_x25519Pt_val_pos (fun h => ⟨x25519BaseKey, h⟩) (fun _ => (0 : X25519Pt))
    isX25519SubgroupKey_baseKey

private theorem leBytesToNat_replicate_zero : ∀ n, leBytesToNat (List.replicate n 0#8) = 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, leBytesToNat_cons, leBytesToNat_replicate_zero n]
    rfl

private theorem decodeU255_replicate_zero : decodeU255 (List.replicate 32 0#8) = 0 := by
  unfold decodeU255
  rw [List.take_of_length_le (by simp), leBytesToNat_replicate_zero]
  rfl

private theorem natToLeBytes_zero : ∀ n, natToLeBytes n 0 = List.replicate n 0#8
  | 0 => rfl
  | n + 1 => by
    simp [natToLeBytes, List.replicate_succ]

private theorem x25519_zero_bytes (s : List (BitVec 8)) :
    x25519 s (List.replicate 32 0#8) = List.replicate 32 0#8 := by
  unfold x25519
  rw [decodeU255_replicate_zero, x25519Ladder_zero, natToLeBytes_zero]

private theorem x25519Ref_zero (s : List.Vector (BitVec 8) 32) :
    x25519Ref s x25519ZeroKey.bytes = x25519ZeroKey.bytes := by
  apply List.Vector.eq
  change x25519 s.toList (List.replicate 32 0#8) = List.replicate 32 0#8
  exact x25519_zero_bytes s.toList

theorem isX25519SubgroupKey_x25519Ref (k : BitVec 256) (Q : X25519Pt) :
    isX25519SubgroupKey ⟨x25519Ref (vec32 (keyToBytes32 k)) Q.val.bytes⟩ = true := by
  rw [isX25519SubgroupKey_iff]
  rcases (isX25519SubgroupKey_iff Q.val).mp Q.property with h0 | hcan
  · left
    rw [h0, x25519Ref_zero]
  · right
    exact isCanonicalX25519_x25519 (a := (vec32 (keyToBytes32 k)).toList) hcan

theorem x25519Dh_dh_val (k : BitVec 256) (Q : X25519Pt) :
    (x25519Dh.dh k Q).val = ⟨x25519Ref (vec32 (keyToBytes32 k)) Q.val.bytes⟩ :=
  let pk : PublicKey := ⟨x25519Ref (vec32 (keyToBytes32 k)) Q.val.bytes⟩
  dite_x25519Pt_val_pos (fun h' => ⟨pk, h'⟩) (fun _ => (0 : X25519Pt))
    (isX25519SubgroupKey_x25519Ref k Q)

attribute [local irreducible] isX25519SubgroupKey x25519BasePt

private theorem gcd_two_edOrderL : Nat.gcd 2 edOrderL = 1 := by
  have hodd := edOrderL_odd
  have hle : Nat.gcd 2 edOrderL ≤ 2 := Nat.gcd_le_left edOrderL (by decide)
  have hdvdL : Nat.gcd 2 edOrderL ∣ edOrderL := Nat.gcd_dvd_right 2 edOrderL
  have hpos : 0 < Nat.gcd 2 edOrderL := Nat.gcd_pos_of_pos_left edOrderL (by decide)
  have hne2 : Nat.gcd 2 edOrderL ≠ 2 := fun h2 => by rw [h2] at hdvdL; omega
  omega

private theorem edOnCurve_x_ne_zero_of_prime_order {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hord : edNatSmul edOrderL P = edZero) :
    P.x ≠ 0 := by
  intro hx0
  have hP2 : edNatSmul 2 P = edZero := (edNatSmul_two_eq_zero_iff hP).mpr hx0
  have h1 := edNatSmul_gcd_eq_zero hP hP2 hord
  rw [gcd_two_edOrderL, edNatSmul_one hP] at h1
  exact hne h1

private theorem match_edPoint_eq_true (m : Option EdPoint) (f : EdPoint → Bool)
    (h : (match m with | none => false | some Q => f Q) = true) :
    ∃ P, m = some P ∧ f P = true := by
  cases m with
  | none => cases h
  | some P => exact ⟨P, rfl, h⟩

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
    have h1 : ((bs.length == 32 && decide (leBytesToNat bs < p25519)) &&
        match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
        | none => false | some P => edSmul edOrderL P == edZero) = true := h
    obtain ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨hlen, hlt⟩ := (Bool.and_eq_true _ _).mp hhead
    obtain ⟨P, hm, heq⟩ := match_edPoint_eq_true _ (fun P => edSmul edOrderL P == edZero) htail
    exact ⟨beq_iff_eq.mp hlen, of_decide_eq_true hlt, P, hm, beq_iff_eq.mp heq⟩
  · rintro ⟨hlen, hlt, P, hm, heq⟩
    have hhead : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = true :=
      (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen, decide_eq_true hlt⟩
    have htail : (match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
        | none => false | some P => edSmul edOrderL P == edZero) = true :=
      match_edPoint_of_some _ P (fun P => edSmul edOrderL P == edZero) hm (beq_iff_eq.mpr heq)
    exact (Bool.and_eq_true _ _).mpr ⟨hhead, htail⟩

private theorem isCanonicalX25519_zero_false :
    isCanonicalX25519 x25519ZeroKey.bytes.toList = false := by
  by_contra h
  have htrue : isCanonicalX25519 x25519ZeroKey.bytes.toList = true := by
    cases hb : isCanonicalX25519 x25519ZeroKey.bytes.toList with
    | true => rfl
    | false => exact absurd hb h
  have h0 : x25519ZeroKey.bytes.toList = List.replicate 32 0#8 := by
    simp [x25519ZeroKey]
  rw [h0] at htrue
  obtain ⟨_, _, P, hm, hmont⟩ := (isCanonicalX25519_eq_true_iff _).mp htrue
  have hP_on := montToEdwards_some_onCurve hm
  have hP_ne := montToEdwards_some_ne_edZero hm
  have huP := montToEdwards_some_edToMontU hm
  rw [decodeU255_replicate_zero] at huP
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont
  have hPx0 : P.x = 0 := (edToMontU_eq_zero_iff hP_on).mp (by simpa using huP)
  exact edOnCurve_x_ne_zero_of_prime_order hP_on hP_ne hP_ord hPx0

/-! ## 3. Session Group Premises (`_hdec`, `_hdum`, `_hz`, `_hDh`, `_hX`) -/

theorem x25519DecT_x25519EncT (Q : X25519Pt) :
    x25519DecT (x25519EncT Q) = some Q := by
  unfold x25519DecT x25519EncT
  split
  · rfl
  · next hn => exact absurd Q.property hn

private theorem leBytesToNat_replicate_ff : ∀ n, leBytesToNat (List.replicate n 0xff#8) = 256 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, leBytesToNat_cons, leBytesToNat_replicate_ff n]
    have hpos : 1 ≤ 256 ^ n := Nat.one_le_pow n 256 (by decide)
    have hff : (0xff#8).toNat = 255 := rfl
    rw [hff, Nat.pow_succ]
    omega

theorem x25519EncT_ne_dummyKey (Q : X25519Pt) :
    x25519EncT Q ≠ dummyKey := by
  intro h
  have hprop : isX25519SubgroupKey dummyKey = true := h ▸ Q.property
  rw [isX25519SubgroupKey_iff] at hprop
  rcases hprop with h0 | hcan
  · have hb := congrArg (fun k : PublicKey => k.bytes.toList.head?) h0
    simp [dummyKey, x25519ZeroKey] at hb
  · unfold isCanonicalX25519 at hcan
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcan
    have hlt := hcan.1.2
    have hff : dummyKey.bytes.toList = List.replicate 32 0xff#8 := by simp [dummyKey]
    rw [hff, leBytesToNat_replicate_ff] at hlt
    exact not_ff32_lt_p25519 hlt

theorem x25519Dh_zero (k : BitVec 256) :
    x25519Dh.dh k 0 = 0 := by
  apply Subtype.ext
  rw [x25519Dh_dh_val]
  change (⟨x25519Ref (vec32 (keyToBytes32 k)) x25519ZeroKey.bytes⟩ : PublicKey) = x25519ZeroKey
  rw [x25519Ref_zero]

private theorem x25519Ref_baseKey (v : List.Vector (BitVec 8) 32) :
    x25519Ref v x25519BaseKey.bytes = x25519PubFromSecretRef v := by
  apply Subtype.ext
  rfl

theorem x25519Dh_commutes : x25519Dh.Commutes := by
  intro a b
  apply Subtype.ext
  change (x25519Dh.dh a (x25519Dh.dh b x25519BasePt)).val =
    (x25519Dh.dh b (x25519Dh.dh a x25519BasePt)).val
  rw [x25519Dh_dh_val, x25519Dh_dh_val, x25519Dh_dh_val, x25519Dh_dh_val, x25519BasePt_val]
  apply congrArg PublicKey.mk
  rw [x25519Ref_baseKey, x25519Ref_baseKey]
  exact x25519Ref_comm (vec32 (keyToBytes32 a)) (vec32 (keyToBytes32 b))

private theorem vec32_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    (vec32 bs).toList = bs := by
  simp [vec32, h]

private theorem vec32_toList_eq (v : List.Vector (BitVec 8) 32) :
    vec32 v.toList = v := by
  apply List.Vector.eq
  exact vec32_of_length_32 v.2

private theorem length_keyToBytes32_eq (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem clamp256_clampScalar_eq (k : BitVec 256) :
    clampScalar (keyToBytes32 (clamp256 k)) = clampScalar (keyToBytes32 k) := by
  have h1 : vec32 (keyToBytes32 (clamp256 k)) =
      CryptoGames.Ratchet.clampScalar (vec32 (keyToBytes32 k)) :=
    (CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_keyVec k).symm
  have h2 := clampScalar_ratchet_clampScalar (vec32 (keyToBytes32 k))
  rw [← h1] at h2
  simpa [vec32_of_length_32 (length_keyToBytes32_eq _)] using h2

theorem x25519RealizesDh_realCrypto :
    X25519RealizesDh realPEParams.C x25519Dh x25519EncPt x25519EncT := by
  refine ⟨?_, fun Q => by simp [x25519EncT, x25519EncPt, vec32_toList_eq]⟩
  refine
    { enc_injective := fun Q₁ Q₂ h => by
        cases Q₁ with
        | mk pk₁ _ =>
          cases Q₂ with
          | mk pk₂ _ =>
            cases pk₁ with
            | mk v₁ =>
              cases pk₂ with
              | mk v₂ =>
                exact Subtype.ext (congrArg PublicKey.mk (Subtype.ext h))
      enc_length := fun Q => Q.val.bytes.2
      enc_zero := rfl
      enc_base := by
        dsimp only [x25519EncPt]
        have hb : x25519Dh.base = x25519BasePt := rfl
        rw [hb, x25519BasePt_val]
        exact x25519Base_eq_basepoint
      base_ne_zero := by
        intro h
        have hv : x25519Dh.base.val.bytes.toList.head? = (0 : X25519Pt).val.bytes.toList.head? :=
          congrArg (fun Q : X25519Pt => Q.val.bytes.toList.head?) h
        have hb : x25519Dh.base = x25519BasePt := rfl
        have h0 : (0 : X25519Pt).val = x25519ZeroKey := rfl
        rw [hb, x25519BasePt_val, h0] at hv
        have h9 : x25519BaseKey.bytes.toList = x25519Base := x25519Base_eq_basepoint
        rw [h9] at hv
        have hne : x25519Base.head? ≠ x25519ZeroKey.bytes.toList.head? := by decide
        exact hne hv
      hook := fun x Q => by
        dsimp only [x25519EncPt]
        rw [x25519Dh_dh_val, vec32_toList_eq]
        rfl
      pubKey_hook := fun x => by
        dsimp only [x25519EncPt]
        have hb : x25519Dh.base = x25519BasePt := rfl
        rw [hb, x25519Dh_dh_val, x25519BasePt_val, x25519Ref_baseKey]
        rfl
      dh_clamp := fun x Q => by
        apply Subtype.ext
        rw [x25519Dh_dh_val, x25519Dh_dh_val]
        apply congrArg PublicKey.mk
        apply List.Vector.eq
        rw [x25519Ref_toList, x25519Ref_toList]
        unfold x25519
        rw [vec32_of_length_32 (length_keyToBytes32_eq (clamp256 x)),
            vec32_of_length_32 (length_keyToBytes32_eq x),
            clamp256_clampScalar_eq x]
      dh_ne_zero := fun x Q hQ => by
        have hcan : isCanonicalX25519 Q.val.bytes.toList = true := by
          rcases (isX25519SubgroupKey_iff Q.val).mp Q.property with h0 | hc
          · exact absurd (Subtype.ext h0) hQ
          · exact hc
        intro h0
        have hval := congrArg Subtype.val h0
        rw [x25519Dh_dh_val] at hval
        have hcan' : isCanonicalX25519
            (x25519Ref (vec32 (keyToBytes32 x)) Q.val.bytes).toList = true := by
          rw [x25519Ref_toList]
          exact isCanonicalX25519_x25519 (a := (vec32 (keyToBytes32 x)).toList) hcan
        change (⟨x25519Ref (vec32 (keyToBytes32 x)) Q.val.bytes⟩ : PublicKey) = x25519ZeroKey at hval
        have hbytes : (x25519Ref (vec32 (keyToBytes32 x)) Q.val.bytes).toList =
            x25519ZeroKey.bytes.toList := congrArg (fun pk : PublicKey => pk.bytes.toList) hval
        rw [hbytes, isCanonicalX25519_zero_false] at hcan'
        cases hcan' }

/-! ## 4. Injectivity & `DhKerUniform x25519Dh` -/

private theorem edOnCurve_eq_or_edNeg_of_edToMontU_eq {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : edToMontU P = edToMontU Q) :
    P = Q ∨ P = edNeg Q := by
  by_cases hpar : P.x % 2 = Q.x % 2
  · exact Or.inl (edOnCurve_eq_of_edToMontU_eq hP hQ hPx hQx hu hpar)
  · right
    have hQ_lt : Q.x < p25519 := edOnCurve_x_lt hQ
    have hQ_mod_ne : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQ_lt]; omega
    have hNegQx : (edNeg Q).x ≠ 0 := by
      dsimp only [edNeg]
      unfold fpNeg
      rw [Nat.mod_eq_of_lt hQ_lt, Nat.mod_eq_of_lt (by omega)]
      omega
    have hNegPar : P.x % 2 = (edNeg Q).x % 2 := by
      dsimp only [edNeg]
      rw [fpNeg_mod_two_of_ne_zero hQ_mod_ne, Nat.mod_eq_of_lt hQ_lt]
      rcases Nat.mod_two_eq_zero_or_one P.x with h0 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one Q.x with q0 | q1 <;> omega
    exact edOnCurve_eq_of_edToMontU_eq hP (edOnCurve_edNeg hQ) hPx hNegQx
      (hu.trans (edToMontU_edNeg Q).symm) hNegPar

private theorem edNatSmul_edNeg_eq (n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero => simp [edNatSmul, VerifiedLibraries.Common.edNeg, VerifiedLibraries.Common.edZero]
  | succ k ih =>
    have h_on := edOnCurve_edNatSmul k hP
    have h_neg := edOnCurve_edNeg hP
    have h_kneg := edOnCurve_edNeg h_on
    have hsum : edAdd (edAdd P (edNatSmul k P)) (edAdd (edNeg P) (edNeg (edNatSmul k P))) = edZero := by
      rw [edAdd_assoc hP h_on (edOnCurve_edAdd h_neg h_kneg),
          ← edAdd_assoc h_on h_neg h_kneg,
          edAdd_comm (edNatSmul k P) (edNeg P),
          edAdd_assoc h_neg h_on h_kneg,
          edAdd_edNeg_self h_on, edAdd_edZero h_neg, edAdd_edNeg_self hP]
    have hstep : edAdd (edNeg P) (edNeg (edNatSmul k P)) = edNeg (edAdd P (edNatSmul k P)) := by
      have h1 := congrArg (edAdd (edNeg (edAdd P (edNatSmul k P)))) hsum
      have hPQ := edOnCurve_edAdd hP h_on
      have hR := edOnCurve_edAdd h_neg h_kneg
      rw [← edAdd_assoc (edOnCurve_edNeg hPQ) hPQ hR,
          edAdd_comm (edNeg (edAdd P (edNatSmul k P))) (edAdd P (edNatSmul k P)),
          edAdd_edNeg_self hPQ, edZero_edAdd hR, edAdd_edZero (edOnCurve_edNeg hPQ)] at h1
      exact h1
    simpa [edNatSmul, ih] using hstep

theorem x25519Dh_inj (k : BitVec 256) : Function.Injective (x25519Dh.dh k) := by
  intro Q₁ Q₂ heq
  by_cases h1 : Q₁ = 0
  · subst h1
    by_cases h2 : Q₂ = 0
    · exact h2.symm
    · rw [x25519Dh_zero] at heq
      exact absurd heq.symm (x25519RealizesDh_realCrypto.1.dh_ne_zero k Q₂ h2)
  · by_cases h2 : Q₂ = 0
    · subst h2
      rw [x25519Dh_zero] at heq
      exact absurd heq (x25519RealizesDh_realCrypto.1.dh_ne_zero k Q₁ h1)
    · have hc1 : isCanonicalX25519 Q₁.val.bytes.toList = true :=
        ((isX25519SubgroupKey_iff Q₁.val).mp Q₁.property).resolve_left (fun h => h1 (Subtype.ext h))
      have hc2 : isCanonicalX25519 Q₂.val.bytes.toList = true :=
        ((isX25519SubgroupKey_iff Q₂.val).mp Q₂.property).resolve_left (fun h => h2 (Subtype.ext h))
      rcases (isCanonicalX25519_eq_true_iff _).mp hc1 with ⟨hlen1, hlt1, P₁, hlift1, hm1⟩
      rcases (isCanonicalX25519_eq_true_iff _).mp hc2 with ⟨hlen2, hlt2, P₂, hlift2, hm2⟩
      have hP1_on := montToEdwards_some_onCurve hlift1
      have hP2_on := montToEdwards_some_onCurve hlift2
      have hP1_ne := montToEdwards_some_ne_edZero hlift1
      have hP2_ne := montToEdwards_some_ne_edZero hlift2
      have hP1_ord : edNatSmul edOrderL P₁ = edZero :=
        (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP1_on).symm.trans hm1
      have hP2_ord : edNatSmul edOrderL P₂ = edZero :=
        (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP2_on).symm.trans hm2
      have hu1 : edToMontU P₁ = leBytesToNat Q₁.val.bytes.toList := by
        have h := montToEdwards_some_edToMontU hlift1
        unfold decodeU255 at h
        rw [List.take_of_length_le (Nat.le_of_eq hlen1),
            Nat.mod_eq_of_lt (lt_trans hlt1 p25519_lt_two_pow_255),
            Nat.mod_eq_of_lt hlt1] at h
        exact h
      have hu2 : edToMontU P₂ = leBytesToNat Q₂.val.bytes.toList := by
        have h := montToEdwards_some_edToMontU hlift2
        unfold decodeU255 at h
        rw [List.take_of_length_le (Nat.le_of_eq hlen2),
            Nat.mod_eq_of_lt (lt_trans hlt2 p25519_lt_two_pow_255),
            Nat.mod_eq_of_lt hlt2] at h
        exact h
      have hbytes : x25519 (keyToBytes32 k) Q₁.val.bytes.toList =
          x25519 (keyToBytes32 k) Q₂.val.bytes.toList := by
        have hv := congrArg (fun Q : X25519Pt => Q.val.bytes.toList) heq
        rw [x25519Dh_dh_val, x25519Dh_dh_val] at hv
        simpa [x25519Ref_toList, vec32_of_length_32 (length_keyToBytes32_eq k)] using hv
      set s := clampScalar (keyToBytes32 k)
      have hxs1 : x25519 (keyToBytes32 k) Q₁.val.bytes.toList =
          natToLeBytes 32 (edToMontU (edNatSmul s P₁)) := by
        unfold x25519
        rw [← x25519Ladder_mod, ← montToEdwards_some_edToMontU hlift1,
            x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 _) hP1_on]
      have hxs2 : x25519 (keyToBytes32 k) Q₂.val.bytes.toList =
          natToLeBytes 32 (edToMontU (edNatSmul s P₂)) := by
        unfold x25519
        rw [← x25519Ladder_mod, ← montToEdwards_some_edToMontU hlift2,
            x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 _) hP2_on]
      rw [hxs1, hxs2] at hbytes
      have hu_s : edToMontU (edNatSmul s P₁) = edToMontU (edNatSmul s P₂) := by
        have h := congrArg leBytesToNat hbytes
        rwa [leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32),
             leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32)] at h
      obtain ⟨m, hs_eq, hm0, hm_lt⟩ := clampScalar_eight_mul (keyToBytes32 k)
      have hgcd := gcd_sixteen_mul_odd_prime edOrderL_prime edOrderL_odd hm0
        (Nat.lt_trans hm_lt two_pow_252_lt_edOrderL)
      have hkill : ∀ D : EdPoint, edOnCurve D = true → edNatSmul edOrderL D = edZero →
          edNatSmul s D = edZero → D = edZero := fun D hDon hDL hDs => by
        have h16 : edNatSmul (16 * m) D = edZero := by
          rw [show 16 * m = 2 * s by omega, edNatSmul_mul 2 s hDon, hDs, edNatSmul_edZero]
        have h1 := edNatSmul_gcd_eq_zero hDon h16 hDL
        rwa [hgcd, edNatSmul_one hDon] at h1
      have hsP1_ord : edNatSmul edOrderL (edNatSmul s P₁) = edZero := by
        rw [← edNatSmul_mul edOrderL s hP1_on, Nat.mul_comm edOrderL s,
            edNatSmul_mul s edOrderL hP1_on, hP1_ord, edNatSmul_edZero]
      have hsP2_ord : edNatSmul edOrderL (edNatSmul s P₂) = edZero := by
        rw [← edNatSmul_mul edOrderL s hP2_on, Nat.mul_comm edOrderL s,
            edNatSmul_mul s edOrderL hP2_on, hP2_ord, edNatSmul_edZero]
      have hsP1_ne : edNatSmul s P₁ ≠ edZero := fun h0 => hP1_ne (hkill P₁ hP1_on hP1_ord h0)
      have hsP2_ne : edNatSmul s P₂ ≠ edZero := fun h0 => hP2_ne (hkill P₂ hP2_on hP2_ord h0)
      have hpm := edOnCurve_eq_or_edNeg_of_edToMontU_eq
        (edOnCurve_edNatSmul s hP1_on) (edOnCurve_edNatSmul s hP2_on)
        (edOnCurve_x_ne_zero_of_prime_order (edOnCurve_edNatSmul s hP1_on) hsP1_ne hsP1_ord)
        (edOnCurve_x_ne_zero_of_prime_order (edOnCurve_edNatSmul s hP2_on) hsP2_ne hsP2_ord)
        hu_s
      have hP_pm : P₁ = P₂ ∨ P₁ = edNeg P₂ := by
        rcases hpm with hpos | hneg
        · left
          let D := edAdd P₁ (edNeg P₂)
          have hDon := edOnCurve_edAdd hP1_on (edOnCurve_edNeg hP2_on)
          have hDL : edNatSmul edOrderL D = edZero := by
            rw [edNatSmul_edAdd edOrderL hP1_on (edOnCurve_edNeg hP2_on),
                hP1_ord, edNatSmul_edNeg_eq edOrderL hP2_on, hP2_ord,
                edNeg_edZero, edAdd_edZero edOnCurve_edZero]
          have hDs : edNatSmul s D = edZero := by
            rw [edNatSmul_edAdd s hP1_on (edOnCurve_edNeg hP2_on),
                edNatSmul_edNeg_eq s hP2_on, hpos,
                edAdd_edNeg_self (edOnCurve_edNatSmul s hP2_on)]
          have hD0 := hkill D hDon hDL hDs
          have hadd := congrArg (fun X => edAdd X P₂) hD0
          rw [edAdd_assoc hP1_on (edOnCurve_edNeg hP2_on) hP2_on,
              edAdd_comm (edNeg P₂) P₂, edAdd_edNeg_self hP2_on,
              edAdd_edZero hP1_on, edZero_edAdd hP2_on] at hadd
          exact hadd
        · right
          let D := edAdd P₁ P₂
          have hDon := edOnCurve_edAdd hP1_on hP2_on
          have hDL : edNatSmul edOrderL D = edZero := by
            rw [edNatSmul_edAdd edOrderL hP1_on hP2_on, hP1_ord, hP2_ord,
                edAdd_edZero edOnCurve_edZero]
          have hDs : edNatSmul s D = edZero := by
            rw [edNatSmul_edAdd s hP1_on hP2_on, hneg,
                edAdd_comm (edNeg (edNatSmul s P₂)) (edNatSmul s P₂),
                edAdd_edNeg_self (edOnCurve_edNatSmul s hP2_on)]
          have hD0 := hkill D hDon hDL hDs
          have hadd := congrArg (fun X => edAdd X (edNeg P₂)) hD0
          rw [edAdd_assoc hP1_on hP2_on (edOnCurve_edNeg hP2_on),
              edAdd_edNeg_self hP2_on, edAdd_edZero hP1_on,
              edZero_edAdd (edOnCurve_edNeg hP2_on)] at hadd
          exact hadd
      have hu_eq : leBytesToNat Q₁.val.bytes.toList = leBytesToNat Q₂.val.bytes.toList := by
        rw [← hu1, ← hu2]
        rcases hP_pm with rfl | rfl
        · rfl
        · exact edToMontU_edNeg_of_onCurve hP2_on
      have hbl : Q₁.val.bytes.toList = Q₂.val.bytes.toList := by
        have h1' := natToLeBytes_leBytesToNat Q₁.val.bytes.toList
        have h2' := natToLeBytes_leBytesToNat Q₂.val.bytes.toList
        rw [hlen1] at h1'
        rw [hlen2] at h2'
        rw [← h1', hu_eq, h2']
      cases Q₁ with
      | mk pk₁ _ =>
        cases Q₂ with
        | mk pk₂ _ =>
          cases pk₁ with
          | mk v₁ =>
            cases pk₂ with
            | mk v₂ =>
              exact Subtype.ext (congrArg PublicKey.mk (Subtype.ext hbl))

theorem x25519Dh_kerUniform : DhKerUniform x25519Dh := by
  intro s x Q Q'
  rw [(x25519Dh_inj x).eq_iff, (x25519Dh_inj s).eq_iff]

/-! ## 5. Tight Base-Point Fiber Bound (`x25519Delta = 1 / 2 ^ 250`) -/

private theorem leBytesToNat_ofU8 (bs : List UInt8) :
    leBytesToNat (ofU8 bs) = natOfBytesLE bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hcons : ofU8 (b :: rest) = b.toBitVec :: ofU8 rest := rfl
    have hb : b.toBitVec.toNat = b.toNat := rfl
    rw [hcons, leBytesToNat_cons, natOfBytesLE, ih, hb]
    omega

private theorem ratchet_clampScalar_toList_eq_clampScalarBytes (v : List.Vector (BitVec 8) 32) :
    (CryptoGames.Ratchet.clampScalar v).toList = clampScalarBytes v.toList := by
  rcases v with ⟨bs, hbs⟩
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hbs; done)
  rfl

private theorem clampScalar_keyToBytes32_mod_edOrderL (k : BitVec 256) :
    clampScalar (keyToBytes32 k) % edOrderL =
      (clampedScalarZMod (SignalPqxdh.word256ToBytes k)).val := by
  let kv : List.Vector (BitVec 8) 32 := ⟨keyToBytes32 k, length_keyToBytes32_eq k⟩
  have hu : u8Vec 32 (SignalPqxdh.word256ToBytes k) = kv := by
    apply List.Vector.eq
    change (u8Vec 32 (SignalPqxdh.word256ToBytes k)).toList = keyToBytes32 k
    rw [u8Vec_toList_of_length (length_word256ToBytes k), ofU8_word256ToBytes]
  have hcl := clampScalar_ratchet_clampScalar kv
  change clampScalar kv.toList % edOrderL = _
  rw [← hcl, ← hu]
  have hlist : (CryptoGames.Ratchet.clampScalar (u8Vec 32 (SignalPqxdh.word256ToBytes k))).toList =
      ofU8 (SignalPqxdh.clampScalar25519 (SignalPqxdh.word256ToBytes k)) := by
    rw [← u8Vec_clampScalar25519,
        u8Vec_toList_of_length (SignalPqxdh.clampScalar25519_length _)]
  have hbytes_idem : clampScalarBytes (ofU8 (SignalPqxdh.clampScalar25519 (SignalPqxdh.word256ToBytes k))) =
      ofU8 (SignalPqxdh.clampScalar25519 (SignalPqxdh.word256ToBytes k)) := by
    rw [← hlist, clampScalarBytes_ratchet_clampScalar, ← ratchet_clampScalar_toList_eq_clampScalarBytes]
  rw [hlist]
  unfold clampScalar
  have hlen : (ofU8 (SignalPqxdh.clampScalar25519 (SignalPqxdh.word256ToBytes k))).length = 32 := by
    simp [ofU8]
  rw [List.take_of_length_le (Nat.le_of_eq hlen),
      hbytes_idem, leBytesToNat_ofU8, edOrderL_eq_l25519]
  unfold clampedScalarZMod Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.decodeScalarBytes
  exact (ZMod.val_natCast l25519 _).symm

private theorem clampScalar25519_eq_of_clampedScalarZMod_eq {sk1 sk2 : SignalPqxdh.Bytes}
    (h : clampedScalarZMod sk1 = clampedScalarZMod sk2) :
    SignalPqxdh.clampScalar25519 sk1 = SignalPqxdh.clampScalar25519 sk2 := by
  obtain ⟨k1, hk1_eq, _, hk1_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk1
  obtain ⟨k2, hk2_eq, _, hk2_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk2
  unfold clampedScalarZMod Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.decodeScalarBytes at h
  rw [hk1_eq, hk2_eq, Nat.cast_mul, Nat.cast_mul,
    show ((8 : ℕ) : ZMod l25519) = (8 : ZMod l25519) from rfl] at h
  have hk_cast : (k1 : ZMod l25519) = (k2 : ZMod l25519) :=
    mul_left_cancel₀ eight_ne_zero_zmod_l25519 h
  have hk_eq : k1 = k2 := by
    have hv := congrArg ZMod.val hk_cast
    rwa [ZMod.val_natCast_of_lt (lt_trans hk1_hi two_pow_252_lt_l25519),
      ZMod.val_natCast_of_lt (lt_trans hk2_hi two_pow_252_lt_l25519)] at hv
  have hl1 : (SignalPqxdh.clampScalar25519 sk1).length = 32 := SignalPqxdh.clampScalar25519_length sk1
  have hl2 : (SignalPqxdh.clampScalar25519 sk2).length = 32 := SignalPqxdh.clampScalar25519_length sk2
  calc SignalPqxdh.clampScalar25519 sk1
      = bytesOfNatLE 32 (natOfBytesLE (SignalPqxdh.clampScalar25519 sk1)) := by
          conv_lhs => rw [← bytesOfNatLE_natOfBytesLE (SignalPqxdh.clampScalar25519 sk1), hl1]
    _ = bytesOfNatLE 32 (natOfBytesLE (SignalPqxdh.clampScalar25519 sk2)) := by
          rw [hk1_eq, hk2_eq, hk_eq]
    _ = SignalPqxdh.clampScalar25519 sk2 := by
          conv_rhs => rw [← bytesOfNatLE_natOfBytesLE (SignalPqxdh.clampScalar25519 sk2), hl2]

private theorem zmod_pm_of_edToMontU_edBasepoint_eq {a b : ZMod l25519}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : edToMontU (edNatSmul a.val edBasepoint) = edToMontU (edNatSmul b.val edBasepoint)) :
    a = b ∨ a = -b := by
  have ha_on := edOnCurve_edNatSmul a.val edOnCurve_edBasepoint
  have hb_on := edOnCurve_edNatSmul b.val edOnCurve_edBasepoint
  have ha_ord : edNatSmul edOrderL (edNatSmul a.val edBasepoint) = edZero := by
    rw [← edNatSmul_mul edOrderL a.val edOnCurve_edBasepoint, Nat.mul_comm,
        edNatSmul_mul a.val edOrderL edOnCurve_edBasepoint,
        edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
  have hb_ord : edNatSmul edOrderL (edNatSmul b.val edBasepoint) = edZero := by
    rw [← edNatSmul_mul edOrderL b.val edOnCurve_edBasepoint, Nat.mul_comm,
        edNatSmul_mul b.val edOrderL edOnCurve_edBasepoint,
        edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
  have ha_ne : edNatSmul a.val edBasepoint ≠ edZero := by
    intro h0
    have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff a.val).mp h0
    rw [edOrderL_eq_l25519] at hdvd
    have hval0 : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd a.val_lt
    exact ha (ZMod.val_injective l25519 (by simpa using hval0))
  have hb_ne : edNatSmul b.val edBasepoint ≠ edZero := by
    intro h0
    have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff b.val).mp h0
    rw [edOrderL_eq_l25519] at hdvd
    have hval0 : b.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd b.val_lt
    exact hb (ZMod.val_injective l25519 (by simpa using hval0))
  have hpm := edOnCurve_eq_or_edNeg_of_edToMontU_eq ha_on hb_on
    (edOnCurve_x_ne_zero_of_prime_order ha_on ha_ne ha_ord)
    (edOnCurve_x_ne_zero_of_prime_order hb_on hb_ne hb_ord) hu
  rcases hpm with hpos | hneg
  · left
    have hsub : edNatSmul (if b.val ≤ a.val then a.val - b.val else b.val - a.val) edBasepoint = edZero := by
      split
      · next hle =>
        have hadd : edAdd (edNatSmul (a.val - b.val) edBasepoint) (edNatSmul b.val edBasepoint) =
            edNatSmul b.val edBasepoint := by
          rw [← edNatSmul_add (a.val - b.val) b.val edOnCurve_edBasepoint,
              Nat.sub_add_cancel hle, hpos]
        have hs := congrArg (fun X => edAdd X (edNeg (edNatSmul b.val edBasepoint))) hadd
        rw [edAdd_assoc (edOnCurve_edNatSmul _ edOnCurve_edBasepoint) hb_on (edOnCurve_edNeg hb_on),
            edAdd_edNeg_self hb_on, edAdd_edZero (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)] at hs
        exact hs
      · next hlt =>
        have hadd : edAdd (edNatSmul (b.val - a.val) edBasepoint) (edNatSmul a.val edBasepoint) =
            edNatSmul a.val edBasepoint := by
          rw [← edNatSmul_add (b.val - a.val) a.val edOnCurve_edBasepoint,
              Nat.sub_add_cancel (Nat.le_of_not_ge hlt), hpos]
        have hs := congrArg (fun X => edAdd X (edNeg (edNatSmul a.val edBasepoint))) hadd
        rw [edAdd_assoc (edOnCurve_edNatSmul _ edOnCurve_edBasepoint) ha_on (edOnCurve_edNeg ha_on),
            edAdd_edNeg_self ha_on, edAdd_edZero (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)] at hs
        exact hs
    have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff _).mp hsub
    rw [edOrderL_eq_l25519] at hdvd
    apply ZMod.val_injective l25519
    have ha_lt := a.val_lt
    have hb_lt := b.val_lt
    split at hdvd
    · have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
    · have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
  · right
    have hsum : edNatSmul (a.val + b.val) edBasepoint = edZero := by
      rw [edNatSmul_add a.val b.val edOnCurve_edBasepoint, hneg,
          edAdd_comm (edNeg (edNatSmul b.val edBasepoint)) (edNatSmul b.val edBasepoint),
          edAdd_edNeg_self hb_on]
    have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff _).mp hsum
    rw [edOrderL_eq_l25519] at hdvd
    have hzero : ((a.val + b.val : ℕ) : ZMod l25519) = 0 :=
      (ZMod.natCast_eq_zero_iff (a.val + b.val) l25519).mpr hdvd
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hzero
    exact eq_neg_of_add_eq_zero_left hzero

private theorem clampedScalarZMod_pm_of_dh_base_eq {w1 w2 : BitVec 256}
    (h : x25519Dh.dh w1 x25519Dh.base = x25519Dh.dh w2 x25519Dh.base) :
    clampedScalarZMod (SignalPqxdh.word256ToBytes w1) =
        clampedScalarZMod (SignalPqxdh.word256ToBytes w2) ∨
      clampedScalarZMod (SignalPqxdh.word256ToBytes w1) =
        -clampedScalarZMod (SignalPqxdh.word256ToBytes w2) := by
  have hbytes : x25519Pubkey (keyToBytes32 w1) = x25519Pubkey (keyToBytes32 w2) := by
    have hv := congrArg (fun Q : X25519Pt => Q.val.bytes.toList) h
    change (x25519Dh.dh w1 x25519BasePt).val.bytes.toList =
      (x25519Dh.dh w2 x25519BasePt).val.bytes.toList at hv
    rw [x25519Dh_dh_val, x25519Dh_dh_val, x25519BasePt_val] at hv
    change (x25519Ref (vec32 (keyToBytes32 w1)) x25519BaseKey.bytes).toList =
      (x25519Ref (vec32 (keyToBytes32 w2)) x25519BaseKey.bytes).toList at hv
    rw [x25519Ref_toList, x25519Ref_toList,
        vec32_of_length_32 (length_keyToBytes32_eq w1),
        vec32_of_length_32 (length_keyToBytes32_eq w2)] at hv
    exact hv
  rw [x25519Pubkey_eq_edNatSmul, x25519Pubkey_eq_edNatSmul] at hbytes
  have hu : edToMontU (edNatSmul (clampScalar (keyToBytes32 w1)) edBasepoint) =
      edToMontU (edNatSmul (clampScalar (keyToBytes32 w2)) edBasepoint) := by
    have hl := congrArg leBytesToNat hbytes
    rwa [leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32),
         leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32)] at hl
  rw [← edNatSmul_mod_edOrderL_edBasepoint (clampScalar (keyToBytes32 w1)),
      ← edNatSmul_mod_edOrderL_edBasepoint (clampScalar (keyToBytes32 w2)),
      clampScalar_keyToBytes32_mod_edOrderL w1,
      clampScalar_keyToBytes32_mod_edOrderL w2] at hu
  exact zmod_pm_of_edToMontU_edBasepoint_eq (clampedScalarZMod_ne_zero _) (clampedScalarZMod_ne_zero _) hu

private theorem zmod_ne_neg_of_ne_zero {c : ZMod l25519} (hc : c ≠ 0) : c ≠ -c := by
  intro h
  have h2 : (2 : ZMod l25519) * c = 0 := by
    calc (2 : ZMod l25519) * c = c + c := by ring
      _ = c + (-c) := by conv_rhs => rw [← h]
      _ = 0 := add_neg_cancel c
  have h2ne : (2 : ZMod l25519) ≠ 0 := by
    intro h0
    have hv := congrArg ZMod.val h0
    have hval2 : ((2 : ℕ) : ZMod l25519).val = 2 := ZMod.val_natCast_of_lt two_lt_l25519
    change ((2 : ℕ) : ZMod l25519).val = (0 : ZMod l25519).val at hv
    rw [hval2, ZMod.val_zero] at hv
    omega
  exact hc ((mul_eq_zero.mp h2).resolve_left h2ne)

/-- Each point `Q : X25519Pt` has at most `64` preimages under `w ↦ x25519Dh.dh w x25519Dh.base`
(`≤ 2` clamped scalars `±c₀` times `2^5 = 32` clamped-away bits of `w : BitVec 256`). -/
theorem x25519Dh_base_fiber_card (Q : X25519Pt) :
    (Finset.univ.filter (fun w : BitVec 256 => x25519Dh.dh w x25519Dh.base = Q)).card ≤ 64 := by
  set S := Finset.univ.filter (fun w : BitVec 256 => x25519Dh.dh w x25519Dh.base = Q)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : x25519Dh.dh w0 x25519Dh.base = Q := (Finset.mem_filter.mp hw0).2
    set c0 := clampedScalarZMod (SignalPqxdh.word256ToBytes w0)
    have hc0_ne_neg : c0 ≠ -c0 := zmod_ne_neg_of_ne_zero (clampedScalarZMod_ne_zero _)
    let tag : BitVec 256 → Bool × Fin 8 × Fin 4 := fun w =>
      (@decide (clampedScalarZMod (SignalPqxdh.word256ToBytes w) = c0) (Classical.propDecidable _),
       ⟨w.toNat % 8, Nat.mod_lt _ (by decide)⟩,
       ⟨w.toNat / 2 ^ 254, Nat.div_lt_of_lt_mul (by have := w.isLt; omega)⟩)
    have hinj : Set.InjOn tag (S : Set (BitVec 256)) := by
      intro w1 hw1 w2 hw2 htag
      have hw1_eq : x25519Dh.dh w1 x25519Dh.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
      have hw2_eq : x25519Dh.dh w2 x25519Dh.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
      have hpm1 := clampedScalarZMod_pm_of_dh_base_eq (hw1_eq.trans hw0_eq.symm)
      have hpm2 := clampedScalarZMod_pm_of_dh_base_eq (hw2_eq.trans hw0_eq.symm)
      have htag_iff : (clampedScalarZMod (SignalPqxdh.word256ToBytes w1) = c0) ↔
          (clampedScalarZMod (SignalPqxdh.word256ToBytes w2) = c0) :=
        @decide_eq_decide _ _ (Classical.propDecidable _) (Classical.propDecidable _) |>.mp
          (congrArg Prod.fst htag)
      have hlo : w1.toNat % 8 = w2.toNat % 8 := congrArg (fun p => p.2.1.val) htag
      have hhi : w1.toNat / 2 ^ 254 = w2.toNat / 2 ^ 254 := congrArg (fun p => p.2.2.val) htag
      have hc_eq :
          clampedScalarZMod (SignalPqxdh.word256ToBytes w1) =
            clampedScalarZMod (SignalPqxdh.word256ToBytes w2) := by
        rcases hpm1 with hc1 | hc1 <;> rcases hpm2 with hc2 | hc2
        · exact hc1.trans hc2.symm
        · exfalso; exact hc0_ne_neg (hc2.symm.trans (htag_iff.mp hc1)).symm
        · exfalso; exact hc0_ne_neg (hc1.symm.trans (htag_iff.mpr hc2)).symm
        · exact hc1.trans hc2.symm
      have hcl_eq := clampScalar25519_eq_of_clampedScalarZMod_eq hc_eq
      have hcwf : cwfC (SignalPqxdh.word256ToBytes w1) = cwfC (SignalPqxdh.word256ToBytes w2) := by
        rw [← cwfC_clamp (SignalPqxdh.word256ToBytes w1),
            ← cwfC_clamp (SignalPqxdh.word256ToBytes w2), hcl_eq]
      exact cwfC_word_eq w1 w2 hcwf hlo hhi
    have hcard_le : S.card ≤ Fintype.card (Bool × Fin 8 × Fin 4) :=
      Finset.card_le_card_of_injOn tag (fun _ _ => Finset.mem_univ _) hinj
    have hcard64 : Fintype.card (Bool × Fin 8 × Fin 4) = 64 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact hcard_le.trans_eq hcard64
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le 64

/-- Tight base-point fiber probability bound `64 / 2 ^ 256 = 1 / 2 ^ 250 = x25519Delta`. -/
theorem x25519Dh_base_fiber_prob_le (Q : X25519Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | x25519Dh.dh x x25519Dh.base = Q} ≤
      x25519Delta := by
  unfold x25519Delta
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample,
      Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_of_le_mul
  calc ((Finset.univ.filter (fun x : BitVec 256 => x25519Dh.dh x x25519Dh.base = Q)).card : ℝ≥0∞)
      ≤ ((64 : ℕ) : ℝ≥0∞) := by exact_mod_cast x25519Dh_base_fiber_card Q
    _ = (2 : ℝ≥0∞) ^ 6 := by norm_num
    _ = ((1 : ℝ≥0∞) / 2 ^ 250) * (2 : ℝ≥0∞) ^ 256 := by
      rw [one_div, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 250 * 2 ^ 6 by rw [← pow_add],
          ENNReal.inv_mul_cancel_left (by simp) (by simp)]

end Computational.Proofs.LibsignalCli.ConcreteX25519Group
