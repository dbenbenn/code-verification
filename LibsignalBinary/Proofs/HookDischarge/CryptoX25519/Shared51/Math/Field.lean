/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519

/-!
# $\mathbb{F}_p$ ($p = 2^{255} - 19$) field arithmetic, primality, and Fermat's little theorem

Arithmetic and primality proofs modulo `p25519 = 2^255 - 19`:

1. Commutative ring identities for `fpAdd`, `fpSub`, `fpNeg`, `fpMul`, `fpSq`, `fpPow`, and `fpInv`.
2. Modular exponentiation bridge `modPowLoop_eq` / `fpPow_eq_pow_mod`
   ($e < 2^{256} \implies \text{fpPow } a\, e = a^e \bmod p$).
3. Euclid's lemma (`IsPrime.dvd_mul`) and Fermat's little theorem (`IsPrime.pow_sub_one_mod`)
   on `Nat` via Freshman's dream.
4. Pocklington primality tests (`pocklington1`, `pocklington2`) and proof of
   `p25519_prime : IsPrime p25519`.
5. Multiplicative inverse (`fpMul_fpInv_cancel`), integral domain cancellation, difference of
   squares (`fpSq_eq_fpSq_iff`), Euler's non-square criterion (`euler_nonsquare`),
   `edD_nonsquare`, and `fpSq_sqrtM1`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field

open VerifiedLibraries.Common (
  p25519 modPowLoop modPow fpAdd fpSub fpNeg fpMul fpSq fpPow fpInv sqrtM1 edD recoverXEven)
/-! ## 1. Basic Bounds & Modular Normalization -/

theorem p25519_pos : 0 < p25519 := by unfold p25519; decide
theorem p25519_gt_one : 1 < p25519 := by unfold p25519; decide
theorem p25519_ne_zero : p25519 ≠ 0 := by unfold p25519; decide
theorem p25519_odd : p25519 % 2 = 1 := by unfold p25519; decide

theorem fpAdd_lt (a b : Nat) : fpAdd a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpSub_lt (a b : Nat) : fpSub a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpNeg_lt (a : Nat) : fpNeg a < p25519 := Nat.mod_lt _ p25519_pos
theorem fpMul_lt (a b : Nat) : fpMul a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpSq_lt (a : Nat) : fpSq a < p25519 := fpMul_lt a a
theorem edD_lt : edD < p25519 := by unfold edD p25519; decide
theorem sqrtM1_lt : sqrtM1 < p25519 := by unfold sqrtM1 p25519; decide

@[simp] theorem fpAdd_mod_p (a b : Nat) : fpAdd a b % p25519 = fpAdd a b :=
  Nat.mod_eq_of_lt (fpAdd_lt a b)
@[simp] theorem fpSub_mod_p (a b : Nat) : fpSub a b % p25519 = fpSub a b :=
  Nat.mod_eq_of_lt (fpSub_lt a b)
@[simp] theorem fpNeg_mod_p (a : Nat) : fpNeg a % p25519 = fpNeg a :=
  Nat.mod_eq_of_lt (fpNeg_lt a)
@[simp] theorem fpMul_mod_p (a b : Nat) : fpMul a b % p25519 = fpMul a b :=
  Nat.mod_eq_of_lt (fpMul_lt a b)
@[simp] theorem fpSq_mod_p (a : Nat) : fpSq a % p25519 = fpSq a :=
  Nat.mod_eq_of_lt (fpSq_lt a)
@[simp] theorem edD_mod_p : edD % p25519 = edD := Nat.mod_eq_of_lt edD_lt
@[simp] theorem sqrtM1_mod_p : sqrtM1 % p25519 = sqrtM1 := Nat.mod_eq_of_lt sqrtM1_lt

theorem fpMul_eq_mul_mod (a b : Nat) : fpMul a b = (a * b) % p25519 := by
  unfold fpMul; rw [← Nat.mul_mod]

theorem fpSq_eq_pow2_mod (a : Nat) : fpSq a = a ^ 2 % p25519 := by
  unfold fpSq; rw [fpMul_eq_mul_mod, Nat.pow_two]

@[simp] theorem fpAdd_mod_left (a b : Nat) : fpAdd (a % p25519) b = fpAdd a b := by
  unfold fpAdd; rw [Nat.mod_add_mod]
@[simp] theorem fpAdd_mod_right (a b : Nat) : fpAdd a (b % p25519) = fpAdd a b := by
  unfold fpAdd; rw [Nat.add_mod_mod]
@[simp] theorem fpNeg_mod (a : Nat) : fpNeg (a % p25519) = fpNeg a := by
  unfold fpNeg; rw [Nat.mod_mod]
@[simp] theorem fpSub_mod_left (a b : Nat) : fpSub (a % p25519) b = fpSub a b := by
  unfold fpSub
  have hb : b % p25519 ≤ p25519 := Nat.le_of_lt (Nat.mod_lt b p25519_pos)
  rw [Nat.add_sub_assoc hb, Nat.mod_add_mod, ← Nat.add_sub_assoc hb]
@[simp] theorem fpSub_mod_right (a b : Nat) : fpSub a (b % p25519) = fpSub a b := by
  unfold fpSub; rw [Nat.mod_mod]
@[simp] theorem fpMul_mod_left (a b : Nat) : fpMul (a % p25519) b = fpMul a b := by
  unfold fpMul; rw [Nat.mod_mod]
@[simp] theorem fpMul_mod_right (a b : Nat) : fpMul a (b % p25519) = fpMul a b := by
  unfold fpMul; rw [Nat.mod_mod]
@[simp] theorem fpSq_mod (a : Nat) : fpSq (a % p25519) = fpSq a := by
  unfold fpSq; rw [fpMul_mod_left, fpMul_mod_right]

/-! ## 2. Commutative Ring Identities on $\mathbb{F}_{p_{25519}}$ -/

theorem fpAdd_comm (a b : Nat) : fpAdd a b = fpAdd b a := by
  unfold fpAdd; rw [Nat.add_comm]

theorem fpAdd_assoc (a b c : Nat) : fpAdd (fpAdd a b) c = fpAdd a (fpAdd b c) := by
  unfold fpAdd; rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

@[simp] theorem fpAdd_zero (a : Nat) : fpAdd a 0 = a % p25519 := by
  unfold fpAdd; simp
@[simp] theorem zero_fpAdd (a : Nat) : fpAdd 0 a = a % p25519 := by
  unfold fpAdd; simp

@[simp] theorem fpNeg_zero : fpNeg 0 = 0 := by unfold fpNeg; simp

theorem fpNeg_of_mod_eq_zero {a : Nat} (h : a % p25519 = 0) : fpNeg a = 0 := by
  unfold fpNeg; rw [h, Nat.sub_zero, Nat.mod_self]

theorem fpNeg_of_mod_ne_zero {a : Nat} (h : a % p25519 ≠ 0) : fpNeg a = p25519 - a % p25519 := by
  unfold fpNeg
  have hlt : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem fpNeg_fpNeg (a : Nat) : fpNeg (fpNeg a) = a % p25519 := by
  have hlt : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  by_cases h0 : a % p25519 = 0
  · rw [fpNeg_of_mod_eq_zero h0, fpNeg_zero, h0]
  · have hsub_lt : p25519 - a % p25519 < p25519 := by omega
    have hsub_mod : (p25519 - a % p25519) % p25519 = p25519 - a % p25519 := Nat.mod_eq_of_lt hsub_lt
    rw [fpNeg_of_mod_ne_zero h0, fpNeg_of_mod_ne_zero (by rw [hsub_mod]; omega), hsub_mod]
    omega

theorem fpSub_eq_fpAdd_fpNeg (a b : Nat) : fpSub a b = fpAdd a (fpNeg b) := by
  rw [← fpSub_mod_right, ← fpNeg_mod]
  unfold fpSub fpAdd fpNeg
  rw [Nat.mod_mod]
  have hb : b % p25519 < p25519 := Nat.mod_lt b p25519_pos
  rw [Nat.add_mod a, Nat.mod_mod, ← Nat.add_mod, Nat.add_sub_assoc (by omega)]

@[simp] theorem fpAdd_fpNeg_self (a : Nat) : fpAdd a (fpNeg a) = 0 := by
  rw [← fpSub_eq_fpAdd_fpNeg, ← fpSub_mod_left]
  unfold fpSub
  have ha : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  rw [show a % p25519 + p25519 - a % p25519 = p25519 by omega, Nat.mod_self]

@[simp] theorem fpNeg_fpAdd_self (a : Nat) : fpAdd (fpNeg a) a = 0 := by
  rw [fpAdd_comm, fpAdd_fpNeg_self]

@[simp] theorem fpSub_self (a : Nat) : fpSub a a = 0 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpAdd_fpNeg_self]

@[simp] theorem fpSub_zero (a : Nat) : fpSub a 0 = a % p25519 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpNeg_zero, fpAdd_zero]

@[simp] theorem zero_fpSub (a : Nat) : fpSub 0 a = fpNeg a := by
  rw [fpSub_eq_fpAdd_fpNeg, zero_fpAdd, fpNeg_mod_p]

theorem fpNeg_fpAdd (a b : Nat) : fpNeg (fpAdd a b) = fpAdd (fpNeg a) (fpNeg b) := by
  have h2 : fpAdd (fpAdd a b) (fpAdd (fpNeg a) (fpNeg b)) = 0 := by
    rw [fpAdd_assoc, ← fpAdd_assoc b, fpAdd_comm b (fpNeg a), fpAdd_assoc (fpNeg a),
        ← fpAdd_assoc a, fpAdd_fpNeg_self, zero_fpAdd, fpAdd_mod_p, fpAdd_fpNeg_self]
  have h3 := congrArg (fpAdd (fpNeg (fpAdd a b))) h2
  rw [← fpAdd_assoc, fpNeg_fpAdd_self, zero_fpAdd, fpAdd_zero, fpNeg_mod_p, fpAdd_mod_p] at h3
  exact h3.symm

theorem fpNeg_fpSub (a b : Nat) : fpNeg (fpSub a b) = fpSub b a := by
  rw [fpSub_eq_fpAdd_fpNeg, fpNeg_fpAdd, fpNeg_fpNeg, fpAdd_mod_right,
      fpAdd_comm, ← fpSub_eq_fpAdd_fpNeg]

theorem fpAdd_fpSub_cancel (a b : Nat) : fpSub (fpAdd a b) b = a % p25519 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpAdd_assoc, fpAdd_fpNeg_self, fpAdd_zero]

theorem fpSub_fpAdd_cancel (a b : Nat) : fpAdd (fpSub a b) b = a % p25519 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpAdd_assoc, fpNeg_fpAdd_self, fpAdd_zero]

theorem fpSub_eq_zero_iff (a b : Nat) : fpSub a b = 0 ↔ a % p25519 = b % p25519 := by
  constructor
  · intro h
    have h1 := congrArg (fun x => fpAdd x b) h
    rw [fpSub_fpAdd_cancel, zero_fpAdd] at h1
    exact h1
  · intro h; rw [← fpSub_mod_left, ← fpSub_mod_right, h, fpSub_self]

theorem fpNeg_eq_zero_iff (a : Nat) : fpNeg a = 0 ↔ a % p25519 = 0 := by
  rw [← zero_fpSub, fpSub_eq_zero_iff, Nat.zero_mod]
  exact ⟨Eq.symm, Eq.symm⟩

theorem fpMul_comm (a b : Nat) : fpMul a b = fpMul b a := by
  unfold fpMul; rw [Nat.mul_comm]

theorem fpMul_assoc (a b c : Nat) : fpMul (fpMul a b) c = fpMul a (fpMul b c) := by
  rw [fpMul_eq_mul_mod, fpMul_eq_mul_mod a (fpMul b c), fpMul_eq_mul_mod a b, fpMul_eq_mul_mod b c,
      Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

@[simp] theorem fpMul_zero (a : Nat) : fpMul a 0 = 0 := by unfold fpMul; simp
@[simp] theorem zero_fpMul (a : Nat) : fpMul 0 a = 0 := by unfold fpMul; simp
@[simp] theorem fpMul_one (a : Nat) : fpMul a 1 = a % p25519 := by
  rw [fpMul_eq_mul_mod, Nat.mul_one]
@[simp] theorem one_fpMul (a : Nat) : fpMul 1 a = a % p25519 := by
  rw [fpMul_eq_mul_mod, Nat.one_mul]

theorem fpMul_fpAdd (a b c : Nat) : fpMul a (fpAdd b c) = fpAdd (fpMul a b) (fpMul a c) := by
  unfold fpAdd
  rw [fpMul_mod_right, fpMul_eq_mul_mod a (b + c), fpMul_eq_mul_mod a b, fpMul_eq_mul_mod a c,
      Nat.mod_add_mod, Nat.add_mod_mod, ← Nat.mul_add]

theorem fpAdd_fpMul (a b c : Nat) : fpMul (fpAdd a b) c = fpAdd (fpMul a c) (fpMul b c) := by
  rw [fpMul_comm, fpMul_fpAdd, fpMul_comm c, fpMul_comm c]

theorem fpMul_fpNeg (a b : Nat) : fpMul a (fpNeg b) = fpNeg (fpMul a b) := by
  have h1 : fpAdd (fpMul a b) (fpMul a (fpNeg b)) = 0 := by
    rw [← fpMul_fpAdd, fpAdd_fpNeg_self, fpMul_zero]
  have h2 := congrArg (fpAdd (fpNeg (fpMul a b))) h1
  rw [← fpAdd_assoc, fpNeg_fpAdd_self, zero_fpAdd, fpAdd_zero, fpMul_mod_p, fpNeg_mod_p] at h2
  exact h2

theorem fpNeg_fpMul (a b : Nat) : fpMul (fpNeg a) b = fpNeg (fpMul a b) := by
  rw [fpMul_comm, fpMul_fpNeg, fpMul_comm]

theorem fpNeg_fpMul_fpNeg (a b : Nat) : fpMul (fpNeg a) (fpNeg b) = fpMul a b := by
  rw [fpMul_fpNeg, fpNeg_fpMul, fpNeg_fpNeg, fpMul_mod_p]

theorem fpMul_fpSub (a b c : Nat) : fpMul a (fpSub b c) = fpSub (fpMul a b) (fpMul a c) := by
  rw [fpSub_eq_fpAdd_fpNeg, fpMul_fpAdd, fpMul_fpNeg, ← fpSub_eq_fpAdd_fpNeg]

theorem fpSub_fpMul (a b c : Nat) : fpMul (fpSub a b) c = fpSub (fpMul a c) (fpMul b c) := by
  rw [fpMul_comm, fpMul_fpSub, fpMul_comm c, fpMul_comm c]

@[simp] theorem fpSq_zero : fpSq 0 = 0 := fpMul_zero 0
@[simp] theorem fpSq_one : fpSq 1 = 1 := by unfold fpSq; decide
@[simp] theorem fpSq_fpNeg (a : Nat) : fpSq (fpNeg a) = fpSq a := fpNeg_fpMul_fpNeg a a

theorem fpSq_fpMul (a b : Nat) : fpSq (fpMul a b) = fpMul (fpSq a) (fpSq b) := by
  unfold fpSq
  rw [fpMul_assoc, ← fpMul_assoc b a b, fpMul_comm b a, fpMul_assoc a b b, ← fpMul_assoc]

theorem fpSub_fpSq (a b : Nat) : fpSub (fpSq a) (fpSq b) = fpMul (fpSub a b) (fpAdd a b) := by
  unfold fpSq
  rw [fpSub_fpMul, fpMul_fpAdd, fpMul_fpAdd, fpMul_comm b a,
      fpSub_eq_fpAdd_fpNeg (fpAdd (fpMul a a) (fpMul a b)),
      fpNeg_fpAdd, ← fpAdd_assoc, fpAdd_assoc (fpMul a a),
      fpAdd_fpNeg_self, fpAdd_zero, fpMul_mod_p, ← fpSub_eq_fpAdd_fpNeg]

/-! ## 3. Universal `Int` Bridge for $\mathbb{F}_{p_{25519}}$ Ring Identities (`fp_ring`) -/

theorem p25519_int_pos : (0 : Int) < (p25519 : Int) := by unfold p25519; decide

theorem nat_cast_fpAdd_emod (a b : Nat) :
    ((fpAdd a b : Nat) : Int) % (p25519 : Int) = ((a : Int) + (b : Int)) % (p25519 : Int) := by
  unfold fpAdd
  rw [← Int.natCast_emod, Nat.mod_mod, Int.natCast_emod, Int.natCast_add]

theorem nat_cast_fpNeg_emod (a : Nat) :
    ((fpNeg a : Nat) : Int) % (p25519 : Int) = (-(a : Int)) % (p25519 : Int) := by
  unfold fpNeg
  have ha : a % p25519 ≤ p25519 := Nat.le_of_lt (Nat.mod_lt a p25519_pos)
  rw [← Int.natCast_emod, Nat.mod_mod, Int.natCast_emod, Int.ofNat_sub ha, Int.natCast_emod,
      Int.sub_emod, Int.emod_self, Int.emod_emod, ← Int.zero_emod (p25519 : Int),
      ← Int.sub_emod, Int.zero_sub]

theorem nat_cast_fpSub_emod (a b : Nat) :
    ((fpSub a b : Nat) : Int) % (p25519 : Int) = ((a : Int) - (b : Int)) % (p25519 : Int) := by
  rw [fpSub_eq_fpAdd_fpNeg, nat_cast_fpAdd_emod, Int.add_emod,
      nat_cast_fpNeg_emod, ← Int.add_emod, Int.sub_eq_add_neg]

theorem nat_cast_fpMul_emod (a b : Nat) :
    ((fpMul a b : Nat) : Int) % (p25519 : Int) = ((a : Int) * (b : Int)) % (p25519 : Int) := by
  rw [fpMul_eq_mul_mod, ← Int.natCast_emod, Nat.mod_mod, Int.natCast_emod, Int.natCast_mul]

theorem nat_cast_fpSq_emod (a : Nat) :
    ((fpSq a : Nat) : Int) % (p25519 : Int) = ((a : Int) * (a : Int)) % (p25519 : Int) :=
  nat_cast_fpMul_emod a a

theorem eq_of_int_emod_eq {a b : Nat} (ha : a < p25519) (hb : b < p25519)
    (h : (a : Int) % (p25519 : Int) = (b : Int) % (p25519 : Int)) : a = b := by
  rw [← Int.natCast_emod, ← Int.natCast_emod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact Int.ofNat.inj h

/-! ## 4. Modular Exponentiation (`modPow` / `fpPow`) -/

private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  Bool.eq_false_iff.mpr (fun heq => h (beq_iff_eq.mp heq))

private theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        have hexp_eq : 2 * (exp / 2) = exp := by omega
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, hexp_eq, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        have hexp_eq : (2 * (exp / 2)).succ = exp := by omega
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', hexp_eq]

private theorem modPow_eq_pow_mod (base exp m : Nat) (he : exp < 2 ^ 256) :
    modPow base exp m = base ^ exp % m := by
  unfold modPow; rw [modPowLoop_eq 256 (base % m) exp m 1 he, Nat.one_mul, ← Nat.pow_mod base exp m]

private theorem fpPow_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) :
    fpPow a e = a ^ e % p25519 :=
  modPow_eq_pow_mod a e p25519 he

theorem fpPow_lt (a e : Nat) : fpPow a e < p25519 := by
  unfold fpPow modPow
  let rec loop_lt (fuel b exp acc : Nat) : modPowLoop fuel b exp p25519 acc < p25519 := by
    cases fuel with
    | zero => unfold modPowLoop; exact Nat.mod_lt _ p25519_pos
    | succ f =>
      unfold modPowLoop
      split
      · exact Nat.mod_lt _ p25519_pos
      · exact loop_lt f _ _ _
  exact loop_lt 256 _ _ _

theorem fpInv_lt (a : Nat) : fpInv a < p25519 := fpPow_lt a (p25519 - 2)

@[simp] theorem fpPow_mod_p (a e : Nat) : fpPow a e % p25519 = fpPow a e :=
  Nat.mod_eq_of_lt (fpPow_lt a e)
@[simp] theorem fpInv_mod_p (a : Nat) : fpInv a % p25519 = fpInv a :=
  Nat.mod_eq_of_lt (fpInv_lt a)

@[simp] theorem fpPow_mod_left (a e : Nat) : fpPow (a % p25519) e = fpPow a e := by
  unfold fpPow modPow; rw [Nat.mod_mod]
@[simp] theorem fpInv_mod (a : Nat) : fpInv (a % p25519) = fpInv a :=
  fpPow_mod_left a (p25519 - 2)

theorem fpInv_eq_pow_mod (a : Nat) : fpInv a = a ^ (p25519 - 2) % p25519 :=
  fpPow_eq_pow_mod a (p25519 - 2) (by unfold p25519; decide)

/-! ## 5. Primality, Euclid's Lemma, & Fermat's Little Theorem on `Nat` -/

/-- Primality predicate on `Nat`: `1 < p` and the only divisors of `p` are `1` and `p`. -/
@[expose] def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrime.gt_one {p : Nat} (hp : IsPrime p) : 1 < p := hp.1
theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := Nat.lt_trans Nat.zero_lt_one hp.1
theorem IsPrime.ne_zero {p : Nat} (hp : IsPrime p) : p ≠ 0 := Nat.ne_of_gt hp.pos

/-- Gauss's descent proof of Euclid's Lemma on `Nat`:
    for prime `p` and `a < p`, if `p ∣ a * b`, then `a = 0 ∨ p ∣ b`. -/
private theorem IsPrime.dvd_mul_of_lt {p : Nat} (hp : IsPrime p) :
    ∀ a < p, ∀ b, p ∣ a * b → a = 0 ∨ p ∣ b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha_pos
    · exact Or.inl rfl
    · by_cases ha1 : a = 1
      · subst ha1; rw [Nat.one_mul] at hab; exact Or.inr hab
      · have hmod_lt : p % a < a := Nat.mod_lt p ha_pos
        have hmod_ne : p % a ≠ 0 := by
          intro h0
          rcases hp.2 a (Nat.dvd_of_mod_eq_zero h0) with rfl | rfl
          · exact ha1 rfl
          · exact Nat.lt_irrefl a ha
        have hdiv_eq : (p % a) * b + (p / a) * (a * b) = p * b := by
          rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.mod_add_div' p a]
        have hdvd_sum : p ∣ (p % a) * b + (p / a) * (a * b) := by
          rw [hdiv_eq]; exact Nat.dvd_mul_right p b
        have hdvd_rhs : p ∣ (p / a) * (a * b) := by
          rcases hab with ⟨k, hk⟩
          exact ⟨(p / a) * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (p / a) p, Nat.mul_assoc]⟩
        have hdvd_lhs : p ∣ (p % a) * b :=
          (Nat.dvd_add_iff_left hdvd_rhs).mpr hdvd_sum
        rcases ih (p % a) hmod_lt (Nat.lt_trans hmod_lt ha) b hdvd_lhs with h0 | hpb
        · exact absurd h0 hmod_ne
        · exact Or.inr hpb

/-- Euclid's Lemma: if `p` is prime and `p ∣ a * b`, then `p ∣ a ∨ p ∣ b`. -/
theorem IsPrime.dvd_mul {p : Nat} (hp : IsPrime p) {a b : Nat} (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have heq : (a % p) * b + p * ((a / p) * b) = a * b := by
    rw [← Nat.mul_assoc p, ← Nat.add_mul, Nat.mod_add_div a p]
  have hdvd : p ∣ (a % p) * b := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right p ((a / p) * b))).mpr
    rwa [heq]
  rcases hp.dvd_mul_of_lt (a % p) (Nat.mod_lt a hp.pos) b hdvd with h0 | hpb
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h0)
  · exact Or.inr hpb

theorem IsPrime.mul_mod_eq_zero_iff {p : Nat} (hp : IsPrime p) (a b : Nat) :
    (a * b) % p = 0 ↔ a % p = 0 ∨ b % p = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
  refine ⟨hp.dvd_mul, ?_⟩
  rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact ⟨k * b, by rw [Nat.mul_assoc]⟩
  · exact ⟨a * k, by rw [← Nat.mul_assoc, Nat.mul_comm a p, Nat.mul_assoc]⟩

theorem IsPrime.pow_mod_eq_zero_iff {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ n > 0, a ^ n % p = 0 ↔ a % p = 0
  | 1, _ => by rw [Nat.pow_one]
  | n + 2, _ => by
    rw [Nat.pow_succ, hp.mul_mod_eq_zero_iff, hp.pow_mod_eq_zero_iff a (n + 1) (by omega), or_self]

/-- Binomial coefficients $\binom{n}{k}$. -/
private def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

private theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
private theorem choose_gt : ∀ (n k : Nat), n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    unfold choose
    rw [choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]
private theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by unfold choose; rw [choose_self n, choose_gt n (n + 1) (by omega)]
private theorem choose_one_right : ∀ n : Nat, choose n 1 = n
  | 0 => rfl
  | n + 1 => by unfold choose; rw [choose_zero_right, choose_one_right n, Nat.add_comm]

/-- Absorption identity $(k + 1) \binom{n + 1}{k + 1} = (n + 1) \binom{n}{k}$. -/
private theorem succ_mul_choose_succ :
    ∀ (n k : Nat), (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k
  | n, 0 => by rw [Nat.one_mul, choose_one_right, choose_zero_right, Nat.mul_one]
  | 0, k + 1 => by
    change (k + 2) * (choose 0 (k + 1) + choose 0 (k + 2)) = 1 * choose 0 (k + 1)
    simp [choose]
  | n + 1, k + 1 => by
    change (k + 2) * (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) =
      (n + 2) * (choose n k + choose n (k + 1))
    have ih1 := succ_mul_choose_succ n k
    have ih2 := succ_mul_choose_succ n (k + 1)
    have hsplit : (k + 2) * (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) =
        (k + 1) * choose (n + 1) (k + 1) + choose (n + 1) (k + 1) +
        (k + 2) * choose (n + 1) (k + 2) := by
      rw [Nat.mul_add, Nat.succ_mul (k + 1)]
    have h1 : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
    rw [hsplit, ih1, ih2, h1, Nat.mul_add (n + 2), Nat.succ_mul (n + 1), Nat.succ_mul (n + 1)]
    omega

/-- Kummer's lemma for prime $p$: $p \mid \binom{p}{k}$ for $0 < k < p$. -/
private theorem IsPrime.dvd_choose {p k : Nat} (hp : IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ choose p k := by
  rcases p with _ | p'
  · omega
  rcases k with _ | k'
  · omega
  have habs := succ_mul_choose_succ p' k'
  have hdvd : (p' + 1) ∣ (k' + 1) * choose (p' + 1) (k' + 1) :=
    ⟨choose p' k', habs⟩
  rcases hp.dvd_mul hdvd with hpk | hpc
  · exfalso; have := Nat.le_of_dvd (by omega) hpk; omega
  · exact hpc

/-- Partial binomial sum $\sum_{i=0}^{k} \binom{n}{i} a^i$. -/
private def binomSum (n a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => binomSum n a k + choose n (k + 1) * a ^ (k + 1)

private theorem binomSum_succ (n a : Nat) :
    ∀ k : Nat, binomSum (n + 1) a (k + 1) = binomSum n a (k + 1) + a * binomSum n a k
  | 0 => by
    change 1 + (choose n 0 + choose n 1) * (1 * a) = (1 + choose n 1 * (1 * a)) + a * 1
    rw [choose_zero_right, Nat.one_mul, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    omega
  | k + 1 => by
    unfold binomSum
    rw [binomSum_succ n a k]
    change (binomSum n a (k + 1) + a * binomSum n a k) +
        (choose n (k + 1) + choose n (k + 2)) * (a ^ (k + 1) * a) =
      (binomSum n a (k + 1) + choose n (k + 2) * (a ^ (k + 1) * a)) +
        a * (binomSum n a k + choose n (k + 1) * a ^ (k + 1))
    rw [Nat.add_mul, Nat.mul_add]
    have hmul : choose n (k + 1) * (a ^ (k + 1) * a) = a * (choose n (k + 1) * a ^ (k + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (choose n (k + 1) * a ^ (k + 1)) a]
    omega

private theorem add_one_pow_eq_binomSum (a : Nat) :
    ∀ n : Nat, (a + 1) ^ n = binomSum n a n
  | 0 => rfl
  | n + 1 => by
    have hgt : binomSum n a (n + 1) = binomSum n a n := by
      change binomSum n a n + choose n (n + 1) * a ^ (n + 1) = binomSum n a n
      rw [choose_gt n (n + 1) (by omega), Nat.zero_mul, Nat.add_zero]
    rw [Nat.pow_succ, add_one_pow_eq_binomSum a n, binomSum_succ, hgt, Nat.mul_comm _ (a + 1),
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem binomSum_prime_lt_mod {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ k < p, binomSum p a k % p = 1 % p
  | 0, _ => rfl
  | k + 1, hk => by
    unfold binomSum
    have hdvd : p ∣ choose p (k + 1) := hp.dvd_choose (by omega) hk
    have h0 : (choose p (k + 1) * a ^ (k + 1)) % p = 0 := by
      rw [Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod, binomSum_prime_lt_mod hp a k (by omega)]

/-- Freshman's Dream: $(a + 1)^p \equiv a^p + 1 \pmod p$ for prime $p$. -/
theorem IsPrime.add_one_pow_mod {p : Nat} (hp : IsPrime p) (a : Nat) :
    (a + 1) ^ p % p = (a ^ p + 1) % p := by
  rw [add_one_pow_eq_binomSum]
  rcases p with _ | p'
  · exact absurd hp.gt_one (by decide)
  unfold binomSum
  rw [choose_self (p' + 1), Nat.one_mul, Nat.add_mod,
      binomSum_prime_lt_mod hp a p' (by omega), ← Nat.add_mod, Nat.add_comm 1]

/-- Fermat's Little Theorem (unreduced form): $a^p \equiv a \pmod p$ for all $a : \text{Nat}$. -/
theorem IsPrime.pow_mod_self {p : Nat} (hp : IsPrime p) : ∀ a : Nat, a ^ p % p = a % p
  | 0 => by
    rcases p with _ | p'
    · exact absurd hp.gt_one (by decide)
    rw [Nat.zero_pow (by omega)]
  | a + 1 => by
    rw [hp.add_one_pow_mod a, Nat.add_mod, hp.pow_mod_self a, ← Nat.add_mod]

private theorem IsPrime.mul_right_cancel_mod_of_le {p a b c : Nat} (hp : IsPrime p)
    (hc : c % p ≠ 0) (hle : a % p ≤ b % p) (h : (a * c) % p = (b * c) % p) :
    a % p = b % p := by
  have h1 : ((b % p - a % p) * c + (a % p) * c) % p = ((b % p) * c) % p := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  have h_eq : ((b % p) * c) % p = ((a % p) * c) % p := by
    rw [Nat.mod_mul_mod, ← h, ← Nat.mod_mul_mod]
  rw [h_eq] at h1
  have hdvd : p ∣ (b % p - a % p) * c := by
    have hdiv1 := Nat.div_add_mod ((b % p - a % p) * c + (a % p) * c) p
    have hdiv2 := Nat.div_add_mod ((a % p) * c) p
    have h2 : (b % p - a % p) * c =
        p * (((b % p - a % p) * c + (a % p) * c) / p - ((a % p) * c) / p) := by
      rw [Nat.mul_sub_left_distrib]; omega
    exact ⟨_, h2⟩
  rcases (hp.mul_mod_eq_zero_iff _ _).mp (Nat.mod_eq_zero_of_dvd hdvd) with h0 | h0
  · have hlt : b % p - a % p < p := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt b hp.pos)
    rw [Nat.mod_eq_of_lt hlt] at h0; omega
  · exact absurd h0 hc

/-- Fermat's little theorem: if $p$ is prime and $a \bmod p \ne 0$, then $a^{p - 1} \bmod p = 1$. -/
theorem IsPrime.pow_sub_one_mod {p : Nat} (hp : IsPrime p) {a : Nat} (ha : a % p ≠ 0) :
    a ^ (p - 1) % p = 1 := by
  have hpow : (a ^ (p - 1) * a) % p = (1 * a) % p := by
    rw [← Nat.pow_succ, show (p - 1).succ = p by have := hp.gt_one; omega,
        hp.pow_mod_self a, Nat.one_mul]
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.gt_one
  refine (?_ : a ^ (p - 1) % p = 1 % p).trans hp1
  by_cases hle : a ^ (p - 1) % p ≤ 1 % p
  · exact hp.mul_right_cancel_mod_of_le ha hle hpow
  · exact (hp.mul_right_cancel_mod_of_le ha (by omega) hpow.symm).symm

/-! ## 6. Pocklington Primality Certificate & Proof of `IsPrime p25519` -/

/-- Every composite number $n > 1$ has a prime divisor $p$ with $p^2 \le n$. -/
private theorem exists_prime_dvd_sq_le :
    ∀ n : Nat, 1 < n → ¬ IsPrime n → ∃ p : Nat, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn1 hnp
    have hex : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
      apply Classical.byContradiction
      intro hno
      apply hnp
      refine ⟨hn1, fun d hd => Classical.byContradiction fun hne => ?_⟩
      exact hno ⟨d, hd, fun h1 => hne (Or.inl h1), fun hn => hne (Or.inr hn)⟩
    rcases hex with ⟨d, ⟨q, hnq⟩, hd1, hdn⟩
    have hd_pos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · rw [Nat.zero_mul] at hnq; omega
      · exact hpos
    have hq_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | hpos
      · rw [Nat.mul_zero] at hnq; omega
      · exact hpos
    have hd_gt1 : 1 < d := by omega
    have hq_gt1 : 1 < q := by
      rcases Nat.eq_or_lt_of_le (show 1 ≤ q by omega) with rfl | hlt
      · rw [Nat.mul_one] at hnq; exact absurd hnq.symm hdn
      · exact hlt
    have h_min : d * d ≤ n ∨ q * q ≤ n := by
      by_cases hle : d ≤ q
      · left; rw [hnq]; exact Nat.mul_le_mul_left d hle
      · have hle' : q ≤ d := by omega
        right; rw [hnq]; exact Nat.mul_le_mul_right q hle'
    have finish_factor (m : Nat) (hm1 : 1 < m) (hmn : m < n) (hmd : m ∣ n) (hmsq : m * m ≤ n) :
        ∃ p : Nat, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
      by_cases hmp : IsPrime m
      · exact ⟨m, hmp, hmd, hmsq⟩
      · rcases ih m hmn hm1 hmp with ⟨p, hp, hpm, hpsq⟩
        have hpm_le : p ≤ m := Nat.le_of_dvd (by omega) hpm
        have hpsq_m : p * p ≤ m * m := Nat.mul_le_mul hpm_le hpm_le
        exact ⟨p, hp, Nat.dvd_trans hpm hmd, Nat.le_trans hpsq_m hmsq⟩
    rcases h_min with hdsq | hqsq
    · have hdn_lt : d < n := by
        rw [hnq]
        calc d = d * 1 := (Nat.mul_one d).symm
          _ < d * q := Nat.mul_lt_mul_of_pos_left hq_gt1 hd_pos
      exact finish_factor d hd_gt1 hdn_lt ⟨q, hnq⟩ hdsq
    · have hqn_lt : q < n := by
        rw [hnq]
        calc q = 1 * q := (Nat.one_mul q).symm
          _ < d * q := Nat.mul_lt_mul_of_pos_right hd_gt1 hq_pos
      exact finish_factor q hq_gt1 hqn_lt ⟨d, by rw [hnq, Nat.mul_comm]⟩ hqsq

/-- Order-GCD lemma: if $b^x \equiv 1 \pmod p$ and $b^y \equiv 1 \pmod p$, then
    $b^{\gcd(x, y)} \equiv 1 \pmod p$. -/
private theorem pow_mod_eq_one_gcd (b p : Nat) :
    ∀ x y : Nat, b ^ x % p = 1 % p → b ^ y % p = 1 % p → b ^ (Nat.gcd x y) % p = 1 % p := by
  intro x y
  induction x, y using Nat.gcd.induction with
  | H0 y => intro _ hy; rwa [Nat.gcd_zero_left]
  | H1 x y hx ih =>
    intro hbx hby
    rw [Nat.gcd_rec]
    apply ih _ hbx
    have hdiv : y = x * (y / x) + y % x := (Nat.div_add_mod y x).symm
    have hpow : b ^ y % p = ((b ^ x) ^ (y / x) * b ^ (y % x)) % p := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdiv]
    have h1 : (b ^ x) ^ (y / x) % p = 1 % p := by
      rw [Nat.pow_mod, hbx, ← Nat.pow_mod, Nat.one_pow]
    rw [hpow, Nat.mul_mod, h1, ← Nat.mul_mod, Nat.one_mul] at hby
    exact hby

/-- Pocklington single-prime divisor lemma: if `q` is prime, `q ∣ n - 1`,
    `modPow a (n - 1) n = 1`, and `Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n = 1`,
    then for every prime divisor `p` of `n`, `q ∣ p - 1`. -/
private theorem pocklington_dvd_sub_one {n q a p : Nat}
    (hq : IsPrime q) (hq_dvd : (n - 1) % q = 0) (hn_lt : n - 1 < 2 ^ 256)
    (hfermat : modPow a (n - 1) n = 1)
    (hgcd : Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n = 1)
    (hp : IsPrime p) (hp_dvd : p ∣ n) : q ∣ p - 1 := by
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.gt_one
  have hdiv_lt : (n - 1) / q < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_lt
  have hfermat' : a ^ (n - 1) % n = 1 := by rw [← modPow_eq_pow_mod a (n - 1) n hn_lt, hfermat]
  let b := a ^ ((n - 1) / q)
  have hbq_eq : b ^ q = a ^ (n - 1) := by
    dsimp [b]; rw [← Nat.pow_mul, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq_dvd)]
  have hbq_mod : b ^ q % p = 1 % p := by
    rw [hbq_eq, ← Nat.mod_mod_of_dvd _ hp_dvd, hfermat']
  have hb_ne0 : b % p ≠ 0 := by
    intro h0
    have : b ^ q % p = 0 := (hp.pow_mod_eq_zero_iff b q hq.pos).mpr h0
    rw [hbq_mod, hp1] at this; exact absurd this (by decide)
  have hbp1 : b ^ (p - 1) % p = 1 % p := by
    rw [hp1]; exact hp.pow_sub_one_mod hb_ne0
  have hbgcd : b ^ (Nat.gcd q (p - 1)) % p = 1 % p :=
    pow_mod_eq_one_gcd b p q (p - 1) hbq_mod hbp1
  rcases hq.2 (Nat.gcd q (p - 1)) (Nat.gcd_dvd_left q (p - 1)) with hgcd1 | hgcdq
  · exfalso
    rw [hgcd1, Nat.pow_one, hp1] at hbgcd
    let r := modPow a ((n - 1) / q) n
    have hr_eq : r = b % n := modPow_eq_pow_mod a ((n - 1) / q) n hdiv_lt
    have hr_mod : r % p = 1 := by rw [hr_eq, Nat.mod_mod_of_dvd _ hp_dvd, hbgcd]
    have hr_ne0 : r ≠ 0 := by intro h0; rw [h0, Nat.zero_mod] at hr_mod; exact absurd hr_mod (by decide)
    have hp_dvd_rn : p ∣ r + n - 1 := by
      rcases hp_dvd with ⟨k, rfl⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      have h1 : (r + p * k) % p = 1 := by rw [Nat.add_mul_mod_self_left, hr_mod]
      have hdiv := Nat.div_add_mod (r + p * k) p
      rw [h1] at hdiv
      have h2 : r + p * k - 1 = p * ((r + p * k) / p) := by omega
      rw [h2, Nat.mul_mod_right]
    have hp_dvd_one : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hp_dvd_rn hp_dvd
    exact absurd (Nat.le_of_dvd Nat.one_pos hp_dvd_one) (by have := hp.gt_one; omega)
  · rw [← hgcdq]; exact Nat.gcd_dvd_right q (p - 1)

/-- Computable 1-prime Pocklington certificate check. -/
@[expose] def checkPock1 (n q a : Nat) : Bool :=
  decide (1 < n) && decide (n - 1 < 2 ^ 256) &&
  ((n - 1) % q == 0) && decide (n < q * q) &&
  (modPow a (n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n == 1)

/-- 1-prime Pocklington primality theorem. -/
theorem pocklington1 {n q a : Nat} (hq : IsPrime q) (hchk : checkPock1 n q a = true) :
    IsPrime n := by
  unfold checkPock1 at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hn1, hn_lt⟩, hq_dvd⟩, hnq2⟩, hfermat⟩, hgcd⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hq_dvd_p1 : q ∣ p - 1 := pocklington_dvd_sub_one hq hq_dvd hn_lt hfermat hgcd hp hp_dvd
  have hqp : q < p := by
    have hp_gt1 := hp.gt_one
    have hle := Nat.le_of_dvd (by omega) hq_dvd_p1
    omega
  have hq2_lt_p2 : q * q < p * p := Nat.mul_lt_mul_of_lt_of_lt hqp hqp
  omega

/-- Computable 2-prime Pocklington certificate check. -/
@[expose] def checkPock2 (n q1 q2 a : Nat) : Bool :=
  decide (1 < n) && decide (n - 1 < 2 ^ 256) && decide (q2 < q1) &&
  ((n - 1) % q1 == 0) && ((n - 1) % q2 == 0) &&
  decide (n < (q1 * q2) * (q1 * q2)) &&
  (modPow a (n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q1) n + n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q2) n + n - 1) n == 1)

/-- 2-prime Pocklington primality theorem. -/
theorem pocklington2 {n q1 q2 a : Nat} (hq1 : IsPrime q1) (hq2 : IsPrime q2)
    (hchk : checkPock2 n q1 q2 a = true) : IsPrime n := by
  unfold checkPock2 at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨hn1, hn_lt⟩, hq21⟩, hq1_dvd⟩, hq2_dvd⟩, hnq12⟩, hfermat⟩, hgcd1⟩, hgcd2⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hd1 : q1 ∣ p - 1 := pocklington_dvd_sub_one hq1 hq1_dvd hn_lt hfermat hgcd1 hp hp_dvd
  have hd2 : q2 ∣ p - 1 := pocklington_dvd_sub_one hq2 hq2_dvd hn_lt hfermat hgcd2 hp hp_dvd
  rcases hd2 with ⟨k, hk⟩
  have hq1_dvd_prod : q1 ∣ q2 * k := hk ▸ hd1
  rcases hq1.dvd_mul hq1_dvd_prod with hq1_q2 | ⟨m, rfl⟩
  · have := Nat.le_of_dvd hq2.pos hq1_q2; omega
  · have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [Nat.mul_zero, Nat.mul_zero] at hk; have := hp.gt_one; omega
      · exact hpos
    have hq12_le : q1 * q2 ≤ p - 1 := by
      rw [hk, ← Nat.mul_assoc, Nat.mul_comm q2 q1]
      exact Nat.le_mul_of_pos_right (q1 * q2) hm_pos
    have hq12_lt_p : q1 * q2 < p := by have := hp.gt_one; omega
    have hsq_lt : (q1 * q2) * (q1 * q2) < p * p := Nat.mul_lt_mul_of_lt_of_lt hq12_lt_p hq12_lt_p
    omega

/-- Trial division primality check for small primes $n < B^2$. -/
@[expose] def checkSmallPrime (n B : Nat) : Bool :=
  decide (1 < n) && decide (n < B * B) &&
  (List.range' 2 (B - 2)).all (fun k => n % k != 0)

theorem smallPrime_of_check {n B : Nat} (h : checkSmallPrime n B = true) : IsPrime n := by
  unfold checkSmallPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range',
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨hn1, hnB⟩, hall⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hp_lt_B : p < B := by
    apply Classical.byContradiction
    intro hge
    have hB_le : B ≤ p := by omega
    have hB2 : B * B ≤ p * p := Nat.mul_le_mul hB_le hB_le
    omega
  have hp_ge2 : 2 ≤ p := hp.gt_one
  exact hall p ⟨p - 2, by omega, by omega⟩ (Nat.mod_eq_zero_of_dvd hp_dvd)

private theorem prime_97 : IsPrime 97 := smallPrime_of_check (B := 10) (by decide)
private theorem prime_103 : IsPrime 103 := smallPrime_of_check (B := 11) (by decide)
private theorem prime_127 : IsPrime 127 := smallPrime_of_check (B := 12) (by decide)
private theorem prime_419 : IsPrime 419 := smallPrime_of_check (B := 21) (by decide)
private theorem prime_991 : IsPrime 991 := smallPrime_of_check (B := 32) (by decide)
private theorem prime_1723 : IsPrime 1723 := smallPrime_of_check (B := 42) (by decide)
private theorem prime_4153 : IsPrime 4153 := smallPrime_of_check (B := 65) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_430751 : IsPrime 430751 :=
  pocklington1 prime_1723 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_31757755568855353 : IsPrime 31757755568855353 :=
  pocklington2 prime_430751 prime_4153 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_569003 : IsPrime 569003 :=
  pocklington2 prime_419 prime_97 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_2773320623 : IsPrime 2773320623 :=
  pocklington1 prime_569003 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_72106336199 : IsPrime 72106336199 :=
  pocklington1 prime_2773320623 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_8574133 : IsPrime 8574133 :=
  pocklington2 prime_991 prime_103 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_1919519569386763 : IsPrime 1919519569386763 :=
  pocklington2 prime_8574133 prime_127 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_75445702479781427272750846543864801 :
    IsPrime 75445702479781427272750846543864801 :=
  pocklington2 prime_1919519569386763 prime_72106336199 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_p25519_q1 :
    IsPrime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  pocklington2 prime_75445702479781427272750846543864801 prime_31757755568855353 (a := 2) (by decide)

set_option maxRecDepth 20000 in
/-- Primality of $p_{25519} = 2^{255} - 19$, proved via Pocklington's test. -/
theorem p25519_prime : IsPrime p25519 :=
  pocklington1 prime_p25519_q1 (a := 2) (by unfold p25519; decide)

/-! ## 7. Field Inversion, Cancellation, & Euler's Criterion in $\mathbb{F}_{p_{25519}}$ -/

theorem mul_mod_p25519_eq_zero_iff (a b : Nat) :
    (a * b) % p25519 = 0 ↔ a % p25519 = 0 ∨ b % p25519 = 0 :=
  p25519_prime.mul_mod_eq_zero_iff a b

theorem fpMul_eq_zero_iff (a b : Nat) :
    fpMul a b = 0 ↔ a % p25519 = 0 ∨ b % p25519 = 0 := by
  rw [fpMul_eq_mul_mod, mul_mod_p25519_eq_zero_iff]

theorem fpMul_ne_zero {a b : Nat} (ha : a % p25519 ≠ 0) (hb : b % p25519 ≠ 0) :
    fpMul a b ≠ 0 := by
  rw [ne_eq, fpMul_eq_zero_iff]
  rintro (h | h)
  · exact ha h
  · exact hb h

theorem fpSq_eq_zero_iff (a : Nat) : fpSq a = 0 ↔ a % p25519 = 0 := by
  unfold fpSq; rw [fpMul_eq_zero_iff, or_self]

theorem pow_p25519_sub_one_mod {a : Nat} (ha : a % p25519 ≠ 0) :
    a ^ (p25519 - 1) % p25519 = 1 :=
  p25519_prime.pow_sub_one_mod ha

theorem fpPow_p25519_sub_one {a : Nat} (ha : a % p25519 ≠ 0) :
    fpPow a (p25519 - 1) = 1 := by
  rw [fpPow_eq_pow_mod a (p25519 - 1) (by unfold p25519; decide), pow_p25519_sub_one_mod ha]

set_option maxRecDepth 20000 in
@[simp] theorem fpInv_zero : fpInv 0 = 0 := by unfold fpInv fpPow modPow p25519; decide
set_option maxRecDepth 20000 in
@[simp] theorem fpInv_one : fpInv 1 = 1 := by unfold fpInv fpPow modPow p25519; decide

/-- Multiplicative inverse in $\mathbb{F}_{p_{25519}}$: `a * a^(p - 2) ≡ 1 (mod p)` for `a % p ≠ 0`. -/
theorem fpMul_fpInv_cancel {a : Nat} (ha : a % p25519 ≠ 0) : fpMul a (fpInv a) = 1 := by
  rw [fpMul_comm, fpMul_eq_mul_mod, fpInv_eq_pow_mod, Nat.mod_mul_mod, ← Nat.pow_succ,
      show (p25519 - 2).succ = p25519 - 1 by unfold p25519; decide]
  exact pow_p25519_sub_one_mod ha

theorem fpInv_fpMul_cancel {a : Nat} (ha : a % p25519 ≠ 0) : fpMul (fpInv a) a = 1 := by
  rw [fpMul_comm, fpMul_fpInv_cancel ha]

theorem fpInv_ne_zero {a : Nat} (ha : a % p25519 ≠ 0) : fpInv a ≠ 0 := by
  intro h0
  have h1 := fpMul_fpInv_cancel ha
  rw [h0, fpMul_zero] at h1
  exact absurd h1 (by decide)

theorem fpMul_cancel_right {a b c : Nat} (hc : c % p25519 ≠ 0) :
    fpMul a c = fpMul b c ↔ a % p25519 = b % p25519 := by
  constructor
  · intro h
    have h1 := congrArg (fun x => fpMul x (fpInv c)) h
    rw [fpMul_assoc, fpMul_assoc, fpMul_fpInv_cancel hc, fpMul_one, fpMul_one] at h1
    exact h1
  · intro h; rw [← fpMul_mod_left a, ← fpMul_mod_left b, h]

theorem fpMul_cancel_left {a b c : Nat} (ha : a % p25519 ≠ 0) :
    fpMul a b = fpMul a c ↔ b % p25519 = c % p25519 := by
  rw [fpMul_comm a b, fpMul_comm a c, fpMul_cancel_right ha]

theorem fpInv_eq_of_fpMul_eq_one {a b : Nat} (h : fpMul a b = 1) :
    fpInv a = b % p25519 := by
  have ha : a % p25519 ≠ 0 := by
    intro h0; rw [← fpMul_mod_left, h0, zero_fpMul] at h; exact absurd h (by decide)
  have h1 : fpMul a (fpInv a) = fpMul a b := by rw [fpMul_fpInv_cancel ha, h]
  rw [← (fpMul_cancel_left ha).mp h1, fpInv_mod_p]

theorem fpInv_fpMul (a b : Nat) : fpInv (fpMul a b) = fpMul (fpInv a) (fpInv b) := by
  by_cases ha : a % p25519 = 0
  · rw [← fpMul_mod_left a, ← fpInv_mod a, ha, zero_fpMul, fpInv_zero, zero_fpMul]
  · by_cases hb : b % p25519 = 0
    · rw [← fpMul_mod_right _ b, ← fpInv_mod b, hb, fpMul_zero, fpInv_zero, fpMul_zero]
    · refine (fpInv_eq_of_fpMul_eq_one ?_).trans (fpMul_mod_p _ _)
      rw [fpMul_assoc, ← fpMul_assoc b (fpInv a) (fpInv b), fpMul_comm b (fpInv a),
          fpMul_assoc (fpInv a) b (fpInv b), fpMul_fpInv_cancel hb, fpMul_one,
          fpInv_mod_p, fpMul_fpInv_cancel ha]

theorem fpSq_eq_fpSq_iff (a b : Nat) :
    fpSq a = fpSq b ↔ a % p25519 = b % p25519 ∨ a % p25519 = fpNeg b := by
  have h1 : fpSq a = fpSq b ↔ fpSq a % p25519 = fpSq b % p25519 := by
    rw [fpSq_mod_p, fpSq_mod_p]
  have h2 : fpAdd a b = fpSub a (fpNeg b) := by
    rw [fpSub_eq_fpAdd_fpNeg, fpNeg_fpNeg, fpAdd_mod_right]
  rw [h1, ← fpSub_eq_zero_iff (fpSq a) (fpSq b), fpSub_fpSq, fpMul_eq_zero_iff,
      fpSub_mod_p, fpAdd_mod_p, fpSub_eq_zero_iff, h2, fpSub_eq_zero_iff, fpNeg_mod_p]

/-- Euler's non-square criterion: if $d^{(p - 1)/2} \equiv p - 1 \pmod p$, then $d$ has no
    square root in $\mathbb{F}_p$. -/
theorem euler_nonsquare {d : Nat} (hd : fpPow d ((p25519 - 1) / 2) = p25519 - 1) :
    ¬ ∃ r : Nat, fpSq r = d % p25519 := by
  rintro ⟨r, hr⟩
  have he_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide
  have hmul2 : 2 * ((p25519 - 1) / 2) = p25519 - 1 := by unfold p25519; decide
  rw [← fpPow_mod_left d, ← hr, fpPow_eq_pow_mod _ _ he_lt, fpSq_eq_pow2_mod,
      ← Nat.pow_mod, ← Nat.pow_mul, hmul2] at hd
  by_cases hr0 : r % p25519 = 0
  · have h0 : r ^ (p25519 - 1) % p25519 = 0 :=
      (p25519_prime.pow_mod_eq_zero_iff r (p25519 - 1) (by unfold p25519; decide)).mpr hr0
    rw [h0] at hd; revert hd; unfold p25519; decide
  · rw [pow_p25519_sub_one_mod hr0] at hd; revert hd; unfold p25519; decide

set_option maxRecDepth 20000 in
/-- `edD` is a non-square in $\mathbb{F}_{p_{25519}}$ (`edD^((p-1)/2) = p - 1`). -/
theorem edD_euler : fpPow edD ((p25519 - 1) / 2) = p25519 - 1 := by
  unfold fpPow modPow edD p25519; decide

theorem edD_nonsquare : ¬ ∃ r : Nat, fpSq r = edD := by
  rw [← edD_mod_p]; exact euler_nonsquare edD_euler

/-- `sqrtM1^2 ≡ -1 (mod p25519)`. -/
theorem fpSq_sqrtM1 : fpSq sqrtM1 = p25519 - 1 := by
  unfold fpSq fpMul sqrtM1 p25519; decide

theorem fpSq_sqrtM1_eq_fpNeg_one : fpSq sqrtM1 = fpNeg 1 := by
  unfold fpSq fpMul fpNeg sqrtM1 p25519; decide

/-! ## 8. Non-Vanishing Twisted Edwards Denominators & `recoverXEven` Correctness -/

theorem fpAdd_eq_zero_iff (a b : Nat) : fpAdd a b = 0 ↔ a % p25519 = fpNeg b := by
  have h : fpAdd a b = fpSub a (fpNeg b) := by
    rw [fpSub_eq_fpAdd_fpNeg, fpNeg_fpNeg, fpAdd_mod_right]
  rw [h, fpSub_eq_zero_iff, fpNeg_mod_p]

/-- For any $z$, $1 - d z^2 \not\equiv 0 \pmod{p_{25519}}$ because $d$ is a non-square. -/
theorem fpSub_one_edD_fpSq_ne_zero (z : Nat) : fpSub 1 (fpMul edD (fpSq z)) ≠ 0 := by
  intro h
  have h1 : fpMul edD (fpSq z) = 1 := by
    have := (fpSub_eq_zero_iff 1 (fpMul edD (fpSq z))).mp h
    rw [fpMul_mod_p] at this
    exact this.symm.trans (by unfold p25519; decide)
  have hz : z % p25519 ≠ 0 := by
    intro hz0
    rw [← fpSq_mod z, hz0, fpSq_zero, fpMul_zero] at h1
    exact absurd h1 (by decide)
  have h2 : fpSq (fpInv z) = edD := by
    have hmul := congrArg (fun t => fpMul t (fpSq (fpInv z))) h1
    rw [one_fpMul, fpSq_mod_p, fpMul_assoc, ← fpSq_fpMul, fpMul_fpInv_cancel hz,
        fpSq_one, fpMul_one, edD_mod_p] at hmul
    exact hmul.symm
  exact edD_nonsquare ⟨fpInv z, h2⟩

/-- For any $z$, $1 + d z^2 \not\equiv 0 \pmod{p_{25519}}$ because $d$ is a non-square and $-1 = (\sqrt{-1})^2$. -/
theorem fpAdd_one_edD_fpSq_ne_zero (z : Nat) : fpAdd 1 (fpMul edD (fpSq z)) ≠ 0 := by
  intro h
  have h1 : fpMul edD (fpSq z) = fpSq sqrtM1 := by
    rw [fpAdd_comm] at h
    have := (fpAdd_eq_zero_iff (fpMul edD (fpSq z)) 1).mp h
    rw [fpMul_mod_p, ← fpSq_sqrtM1_eq_fpNeg_one] at this
    exact this
  have hz : z % p25519 ≠ 0 := by
    intro hz0
    rw [← fpSq_mod z, hz0, fpSq_zero, fpMul_zero, fpSq_sqrtM1] at h1
    revert h1; unfold p25519; decide
  have h2 : fpSq (fpMul sqrtM1 (fpInv z)) = edD := by
    have hmul := congrArg (fun t => fpMul t (fpSq (fpInv z))) h1
    rw [← fpSq_fpMul sqrtM1 (fpInv z), fpMul_assoc, ← fpSq_fpMul z (fpInv z),
        fpMul_fpInv_cancel hz, fpSq_one, fpMul_one, edD_mod_p] at hmul
    exact hmul.symm
  exact edD_nonsquare ⟨fpMul sqrtM1 (fpInv z), h2⟩

theorem p25519_mod_two : p25519 % 2 = 1 := by unfold p25519; decide

theorem fpNeg_mod_two_of_ne_zero {a : Nat} (ha : a % p25519 ≠ 0) :
    (fpNeg a) % 2 = 1 - (a % p25519) % 2 := by
  have hlt : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  have hp2 : p25519 % 2 = 1 := p25519_mod_two
  rw [fpNeg_of_mod_ne_zero ha]
  omega

/-- Canonical even representative in $[0, p)$ of $\pm r \bmod p$. -/
@[expose] def fpEvenRep (r : Nat) : Nat :=
  if (r % p25519) % 2 == 1 then fpNeg r else r % p25519

theorem fpEvenRep_of_lt {r : Nat} (hr : r < p25519) :
    (if r % 2 == 1 then fpNeg r else r) = fpEvenRep r := by
  unfold fpEvenRep
  rw [Nat.mod_eq_of_lt hr]

theorem fpEvenRep_lt (r : Nat) : fpEvenRep r < p25519 := by
  unfold fpEvenRep
  split
  · exact fpNeg_lt r
  · exact Nat.mod_lt r p25519_pos

theorem fpEvenRep_mod_p (r : Nat) : (fpEvenRep r) % p25519 = fpEvenRep r :=
  Nat.mod_eq_of_lt (fpEvenRep_lt r)

theorem fpEvenRep_mod_two (r : Nat) : (fpEvenRep r) % 2 = 0 := by
  unfold fpEvenRep
  split
  · next h =>
    have h1 : (r % p25519) % 2 = 1 := beq_iff_eq.mp h
    have hne : r % p25519 ≠ 0 := by omega
    rw [fpNeg_mod_two_of_ne_zero hne, h1]
  · next h =>
    have h1 : (r % p25519) % 2 ≠ 1 := fun heq => h (beq_iff_eq.mpr heq)
    omega

theorem fpSq_fpEvenRep (r : Nat) : fpSq (fpEvenRep r) = fpSq r := by
  unfold fpEvenRep
  split
  · exact fpSq_fpNeg r
  · exact fpSq_mod r

theorem eq_of_fpSq_eq_of_even {a b : Nat} (ha : a < p25519) (hb : b < p25519)
    (ha2 : a % 2 = 0) (hb2 : b % 2 = 0) (hsq : fpSq a = fpSq b) : a = b := by
  have ha_mod : a % p25519 = a := Nat.mod_eq_of_lt ha
  have hb_mod : b % p25519 = b := Nat.mod_eq_of_lt hb
  rcases (fpSq_eq_fpSq_iff a b).mp hsq with h | h
  · rw [ha_mod, hb_mod] at h; exact h
  · rw [ha_mod] at h
    by_cases hb0 : b = 0
    · subst hb0; rw [fpNeg_zero] at h; exact h
    · have hb_ne : b % p25519 ≠ 0 := by rw [hb_mod]; exact hb0
      have hpar := congrArg (· % 2) h
      rw [ha2, fpNeg_mod_two_of_ne_zero hb_ne, hb_mod, hb2] at hpar
      omega

theorem fpEvenRep_eq_of_fpSq_eq {r x : Nat} (hsq : fpSq r = fpSq x) :
    fpEvenRep r = fpEvenRep x :=
  eq_of_fpSq_eq_of_even (fpEvenRep_lt r) (fpEvenRep_lt x)
    (fpEvenRep_mod_two r) (fpEvenRep_mod_two x)
    (by rw [fpSq_fpEvenRep, fpSq_fpEvenRep, hsq])

theorem fpEvenRep_eq_zero_iff {x : Nat} (hx : x < p25519) :
    fpEvenRep x = 0 ↔ x = 0 := by
  have hsq : fpSq (fpEvenRep x) = fpSq x := fpSq_fpEvenRep x
  constructor
  · intro h0
    rw [h0, fpSq_zero] at hsq
    have hx0 := (fpSq_eq_zero_iff x).mp hsq.symm
    rwa [Nat.mod_eq_of_lt hx] at hx0
  · rintro rfl
    unfold fpEvenRep; simp

theorem restore_sign_fpEvenRep {x : Nat} (hx : x < p25519) :
    (if x % 2 == 1 then fpNeg (fpEvenRep x) else fpEvenRep x) = x := by
  rw [← fpEvenRep_of_lt hx]
  cases x % 2 == 1 <;> simp [Nat.mod_eq_of_lt hx]

/-- If $(x, y)$ satisfies $(d y^2 + 1) x^2 \equiv y^2 - 1 \pmod{p_{25519}}$, then
    `recoverXEven y = some (fpEvenRep x)`. -/
theorem recoverXEven_of_curve_eq {x y : Nat}
    (hcurve : fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq x) = fpSub (fpSq y) 1) :
    recoverXEven y = some (fpEvenRep x) := by
  unfold recoverXEven
  dsimp only []
  let y2 := fpSq y
  let u := fpSub y2 1
  let v := fpAdd (fpMul edD y2) 1
  let v3 := fpMul (fpSq v) v
  let v7 := fpMul (fpSq v3) v
  let r0 := fpMul (fpMul u v3) (fpPow (fpMul u v7) ((p25519 - 5) / 8))
  let check := fpMul v (fpSq r0)
  change (if (check == u) = true then some (if (r0 % 2 == 1) = true then fpNeg r0 else r0)
    else if (check == fpNeg u) = true then
      let r1 := fpMul r0 sqrtM1
      some (if (r1 % 2 == 1) = true then fpNeg r1 else r1)
    else none) = some (fpEvenRep x)
  have hv_ne0 : v ≠ 0 := by
    dsimp only [v, y2]
    rw [fpAdd_comm]
    exact fpAdd_one_edD_fpSq_ne_zero y
  have hv : v % p25519 ≠ 0 := by
    rw [Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact hv_ne0
  have hu_mod : u % p25519 = u := Nat.mod_eq_of_lt (fpSub_lt _ _)
  have hu_eq : u = fpMul v (fpSq x) := hcurve.symm
  have h_branch1 (hchk : check = u) :
      (if r0 % 2 == 1 then fpNeg r0 else r0) = fpEvenRep x := by
    rw [fpEvenRep_of_lt (fpMul_lt _ _)]
    apply fpEvenRep_eq_of_fpSq_eq
    have h1 : fpMul v (fpSq r0) = fpMul v (fpSq x) := hchk.trans hu_eq
    have h2 := (fpMul_cancel_left hv).mp h1
    rwa [fpSq_mod_p, fpSq_mod_p] at h2
  have h_branch2 (hchk : check = fpNeg u) :
      (if (fpMul r0 sqrtM1) % 2 == 1 then fpNeg (fpMul r0 sqrtM1) else fpMul r0 sqrtM1) =
        fpEvenRep x := by
    rw [fpEvenRep_of_lt (fpMul_lt _ _)]
    apply fpEvenRep_eq_of_fpSq_eq
    have h1 : fpMul v (fpSq (fpMul r0 sqrtM1)) = fpMul v (fpSq x) := by
      rw [fpSq_fpMul, ← fpMul_assoc, show fpMul v (fpSq r0) = check from rfl,
          hchk, fpSq_sqrtM1_eq_fpNeg_one, fpNeg_fpMul_fpNeg, fpMul_one, hu_mod, hu_eq]
    have h2 := (fpMul_cancel_left hv).mp h1
    rwa [fpSq_mod_p, fpSq_mod_p] at h2
  have h_check_or : check = u ∨ check = fpNeg u := by
    have h_check_eq :
        check = fpMul u (fpMul (fpMul u v7) (fpSq (fpPow (fpMul u v7) ((p25519 - 5) / 8)))) := by
      dsimp only [check, r0, v7, v3]
      rw [fpSq_fpMul, ← fpMul_assoc v, fpSq_fpMul u v3,
          ← fpMul_assoc v (fpSq u) (fpSq v3), fpMul_comm v (fpSq u), fpMul_assoc (fpSq u) v (fpSq v3),
          fpMul_comm v (fpSq v3),
          show fpSq u = fpMul u u from rfl,
          fpMul_assoc u u (fpMul (fpSq v3) v),
          fpMul_assoc u (fpMul u (fpMul (fpSq v3) v))]
    let z := fpMul x (fpMul v3 v)
    have hw_sq : fpMul u v7 = fpSq z := by
      dsimp only [z]
      rw [hu_eq, fpSq_fpMul x (fpMul v3 v), fpSq_fpMul v3 v]
      dsimp only [v7]
      rw [show fpSq v = fpMul v v from rfl,
          ← fpMul_assoc (fpSq v3) v v,
          ← fpMul_assoc (fpSq x) (fpMul (fpSq v3) v) v,
          fpMul_comm (fpMul (fpSq x) (fpMul (fpSq v3) v)) v,
          ← fpMul_assoc v (fpSq x) (fpMul (fpSq v3) v)]
    let s := fpMul (fpSq z) (fpSq (fpPow (fpSq z) ((p25519 - 5) / 8)))
    have h_check_s : check = fpMul u s := by
      rw [h_check_eq, hw_sq]
    by_cases hz0 : z % p25519 = 0
    · left
      have hsqz0 : fpSq z = 0 := (fpSq_eq_zero_iff z).mpr hz0
      have hs0 : s = 0 := by dsimp only [s]; rw [hsqz0, zero_fpMul]
      have hx0 : x % p25519 = 0 := by
        have hzv0 : z % p25519 = 0 := hz0
        rw [Nat.mod_eq_of_lt (fpMul_lt _ _)] at hzv0
        rcases (fpMul_eq_zero_iff x (fpMul v3 v)).mp hzv0 with hx0 | hv3v0
        · exact hx0
        · rw [Nat.mod_eq_of_lt (fpMul_lt _ _)] at hv3v0
          rcases (fpMul_eq_zero_iff v3 v).mp hv3v0 with hv30 | hv0
          · rw [Nat.mod_eq_of_lt (fpMul_lt _ _)] at hv30
            rcases (fpMul_eq_zero_iff (fpSq v) v).mp hv30 with hv20 | hv0
            · rw [Nat.mod_eq_of_lt (fpSq_lt _)] at hv20
              exact absurd ((fpSq_eq_zero_iff v).mp hv20) hv
            · exact absurd hv0 hv
          · exact absurd hv0 hv
      have hu0 : u = 0 := by
        rw [hu_eq, ← fpSq_mod x, hx0, fpSq_zero, fpMul_zero]
      rw [h_check_s, hs0, fpMul_zero, hu0]
    · have hk_lt : (p25519 - 5) / 8 < 2 ^ 256 := by unfold p25519; decide
      have hexp : 2 + 2 * ((p25519 - 5) / 8 * 2) = (p25519 - 1) / 2 := by unfold p25519; decide
      have hexp2 : (p25519 - 1) / 2 * 2 = p25519 - 1 := by unfold p25519; decide
      have hs_pow : s = z ^ ((p25519 - 1) / 2) % p25519 := by
        dsimp only [s]
        rw [fpPow_eq_pow_mod _ _ hk_lt, fpSq_mod, fpSq_eq_pow2_mod (fpSq z ^ _),
            fpSq_eq_pow2_mod z, ← Nat.pow_mul, ← Nat.pow_mod, ← Nat.pow_mul,
            fpMul_eq_mul_mod, Nat.mod_mul_mod, Nat.mul_mod_mod, ← Nat.pow_add, hexp]
      have hsq_s : fpSq s = fpSq 1 := by
        rw [hs_pow, fpSq_mod, fpSq_eq_pow2_mod, ← Nat.pow_mul, hexp2,
            pow_p25519_sub_one_mod hz0, fpSq_one]
      rcases (fpSq_eq_fpSq_iff s 1).mp hsq_s with hs1 | hs_neg1
      · left
        rw [h_check_s, ← fpMul_mod_right u s, hs1, fpMul_mod_right, fpMul_one, hu_mod]
      · right
        rw [h_check_s, ← fpMul_mod_right u s, hs_neg1, fpMul_fpNeg, fpMul_one, fpNeg_mod]
  cases h1 : check == u
  · rcases h_check_or with h_eq | h_neg
    · exact absurd (beq_iff_eq.mpr h_eq) (by simp [h1])
    · have h2 : (check == fpNeg u) = true := beq_iff_eq.mpr h_neg
      rw [h2]
      exact congrArg some (h_branch2 h_neg)
  · exact congrArg some (h_branch1 (beq_iff_eq.mp h1))

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
