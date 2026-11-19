/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec -- proof-setup: allow-public-import

/-!
# Subgroup prime orders and group-exponent divisibility

Defines the quadratic-twist subgroup order and proves primality of the Curve25519 subgroup
orders:

1. Prime subgroup order $\ell' = \text{twistOrderL}$ of the quadratic twist $E'(\mathbb{F}_p)$
   and the Hasse–Weil cardinality identity $8\ell + 4\ell' = 2(p_{25519} + 1)$.
2. Pocklington primality proofs `edOrderL_prime : IsPrime edOrderL` and
   `twistOrderL_prime : IsPrime twistOrderL` (witness $a = 2$).
3. Pure-`Nat` Euclidean closure (`nat_pred_gcd`) and cofactor-prime divisibility / GCD lemmas
   for cyclic group order determination and clamped-scalar torsion elimination.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality

open VerifiedLibraries.Common (
  p25519 edOrderL)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  IsPrime pocklington1 pocklington2 smallPrime_of_check)
/-! ## 1. Quadratic-Twist Subgroup Order `twistOrderL` & Basic Arithmetic Bounds -/

/-- Prime subgroup order $\ell'$ of the Curve25519 quadratic twist $E'(\mathbb{F}_p)$,
    satisfying $|E'(\mathbb{F}_p)| = 4 \ell'$ and $8 \ell + 4 \ell' = 2(p_{25519} + 1)$. -/
@[expose] def twistOrderL : Nat :=
  14474011154664524427946373126085988481603263447650325797860494125407373907997

theorem twistOrderL_pos : 0 < twistOrderL := by
  decide

theorem twistOrderL_gt_one : 1 < twistOrderL := by
  decide

theorem edOrderL_odd : edOrderL % 2 = 1 := by
  decide

theorem twistOrderL_odd : twistOrderL % 2 = 1 := by
  decide

theorem two_pow_252_lt_edOrderL : 2 ^ 252 < edOrderL := by
  decide

theorem two_pow_252_lt_twistOrderL : 2 ^ 252 < twistOrderL := by
  decide

theorem eight_mul_edOrderL_lt_two_pow_256 : 8 * edOrderL < 2 ^ 256 := by
  decide

theorem four_mul_twistOrderL_lt_two_pow_256 : 4 * twistOrderL < 2 ^ 256 := by
  decide

/-- Exact Hasse–Weil trace cancellation between $E(\mathbb{F}_p)$ ($8\ell$) and its quadratic twist
    $E'(\mathbb{F}_p)$ ($4\ell'$): $8\ell + 4\ell' = 2(p_{25519} + 1)$. -/
theorem curve_twist_card_sum : 8 * edOrderL + 4 * twistOrderL = 2 * (p25519 + 1) := by
  decide

/-! ## 2. Certified Pocklington Primality of `edOrderL` ($\ell$) -/

private theorem prime_2551 : IsPrime 2551 :=
  smallPrime_of_check (B := 51) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_531581 : IsPrime 531581 :=
  smallPrime_of_check (B := 730) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q1 : IsPrime 1224481 :=
  pocklington1 prime_2551 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q2 : IsPrime 1257559732178653 :=
  pocklington2 prime_ed_q1 prime_531581 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q3 : IsPrime 4434155615661930479 :=
  pocklington1 prime_ed_q2 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q4 : IsPrime 172054593956031949258510691 :=
  pocklington1 prime_ed_q3 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q5 : IsPrime 19757330305831588566944191468367130476339 :=
  pocklington1 prime_ed_q4 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_ed_q6 : IsPrime 276602624281642239937218680557139826668747 :=
  pocklington1 prime_ed_q5 (a := 2) (by decide)

set_option maxRecDepth 20000 in
/-- Primality of $\ell = \text{edOrderL}$, proved via Pocklington's test. -/
theorem edOrderL_prime : IsPrime edOrderL :=
  pocklington1 prime_ed_q6 (a := 2) (by unfold edOrderL; decide)

/-! ## 3. Certified Pocklington Primality of `twistOrderL` ($\ell'$) -/

private theorem prime_8053 : IsPrime 8053 :=
  smallPrime_of_check (B := 90) (by decide)

private theorem prime_3911 : IsPrime 3911 :=
  smallPrime_of_check (B := 63) (by decide)

private theorem prime_28859 : IsPrime 28859 :=
  smallPrime_of_check (B := 170) (by decide)

private theorem prime_2281 : IsPrime 2281 :=
  smallPrime_of_check (B := 48) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q1 : IsPrime 1013266244677 :=
  pocklington2 prime_8053 prime_3911 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q2 : IsPrime 5171003929967 :=
  pocklington2 prime_28859 prime_2281 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q3 : IsPrime 22561162540501040539 :=
  pocklington1 prime_tw_q2 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q4 : IsPrime 203852586375664218368381551393371968928013 :=
  pocklington2 prime_tw_q3 prime_tw_q1 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q5 : IsPrime 104719073621178708975837602950775180438320278101 :=
  pocklington1 prime_tw_q4 (a := 2) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_tw_q6 : IsPrime 27413359092552162435694767700453926735143482401279781 :=
  pocklington1 prime_tw_q5 (a := 2) (by decide)

set_option maxRecDepth 20000 in
/-- Primality of $\ell' = \text{twistOrderL}$, proved via Pocklington's test. -/
theorem twistOrderL_prime : IsPrime twistOrderL :=
  pocklington1 prime_tw_q6 (a := 2) (by unfold twistOrderL; decide)

/-! ## 4. Euclidean Kernel Closure & Cofactor-Prime Divisibility / GCD Lemmas -/

private theorem nat_pred_mod {P : Nat → Prop}
    (hsub : ∀ a b, a ≤ b → P a → P b → P (b - a))
    (a : Nat) (ha : P a) : ∀ b, P b → P (b % a) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb
    by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · by_cases hlt : b < a
      · rwa [Nat.mod_eq_of_lt hlt]
      · have hle : a ≤ b := by omega
        rw [Nat.mod_eq_sub_mod hle]
        exact ih (b - a) (by omega) (hsub a b hle ha hb)

/-- Pure-`Nat` Euclidean closure: any predicate `P : Nat → Prop` closed under `0` and
    subtraction `b - a` (`a ≤ b`) is closed under `Nat.gcd`. -/
theorem nat_pred_gcd {P : Nat → Prop}
    (hsub : ∀ a b, a ≤ b → P a → P b → P (b - a)) :
    ∀ a b, P a → P b → P (Nat.gcd a b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb
    by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · rw [Nat.gcd_rec a b]
      have hmod_lt : b % a < a := Nat.mod_lt b (by omega)
      exact ih (b % a) hmod_lt a (nat_pred_mod hsub a ha b hb) ha

/-- Proper divisors of $8p$ (for prime $p$) divide either $4p$ or $8$. -/
theorem dvd_four_mul_or_dvd_eight_of_dvd_eight_mul_prime {p d : Nat}
    (hp : IsPrime p) (hdvd : d ∣ 8 * p) (hlt : d < 8 * p) :
    d ∣ 4 * p ∨ d ∣ 8 := by
  rcases hdvd with ⟨q, hq⟩
  have hp_pos : 0 < p := hp.pos
  have hq_ge2 : 2 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0; omega
    · by_cases hq1 : q = 1
      · subst hq1; omega
      · omega
  have hp_dvd_prod : p ∣ d * q := ⟨8, by omega⟩
  rcases hp.dvd_mul hp_dvd_prod with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · left
    have hmq : m * q = 8 := by
      have : p * (m * q) = p * 8 := by rw [← Nat.mul_assoc, ← hq, Nat.mul_comm 8 p]
      exact Nat.eq_of_mul_eq_mul_left hp_pos this
    have hm_dvd4 : m ∣ 4 := by
      by_cases hm1 : m = 1
      · subst hm1; exact ⟨4, by omega⟩
      · by_cases hm2 : m = 2
        · subst hm2; exact ⟨2, by omega⟩
        · by_cases hm4 : m = 4
          · subst hm4; exact ⟨1, by omega⟩
          · exfalso
            have hm0 : m ≠ 0 := by intro h0; subst h0; omega
            have hm3 : m ≠ 3 := by intro h3; subst h3; omega
            have hm_ge5 : 5 ≤ m := by omega
            have : 10 ≤ m * q := Nat.mul_le_mul hm_ge5 hq_ge2
            omega
    rcases hm_dvd4 with ⟨c, hc⟩
    exact ⟨c, by rw [Nat.mul_comm 4 p, hc, Nat.mul_assoc]⟩
  · right
    have hdk : d * k = 8 := by
      have : p * (d * k) = p * 8 := by
        calc p * (d * k) = d * (p * k) := by rw [← Nat.mul_assoc, Nat.mul_comm p d, Nat.mul_assoc]
        _ = 8 * p := hq.symm
        _ = p * 8 := Nat.mul_comm 8 p
      exact Nat.eq_of_mul_eq_mul_left hp_pos this
    exact ⟨k, hdk.symm⟩

/-- Proper divisors of $4p$ (for prime $p$) divide either $2p$ or $4$. -/
theorem dvd_two_mul_or_dvd_four_of_dvd_four_mul_prime {p d : Nat}
    (hp : IsPrime p) (hdvd : d ∣ 4 * p) (hlt : d < 4 * p) :
    d ∣ 2 * p ∨ d ∣ 4 := by
  rcases hdvd with ⟨q, hq⟩
  have hp_pos : 0 < p := hp.pos
  have hq_ge2 : 2 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0; omega
    · by_cases hq1 : q = 1
      · subst hq1; omega
      · omega
  have hp_dvd_prod : p ∣ d * q := ⟨4, by omega⟩
  rcases hp.dvd_mul hp_dvd_prod with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · left
    have hmq : m * q = 4 := by
      have : p * (m * q) = p * 4 := by rw [← Nat.mul_assoc, ← hq, Nat.mul_comm 4 p]
      exact Nat.eq_of_mul_eq_mul_left hp_pos this
    have hm_dvd2 : m ∣ 2 := by
      by_cases hm1 : m = 1
      · subst hm1; exact ⟨2, by omega⟩
      · by_cases hm2 : m = 2
        · subst hm2; exact ⟨1, by omega⟩
        · exfalso
          have hm0 : m ≠ 0 := by intro h0; subst h0; omega
          have hm_ge3 : 3 ≤ m := by omega
          have : 6 ≤ m * q := Nat.mul_le_mul hm_ge3 hq_ge2
          omega
    rcases hm_dvd2 with ⟨c, hc⟩
    exact ⟨c, by rw [Nat.mul_comm 2 p, hc, Nat.mul_assoc]⟩
  · right
    have hdk : d * k = 4 := by
      have : p * (d * k) = p * 4 := by
        calc p * (d * k) = d * (p * k) := by rw [← Nat.mul_assoc, Nat.mul_comm p d, Nat.mul_assoc]
        _ = 4 * p := hq.symm
        _ = p * 4 := Nat.mul_comm 4 p
      exact Nat.eq_of_mul_eq_mul_left hp_pos this
    exact ⟨k, hdk.symm⟩

/-- If $p$ is an odd prime and $0 < m < p$, then $p \nmid 2^j \cdot m$ for every $j$. -/
theorem odd_prime_not_dvd_two_pow_mul {p m : Nat}
    (hp : IsPrime p) (hodd : p % 2 = 1) (hm0 : 0 < m) (hmp : m < p) :
    ∀ j : Nat, ¬ (p ∣ 2 ^ j * m) := by
  intro j
  induction j with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    intro hdvd
    have hle : p ≤ m := Nat.le_of_dvd hm0 hdvd
    omega
  | succ j ih =>
    intro hdvd
    have hdvd' : p ∣ 2 * (2 ^ j * m) := by
      have heq : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
      rwa [← heq]
    rcases hp.dvd_mul hdvd' with hp2 | hrest
    · have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by omega) hp2
      have hp_gt1 : 1 < p := hp.gt_one
      omega
    · exact ih hrest

/-- For an odd prime $p$ and $0 < m < p$, $\gcd(16 m, p) = 1$. -/
theorem gcd_sixteen_mul_odd_prime {p m : Nat}
    (hp : IsPrime p) (hodd : p % 2 = 1) (hm0 : 0 < m) (hmp : m < p) :
    Nat.gcd (16 * m) p = 1 := by
  have hdvd_p : Nat.gcd (16 * m) p ∣ p := Nat.gcd_dvd_right (16 * m) p
  rcases hp.2 _ hdvd_p with h1 | hp_eq
  · exact h1
  · exfalso
    have hdvd_16m : p ∣ 16 * m := hp_eq ▸ Nat.gcd_dvd_left (16 * m) p
    have hdvd_pow : p ∣ 2 ^ 4 * m := by simpa using hdvd_16m
    exact odd_prime_not_dvd_two_pow_mul hp hodd hm0 hmp 4 hdvd_pow

/-- For an odd prime $p$ and $0 < m < p$, $\gcd(16 m, 8 p) = 8$. -/
theorem gcd_sixteen_mul_eight_mul_odd_prime {p m : Nat}
    (hp : IsPrime p) (hodd : p % 2 = 1) (hm0 : 0 < m) (hmp : m < p) :
    Nat.gcd (16 * m) (8 * p) = 8 := by
  have h8_dvd_gcd : 8 ∣ Nat.gcd (16 * m) (8 * p) :=
    Nat.dvd_gcd ⟨2 * m, by omega⟩ ⟨p, by omega⟩
  rcases h8_dvd_gcd with ⟨d, hg⟩
  have hd_dvd_p : d ∣ p := by
    have h1 : 8 * d ∣ 8 * p := hg ▸ Nat.gcd_dvd_right (16 * m) (8 * p)
    rcases h1 with ⟨k, hk⟩
    exact ⟨k, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) (by rw [← Nat.mul_assoc]; exact hk)⟩
  rcases hp.2 d hd_dvd_p with hd1 | hdp
  · omega
  · exfalso
    subst hdp
    have h2 : 8 * d ∣ 16 * m := hg ▸ Nat.gcd_dvd_left (16 * m) (8 * d)
    rcases h2 with ⟨k, hk⟩
    have hp_dvd_2m : d ∣ 2 ^ 1 * m :=
      ⟨k, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) (by
        calc 8 * (2 ^ 1 * m) = 16 * m := by omega
        _ = 8 * d * k := hk
        _ = 8 * (d * k) := Nat.mul_assoc 8 d k)⟩
    exact odd_prime_not_dvd_two_pow_mul hp hodd hm0 hmp 1 hp_dvd_2m

/-- For an odd prime $p$ and $0 < m < p$, $\gcd(16 m, 4 p) = 4$. -/
theorem gcd_sixteen_mul_four_mul_odd_prime {p m : Nat}
    (hp : IsPrime p) (hodd : p % 2 = 1) (hm0 : 0 < m) (hmp : m < p) :
    Nat.gcd (16 * m) (4 * p) = 4 := by
  have h4_dvd_gcd : 4 ∣ Nat.gcd (16 * m) (4 * p) :=
    Nat.dvd_gcd ⟨4 * m, by omega⟩ ⟨p, by omega⟩
  rcases h4_dvd_gcd with ⟨d, hg⟩
  have hd_dvd_p : d ∣ p := by
    have h1 : 4 * d ∣ 4 * p := hg ▸ Nat.gcd_dvd_right (16 * m) (4 * p)
    rcases h1 with ⟨k, hk⟩
    exact ⟨k, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) (by rw [← Nat.mul_assoc]; exact hk)⟩
  rcases hp.2 d hd_dvd_p with hd1 | hdp
  · omega
  · exfalso
    subst hdp
    have h2 : 4 * d ∣ 16 * m := hg ▸ Nat.gcd_dvd_left (16 * m) (4 * d)
    rcases h2 with ⟨k, hk⟩
    have hp_dvd_4m : d ∣ 2 ^ 2 * m :=
      ⟨k, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) (by
        calc 4 * (2 ^ 2 * m) = 16 * m := by omega
        _ = 4 * d * k := hk
        _ = 4 * (d * k) := Nat.mul_assoc 4 d k)⟩
    exact odd_prime_not_dvd_two_pow_mul hp hodd hm0 hmp 2 hp_dvd_4m

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality
