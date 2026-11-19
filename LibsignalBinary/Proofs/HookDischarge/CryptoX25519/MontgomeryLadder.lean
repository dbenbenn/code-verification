/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec

/-!
# RFC 7748 Montgomery Ladder & X25519 Algebraic Bridges (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder`)

Pure `0-sorry` mathematical bridge theorems for `x25519Ladder`, `x25519`, `x25519Pubkey`,
`x25519Ref`, `x25519PubFromSecretRef`, and `isCanonicalX25519`:
1. 255-step Kummer-line ladder soundness on all of $E(\mathbb{F}_p)$ (`x25519Ladder_edToMontU`,
   `montLadderLoop_255_edToMontU`) and $E_{\text{twist}}(\mathbb{F}_p)$ (`x25519Ladder_twToMontU`,
   `montLadderLoop_255_twToMontU`), including the degenerate $u = 0$ ($x = 0$) 2-torsion fiber.
2. Congruence mod $p_{25519}$ (`x25519_uCoord_congr`), basepoint identity (`edToMontU_edBasepoint`,
   `x25519Pubkey_eq_edBasepoint`), and Diffie–Hellman commutativity (`x25519_comm`, `x25519Ref_comm`).
3. Complete all-zero / low-order output characterization (`x25519_eq_zero_iff_lowOrder`,
   `x25519Ref_eq_zero_iff_lowOrder`), public-key non-low-order (`x25519Pubkey_not_lowOrder`), and
   non-zero Diffie–Hellman agreement on derived public keys (`x25519_pub_ne_zero`).
4. Preservation of `libsignal-core` prime-order canonicality (`isCanonicalX25519_x25519`) and
   prime-order subgroup Kummer-line bijectivity / scalar action for `X25519Model`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder

open VerifiedLibraries.Common (
  p25519 edOrderL fpMul fpInv fpNeg EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul
  leBytesToNat natToLeBytes clampScalarBytes clampScalar)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 MontProjPoint montLadderLoop x25519Ladder x25519 x25519Basepoint x25519Pubkey
  x25519Ref x25519PubFromSecretRef montToEdwards isCanonicalX25519 lowOrderUs)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpMul_lt fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg edAdd_edZero
  edAdd_edNeg_self edNeg_edAdd_self edNeg_edZero edNeg_edNeg edNeg_edAdd edAdd_assoc edNatSmul
  edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_add edNatSmul_mul
  edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edNatSmul_edOrderL_edBasepoint
  edNatSmul_mod_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_cons leBytesToNat_lt leBytesToNat_natToLeBytes_of_lt
  clampScalar_lt_two_pow_256 edOrderL_pos)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  twistOrderL edOrderL_odd twistOrderL_odd two_pow_252_lt_edOrderL two_pow_252_lt_twistOrderL
  edOrderL_prime twistOrderL_prime odd_prime_not_dvd_two_pow_mul gcd_sixteen_mul_odd_prime
  gcd_sixteen_mul_eight_mul_odd_prime gcd_sixteen_mul_four_mul_odd_prime)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  montRHS edToMontU edToMontU_lt edToMontU_edBasepoint edToMontU_edNeg
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero montToEdwards_some_edToMontU
  decodeU255_natToLeBytes_edToMontU montToEdwards_edToMontU edNatSmul_edBasepoint_eq_edZero_iff
  edSmul_eight_eq_edZero_iff_lowOrderUs)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  FpIsSquare fp_not_isSquare_of_euler_eq_sub_one twOnCurve twZero twNatSmul twOnCurve_twNatSmul
  twNatSmul_twZero twNatSmul_mul twToMontU twToMontU_lt edToMontU_eq_zero_iff
  twToMontU_eq_zero_iff edOnCurve_montRHS_isSquare twOnCurve_montRHS_not_isSquare
  mont_lift_dichotomy)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  edOnCurve_eq_of_edToMontU_eq edNatSmul_gcd_eq_zero edNatSmul_dvd_eq_zero
  twNatSmul_gcd_eq_zero twNatSmul_dvd_eq_zero edNatSmul_eight_mul_edOrderL
  twNatSmul_four_mul_twistOrderL lowOrderU8a lowOrderU8b edNatSmul_two_eq_zero_iff
  edNatSmul_two_eq_zero_iff_montU twNatSmul_two_eq_zero_iff twNatSmul_two_eq_zero_iff_montU
  twNatSmul_four_eq_zero_iff_montU edNatSmul_eight_eq_zero_iff_montU)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer (
  montLadderLoop_zero)

/-! ## 1. 255-Step Kummer-Line Ladder Soundness (Curve, Twist, & $u = 0$) -/

/-- 255-step Kummer-line ladder soundness on $E(\mathbb{F}_p)$ for $P.x \ne 0$. -/
theorem montLadderLoop_255_edToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : edOnCurve P = true) (hPx : P.x ≠ 0) :
    let u1 := edToMontU P
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = edToMontU (edNatSmul k P) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer.montLadderLoop_255_edToMontU hk hP hPx

/-- 255-step Kummer-line ladder soundness on $E_{\text{twist}}(\mathbb{F}_p)$ for $P.x \ne 0$. -/
theorem montLadderLoop_255_twToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : twOnCurve P = true) (hPx : P.x ≠ 0) :
    let u1 := twToMontU P
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = twToMontU (twNatSmul k P) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer.montLadderLoop_255_twToMontU hk hP hPx

theorem x25519Ladder_mod (k u : Nat) :
    x25519Ladder k (u % p25519) = x25519Ladder k u := by
  unfold x25519Ladder
  dsimp only []
  rw [Nat.mod_mod]

theorem x25519Ladder_zero (k : Nat) :
    x25519Ladder k 0 = 0 := by
  unfold x25519Ladder
  dsimp only []
  rw [Nat.zero_mod]
  exact montLadderLoop_zero 255 k

/-- Full 255-step `x25519Ladder` soundness on $E(\mathbb{F}_p)$ for **all** curve points `P`
    (including `edZero` and the 2-torsion point `(0, p - 1)`). -/
theorem x25519Ladder_edToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : edOnCurve P = true) :
    x25519Ladder k (edToMontU P) = edToMontU (edNatSmul k P) := by
  by_cases hPx : P.x = 0
  · have hu0 : edToMontU P = 0 := (edToMontU_eq_zero_iff hP).mpr hPx
    rw [hu0, x25519Ladder_zero]
    have h2P : edNatSmul 2 P = edZero := (edNatSmul_two_eq_zero_iff hP).mpr hPx
    have h2kP : edNatSmul 2 (edNatSmul k P) = edZero := by
      rw [← edNatSmul_mul 2 k hP, Nat.mul_comm 2 k, edNatSmul_mul k 2 hP, h2P, edNatSmul_edZero]
    have hk_on : edOnCurve (edNatSmul k P) = true := edOnCurve_edNatSmul k hP
    exact ((edToMontU_eq_zero_iff hk_on).mpr ((edNatSmul_two_eq_zero_iff hk_on).mp h2kP)).symm
  · unfold x25519Ladder
    dsimp only []
    rw [Nat.mod_eq_of_lt (edToMontU_lt P)]
    exact montLadderLoop_255_edToMontU hk hP hPx

theorem x25519Ladder_edToMontU_edSmul {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : edOnCurve P = true) :
    x25519Ladder k (edToMontU P) = edToMontU (edSmul k P) := by
  rw [x25519Ladder_edToMontU hk hP, edSmul_eq_edNatSmul (Nat.lt_trans hk (by decide)) hP]

/-- Full 255-step `x25519Ladder` soundness on $E_{\text{twist}}(\mathbb{F}_p)$ for **all** twist points `P`
    (including `twZero` and the 2-torsion point `(0, p - 1)`). -/
theorem x25519Ladder_twToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : twOnCurve P = true) :
    x25519Ladder k (twToMontU P) = twToMontU (twNatSmul k P) := by
  by_cases hPx : P.x = 0
  · have hu0 : twToMontU P = 0 := (twToMontU_eq_zero_iff hP).mpr hPx
    rw [hu0, x25519Ladder_zero]
    have h2P : twNatSmul 2 P = twZero := (twNatSmul_two_eq_zero_iff hP).mpr hPx
    have h2kP : twNatSmul 2 (twNatSmul k P) = twZero := by
      rw [← twNatSmul_mul 2 k hP, Nat.mul_comm 2 k, twNatSmul_mul k 2 hP, h2P, twNatSmul_twZero]
    have hk_on : twOnCurve (twNatSmul k P) = true := twOnCurve_twNatSmul k hP
    exact ((twToMontU_eq_zero_iff hk_on).mpr ((twNatSmul_two_eq_zero_iff hk_on).mp h2kP)).symm
  · unfold x25519Ladder
    dsimp only []
    rw [Nat.mod_eq_of_lt (twToMontU_lt P)]
    exact montLadderLoop_255_twToMontU hk hP hPx

/-! ## 2. Clamped ScalarCofactor-8 Decomposition, Congruence, & Commutativity -/

theorem x25519_uCoord_congr (s u u' : List (BitVec 8))
    (h : decodeU255 u % p25519 = decodeU255 u' % p25519) :
    x25519 s u = x25519 s u' := by
  unfold x25519 x25519Ladder
  dsimp only []
  rw [h]

set_option maxRecDepth 8000 in
private theorem all_u8_clamp_masks :
    (List.range 256).all (fun n =>
      let b : BitVec 8 := BitVec.ofNat 8 n
      ((b &&& 0xf8#8).toNat % 8 == 0) &&
      (64 ≤ ((b &&& 0x7f#8) ||| 0x40#8).toNat) &&
      (((b &&& 0x7f#8) ||| 0x40#8).toNat < 128)) = true := by
  decide

private theorem mask_f8_props (b : BitVec 8) :
    (b &&& 0xf8#8).toNat % 8 = 0 ∧ (b &&& 0xf8#8).toNat < 256 := by
  have hb_eq : BitVec.ofNat 8 b.toNat = b :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt])
  have hall := List.all_eq_true.mp all_u8_clamp_masks b.toNat (List.mem_range.mpr b.isLt)
  dsimp only at hall
  rw [hb_eq] at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  exact ⟨hall.1.1, (b &&& 0xf8#8).isLt⟩

private theorem mask_7f_40_props (b : BitVec 8) :
    64 ≤ ((b &&& 0x7f#8) ||| 0x40#8).toNat ∧
    ((b &&& 0x7f#8) ||| 0x40#8).toNat < 128 := by
  have hb_eq : BitVec.ofNat 8 b.toNat = b :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt])
  have hall := List.all_eq_true.mp all_u8_clamp_masks b.toNat (List.mem_range.mpr b.isLt)
  dsimp only at hall
  rw [hb_eq] at hall
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  exact ⟨hall.1.2, hall.2⟩

private theorem leBytesToNat_append_singleton (bs : List (BitVec 8)) (b : BitVec 8) :
    leBytesToNat (bs ++ [b]) = leBytesToNat bs + b.toNat * 256 ^ bs.length := by
  induction bs with
  | nil =>
    simp [leBytesToNat]
  | cons c cs ih =>
    rw [List.cons_append, leBytesToNat_cons, ih, leBytesToNat_cons, List.length_cons,
        Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm]

private theorem pow_256_pos (n : Nat) : 1 ≤ 256 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by decide))

/-- Every RFC 7748 / RFC 8032 clamped scalar `clampScalar s` decomposes as `8 * m` with
    `0 < m < 2 ^ 252`. -/
theorem clampScalar_eight_mul (s : List (BitVec 8)) :
    ∃ m : Nat, clampScalar s = 8 * m ∧ 0 < m ∧ m < 2 ^ 252 := by
  unfold clampScalar clampScalarBytes
  let bs := s.take 32
  let b0 := (bs.getD 0 0#8) &&& 0xf8#8
  let mid := (bs.drop 1).take 30
  let b31 := ((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8
  change ∃ m : Nat, leBytesToNat ([b0] ++ mid ++ [b31]) = 8 * m ∧ 0 < m ∧ m < 2 ^ 252
  have hcons : [b0] ++ mid ++ [b31] = b0 :: (mid ++ [b31]) := rfl
  rw [hcons, leBytesToNat_cons, leBytesToNat_append_singleton]
  obtain ⟨hb0_mod, hb0_lt⟩ := mask_f8_props (bs.getD 0 0#8)
  obtain ⟨hb31_ge, hb31_lt⟩ := mask_7f_40_props (bs.getD 31 0#8)
  have hmid_len : mid.length ≤ 30 := List.length_take_le 30 _
  have hmid_lt : leBytesToNat mid < 256 ^ mid.length := leBytesToNat_lt mid
  have hpow_ge : 1 ≤ 256 ^ mid.length := pow_256_pos mid.length
  have hpow_le : 256 ^ mid.length ≤ 256 ^ 30 := Nat.pow_le_pow_right (by decide) hmid_len
  let H := leBytesToNat mid + b31.toNat * 256 ^ mid.length
  have hH_pos : 64 ≤ H := by
    have h1 : 64 * 1 ≤ 64 * 256 ^ mid.length := Nat.mul_le_mul_left 64 hpow_ge
    have h2 : 64 * 256 ^ mid.length ≤ b31.toNat * 256 ^ mid.length :=
      Nat.mul_le_mul_right _ hb31_ge
    dsimp only [H]; omega
  have hH_lt : H < 2 ^ 247 := by
    have h1 : b31.toNat * 256 ^ mid.length ≤ 127 * 256 ^ mid.length :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hb31_lt)
    have h2 : H < 128 * 256 ^ mid.length := by
      dsimp only [H]
      generalize 256 ^ mid.length = P at hmid_lt h1
      omega
    have h3 : 128 * 256 ^ mid.length ≤ 128 * 256 ^ 30 := Nat.mul_le_mul_left 128 hpow_le
    have h4 : 128 * 256 ^ 30 = 2 ^ 247 := by decide +kernel
    exact Nat.lt_of_lt_of_le h2 (h4 ▸ h3)
  refine ⟨H * 32 + b0.toNat / 8, ?_, ?_, ?_⟩
  · dsimp only [b0] at hb0_mod hb0_lt ⊢
    change H * 256 + ((bs.getD 0 0#8) &&& 0xf8#8).toNat =
      8 * (H * 32 + ((bs.getD 0 0#8) &&& 0xf8#8).toNat / 8)
    generalize ((bs.getD 0 0#8) &&& 0xf8#8).toNat = B0 at hb0_mod hb0_lt ⊢
    omega
  · omega
  · have hH_le : H ≤ 2 ^ 247 - 1 := Nat.le_sub_one_of_lt hH_lt
    have hH32 : H * 32 ≤ (2 ^ 247 - 1) * 32 := Nat.mul_le_mul_right 32 hH_le
    have hb0_div : b0.toNat / 8 ≤ 31 := by dsimp only [b0]; omega
    have hbound : (2 ^ 247 - 1) * 32 + 31 < 2 ^ 252 := by decide +kernel
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hH32 hb0_div) hbound

theorem clampScalar_lt_two_pow_255 (s : List (BitVec 8)) :
    clampScalar s < 2 ^ 255 := by
  obtain ⟨m, hk, _, hm_lt⟩ := clampScalar_eight_mul s
  calc clampScalar s = 8 * m := hk
    _ < 8 * 2 ^ 252 := Nat.mul_lt_mul_of_pos_left hm_lt (by decide)
    _ = 2 ^ 255 := by decide +kernel

private theorem natToLeBytes_length (len n : Nat) :
    (natToLeBytes len n).length = len := by
  unfold natToLeBytes
  rw [List.length_map, List.length_range]

private theorem decodeU255_natToLeBytes_mod_p {v : Nat} (hv : v < p25519) :
    decodeU255 (natToLeBytes 32 v) % p25519 = v := by
  unfold decodeU255
  have htake : (natToLeBytes 32 v).take 32 = natToLeBytes 32 v :=
    List.take_of_length_le (Nat.le_of_eq (natToLeBytes_length 32 v))
  have hv255 : v < 2 ^ 255 := Nat.lt_trans hv (by unfold p25519; decide +kernel)
  have hv256 : v < 256 ^ 32 := Nat.lt_trans hv255 (by decide +kernel)
  rw [htake, leBytesToNat_natToLeBytes_of_lt hv256, Nat.mod_eq_of_lt hv255, Nat.mod_eq_of_lt hv]

private theorem natToLeBytes_eq_replicate_zero_iff {v : Nat} (hv : v < p25519) :
    natToLeBytes 32 v = List.replicate 32 0#8 ↔ v = 0 := by
  constructor
  · intro h
    have hv256 : v < 256 ^ 32 := Nat.lt_trans hv (by unfold p25519; decide +kernel)
    have hl := congrArg leBytesToNat h
    rw [leBytesToNat_natToLeBytes_of_lt hv256] at hl
    have hr : leBytesToNat (List.replicate 32 0#8) = 0 := by decide
    omega
  · rintro rfl
    decide

theorem edBasepoint_x_ne_zero : edBasepoint.x ≠ 0 := by
  unfold edBasepoint; decide +kernel

theorem x25519Pubkey_eq_edNatSmul (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edNatSmul (clampScalar s) edBasepoint)) := by
  unfold x25519Pubkey x25519 x25519Basepoint
  rw [← x25519Ladder_mod,
      decodeU255_natToLeBytes_mod_p (by unfold p25519; decide +kernel : 9 < p25519),
      ← edToMontU_edBasepoint,
      x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s) edOnCurve_edBasepoint]

/-- X25519 public-key / Ed25519 basepoint bridge: `x25519Pubkey s` equals the 32-byte little-endian
    encoding of `edToMontU (edSmul (clampScalar s) edBasepoint)`. -/
theorem x25519Pubkey_eq_edBasepoint (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edSmul (clampScalar s) edBasepoint)) := by
  rw [x25519Pubkey_eq_edNatSmul s,
      ← edSmul_eq_edNatSmul (clampScalar_lt_two_pow_256 s) edOnCurve_edBasepoint]

theorem edNatSmul_clampScalar_edBasepoint_x_ne_zero (s : List (BitVec 8)) :
    (edNatSmul (clampScalar s) edBasepoint).x ≠ 0 := by
  obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul s
  rw [hk]
  intro hx0
  have h_on := edOnCurve_edNatSmul (8 * m) edOnCurve_edBasepoint
  have h2 : edNatSmul 2 (edNatSmul (8 * m) edBasepoint) = edZero :=
    (edNatSmul_two_eq_zero_iff h_on).mpr hx0
  rw [← edNatSmul_mul 2 (8 * m) edOnCurve_edBasepoint,
      show 2 * (8 * m) = 16 * m by omega] at h2
  have hgcd := gcd_sixteen_mul_odd_prime edOrderL_prime edOrderL_odd hm0
    (Nat.lt_trans hm_lt two_pow_252_lt_edOrderL)
  have h1 := edNatSmul_gcd_eq_zero edOnCurve_edBasepoint h2 edNatSmul_edOrderL_edBasepoint
  rw [hgcd, edNatSmul_one edOnCurve_edBasepoint] at h1
  exact edBasepoint_x_ne_zero (congrArg EdPoint.x h1)

theorem x25519_x25519Pubkey_eq_edNatSmul (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) =
      natToLeBytes 32 (edToMontU (edNatSmul (clampScalar a * clampScalar b) edBasepoint)) := by
  rw [x25519Pubkey_eq_edNatSmul b]
  unfold x25519
  rw [← x25519Ladder_mod,
      decodeU255_natToLeBytes_edToMontU _,
      x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 a)
        (edOnCurve_edNatSmul (clampScalar b) edOnCurve_edBasepoint),
      ← edNatSmul_mul (clampScalar a) (clampScalar b) edOnCurve_edBasepoint]

/-- X25519 Diffie–Hellman commutativity (`x25519 a (x25519Pubkey b) = x25519 b (x25519Pubkey a)`). -/
theorem x25519_comm (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) = x25519 b (x25519Pubkey a) := by
  rw [x25519_x25519Pubkey_eq_edNatSmul a b,
      x25519_x25519Pubkey_eq_edNatSmul b a,
      Nat.mul_comm (clampScalar a) (clampScalar b)]

/-- `List.Vector` hook Diffie–Hellman commutativity (`x25519Ref`). -/
theorem x25519Ref_comm (a b : List.Vector (BitVec 8) 32) :
    x25519Ref a (x25519PubFromSecretRef b) = x25519Ref b (x25519PubFromSecretRef a) := by
  apply Subtype.ext
  exact x25519_comm a.toList b.toList

/-! ## 3. All-Zero / Low-Order Output Characterization & Derived Public-Key Non-Degeneracy -/

private theorem mem_lowOrderUs_iff (u : Nat) :
    u ∈ lowOrderUs ↔
      u = 0 ∨ u = 1 ∨ u = lowOrderU8a ∨ u = lowOrderU8b ∨ u = p25519 - 1 := by
  simp [lowOrderUs, lowOrderU8a, lowOrderU8b]

set_option maxRecDepth 20000 in
private theorem not_isSquare_montRHS_sub_one :
    ¬ FpIsSquare (Fp.ofNat (montRHS (p25519 - 1))) := by
  apply fp_not_isSquare_of_euler_eq_sub_one
  unfold Fp.ofNat montRHS p25519
  decide +kernel

private theorem isSquare_montRHS_one : FpIsSquare (Fp.ofNat (montRHS 1)) :=
  ⟨Fp.ofNat 48802004052532134862652268456126542835229456083994414501085850622543968879637,
    by ext; unfold Fp.ofNat montRHS p25519; decide +kernel⟩

private theorem isSquare_montRHS_lowOrderU8a : FpIsSquare (Fp.ofNat (montRHS lowOrderU8a)) :=
  ⟨Fp.ofNat 32026303591712962751241307547882981359278212717910236697706316503764922500307,
    by ext; unfold Fp.ofNat montRHS lowOrderU8a p25519; decide +kernel⟩

private theorem isSquare_montRHS_lowOrderU8b : FpIsSquare (Fp.ofNat (montRHS lowOrderU8b)) :=
  ⟨Fp.ofNat 47389623381099381275796781267935282128369626952426857267179501978497824351671,
    by ext; unfold Fp.ofNat montRHS lowOrderU8b p25519; decide +kernel⟩

/-- Complete Curve25519 + quadratic twist all-zero output characterization:
    `x25519 s u = List.replicate 32 0#8` iff `decodeU255 u % p25519 ∈ lowOrderUs`. -/
theorem x25519_eq_zero_iff_lowOrder (s u : List (BitVec 8)) :
    x25519 s u = List.replicate 32 0#8 ↔ decodeU255 u % p25519 ∈ lowOrderUs := by
  unfold x25519 x25519Ladder
  dsimp only []
  rw [natToLeBytes_eq_replicate_zero_iff (fpMul_lt _ _)]
  let u1 := decodeU255 u % p25519
  change fpMul (montLadderLoop 255 (clampScalar s) u1 ⟨1, 0⟩ ⟨u1, 1⟩).U
      (fpInv (montLadderLoop 255 (clampScalar s) u1 ⟨1, 0⟩ ⟨u1, 1⟩).W) = 0 ↔
    u1 ∈ lowOrderUs
  have hu1_lt : u1 < p25519 := Nat.mod_lt _ p25519_pos
  by_cases hu0 : u1 = 0
  · rw [hu0, montLadderLoop_zero 255 (clampScalar s), mem_lowOrderUs_iff]
    exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · have hu1_pos : 0 < u1 := Nat.pos_of_ne_zero hu0
    obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul s
    have hk_lt : clampScalar s < 2 ^ 255 := clampScalar_lt_two_pow_255 s
    rcases mont_lift_dichotomy hu1_pos hu1_lt with
      ⟨P1, hP1, hP1x, huP1⟩ | ⟨P1, hP1, hP1x, huP1⟩
    · have hsq_u1 : FpIsSquare (Fp.ofNat (montRHS u1)) :=
        huP1 ▸ edOnCurve_montRHS_isSquare hP1 hP1x
      rw [← huP1, montLadderLoop_255_edToMontU hk_lt hP1 hP1x, huP1, hk]
      have h_on := edOnCurve_edNatSmul (8 * m) hP1
      rw [← edNatSmul_two_eq_zero_iff_montU h_on,
          ← edNatSmul_mul 2 (8 * m) hP1,
          show 2 * (8 * m) = 16 * m by omega]
      have h8_iff : edNatSmul (16 * m) P1 = edZero ↔ edNatSmul 8 P1 = edZero := by
        constructor
        · intro h16
          have hgcd := gcd_sixteen_mul_eight_mul_odd_prime edOrderL_prime edOrderL_odd hm0
            (Nat.lt_trans hm_lt two_pow_252_lt_edOrderL)
          have hg := edNatSmul_gcd_eq_zero hP1 h16 (edNatSmul_eight_mul_edOrderL hP1)
          rwa [hgcd] at hg
        · intro h8
          exact edNatSmul_dvd_eq_zero hP1 h8 ⟨2 * m, by omega⟩
      rw [h8_iff, edNatSmul_eight_eq_zero_iff_montU hP1, huP1, mem_lowOrderUs_iff]
      constructor
      · rintro (h0 | h1 | ha | hb)
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
      · rintro (h0 | h1 | ha | hb | hsub1)
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr hb))
        · exfalso
          exact not_isSquare_montRHS_sub_one (hsub1 ▸ hsq_u1)
    · have hnsq_u1 : ¬ FpIsSquare (Fp.ofNat (montRHS u1)) :=
        huP1 ▸ twOnCurve_montRHS_not_isSquare hP1 hP1x
      rw [← huP1, montLadderLoop_255_twToMontU hk_lt hP1 hP1x, huP1, hk]
      have h_on := twOnCurve_twNatSmul (8 * m) hP1
      rw [← twNatSmul_two_eq_zero_iff_montU h_on,
          ← twNatSmul_mul 2 (8 * m) hP1,
          show 2 * (8 * m) = 16 * m by omega]
      have h4_iff : twNatSmul (16 * m) P1 = twZero ↔ twNatSmul 4 P1 = twZero := by
        constructor
        · intro h16
          have hgcd := gcd_sixteen_mul_four_mul_odd_prime twistOrderL_prime twistOrderL_odd hm0
            (Nat.lt_trans hm_lt two_pow_252_lt_twistOrderL)
          have hg := twNatSmul_gcd_eq_zero hP1 h16 (twNatSmul_four_mul_twistOrderL hP1)
          rwa [hgcd] at hg
        · intro h4
          exact twNatSmul_dvd_eq_zero hP1 h4 ⟨4 * m, by omega⟩
      rw [h4_iff, twNatSmul_four_eq_zero_iff_montU hP1, huP1, mem_lowOrderUs_iff]
      constructor
      · rintro (h0 | hsub1)
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr (Or.inr hsub1)))
      · rintro (h0 | h1 | ha | hb | hsub1)
        · exact Or.inl h0
        · exfalso; exact hnsq_u1 (h1 ▸ isSquare_montRHS_one)
        · exfalso; exact hnsq_u1 (ha ▸ isSquare_montRHS_lowOrderU8a)
        · exfalso; exact hnsq_u1 (hb ▸ isSquare_montRHS_lowOrderU8b)
        · exact Or.inr hsub1

/-- `List.Vector` hook all-zero output characterization (`x25519Ref`). -/
theorem x25519Ref_eq_zero_iff_lowOrder (s u : List.Vector (BitVec 8) 32) :
    (x25519Ref s u).toList = List.replicate 32 0#8 ↔ decodeU255 u.toList % p25519 ∈ lowOrderUs :=
  x25519_eq_zero_iff_lowOrder s.toList u.toList

/-- Derived X25519 public keys never lie in `lowOrderUs`. -/
theorem x25519Pubkey_not_lowOrder (s : List (BitVec 8)) :
    decodeU255 (x25519Pubkey s) % p25519 ∉ lowOrderUs := by
  rw [x25519Pubkey_eq_edNatSmul s, decodeU255_natToLeBytes_edToMontU]
  have hP_on := edOnCurve_edNatSmul (clampScalar s) edOnCurve_edBasepoint
  rw [← edSmul_eight_eq_edZero_iff_lowOrderUs hP_on,
      edSmul_eq_edNatSmul (by decide : 8 < 2 ^ 256) hP_on,
      ← edNatSmul_mul 8 (clampScalar s) edOnCurve_edBasepoint,
      edNatSmul_edBasepoint_eq_edZero_iff]
  obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul s
  rw [hk, show 8 * (8 * m) = 2 ^ 6 * m by omega]
  exact odd_prime_not_dvd_two_pow_mul edOrderL_prime edOrderL_odd hm0
    (Nat.lt_trans hm_lt two_pow_252_lt_edOrderL) 6

/-- Diffie–Hellman agreement with any derived public key `x25519Pubkey b` is never all-zero. -/
theorem x25519_pub_ne_zero (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) ≠ List.replicate 32 0#8 :=
  mt (x25519_eq_zero_iff_lowOrder a (x25519Pubkey b)).mp (x25519Pubkey_not_lowOrder b)

/-! ## 4. Canonicality Preservation (`isCanonicalX25519_x25519`) -/

private theorem edNatSmul_edNeg (n : Nat) (A : EdPoint) :
    edNatSmul n (edNeg A) = edNeg (edNatSmul n A) := by
  induction n with
  | zero =>
    exact edNeg_edZero.symm
  | succ k ih =>
    simp only [edNatSmul]
    rw [ih, ← edNeg_edAdd A (edNatSmul k A)]

private theorem montToEdwards_edToMontU_sign_zero {A : EdPoint}
    (hA : edOnCurve A = true) (hne : A ≠ edZero) :
    montToEdwards (natToLeBytes 32 (edToMontU A)) 0 =
      some (if A.x % 2 == 1 then edNeg A else A) := by
  rcases Nat.mod_two_eq_zero_or_one A.x with hx0 | hx1
  · have hb : (A.x % 2 == 1) = false := by rw [hx0]; rfl
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hm := montToEdwards_edToMontU hA hne
    rwa [hx0] at hm
  · have hb : (A.x % 2 == 1) = true := by rw [hx1]; rfl
    rw [hb]
    simp only [↓reduceIte]
    have hneg_on : edOnCurve (edNeg A) = true := edOnCurve_edNeg hA
    have hneg_ne : edNeg A ≠ edZero := by
      intro h0
      have h1 := congrArg edNeg h0
      rw [edNeg_edNeg hA, edNeg_edZero] at h1
      exact hne h1
    have hx_lt : A.x < p25519 := edOnCurve_x_lt hA
    have hx_mod_ne : A.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hx_lt]; omega
    have hneg_even : (edNeg A).x % 2 = 0 := by
      dsimp only [edNeg]
      rw [fpNeg_mod_two_of_ne_zero hx_mod_ne, Nat.mod_eq_of_lt hx_lt, hx1]
    have hm := montToEdwards_edToMontU hneg_on hneg_ne
    rwa [edToMontU_edNeg, hneg_even] at hm

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

/-- `isCanonicalX25519` is preserved by `x25519 a pk` for every secret scalar `a`. -/
theorem isCanonicalX25519_x25519 {a pk : List (BitVec 8)}
    (h : isCanonicalX25519 pk = true) :
    isCanonicalX25519 (x25519 a pk) = true := by
  have h1 : ((pk.length == 32 && decide (leBytesToNat pk < p25519)) &&
      match montToEdwards pk 0 with | none => false | some P => edSmul edOrderL P == edZero) = true := h
  obtain ⟨P, hmont, hmont_cond⟩ := match_edPoint_eq_true (montToEdwards pk 0)
    (fun P => edSmul edOrderL P == edZero) ((Bool.and_eq_true _ _).mp h1).2
  rw [beq_iff_eq] at hmont_cond
  have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
  have hP_ne0 : P ≠ edZero := montToEdwards_some_ne_edZero hmont
  have huP : edToMontU P = decodeU255 pk % p25519 := montToEdwards_some_edToMontU hmont
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
  let k := clampScalar a
  let Q := edNatSmul k P
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul k hP_on
  have hx_eq : x25519 a pk = natToLeBytes 32 (edToMontU Q) := by
    unfold x25519
    rw [← x25519Ladder_mod, ← huP, x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 a) hP_on]
  have hQ_ne0 : Q ≠ edZero := by
    intro hQ0
    obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul a
    have h8m : edNatSmul (8 * m) P = edZero := hk ▸ hQ0
    have h16m : edNatSmul (16 * m) P = edZero := by
      rw [show 16 * m = 2 * (8 * m) by omega, edNatSmul_mul 2 (8 * m) hP_on, h8m, edNatSmul_edZero]
    have hgcd := gcd_sixteen_mul_odd_prime edOrderL_prime edOrderL_odd hm0
      (Nat.lt_trans hm_lt two_pow_252_lt_edOrderL)
    have h1 := edNatSmul_gcd_eq_zero hP_on h16m hP_ord
    rw [hgcd, edNatSmul_one hP_on] at h1
    exact hP_ne0 h1
  have hQ_ord : edNatSmul edOrderL Q = edZero := by
    dsimp only [Q]
    rw [← edNatSmul_mul edOrderL k hP_on, Nat.mul_comm edOrderL k,
        edNatSmul_mul k edOrderL hP_on, hP_ord, edNatSmul_edZero]
  let Q' : EdPoint := if Q.x % 2 == 1 then edNeg Q else Q
  have hQ'_on : edOnCurve Q' = true := by
    dsimp only [Q']
    split
    · exact edOnCurve_edNeg hQ_on
    · exact hQ_on
  have hQ'_ord : edSmul edOrderL Q' = edZero := by
    rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hQ'_on]
    dsimp only [Q']
    split
    · rw [edNatSmul_edNeg edOrderL Q, hQ_ord, edNeg_edZero]
    · exact hQ_ord
  rw [hx_eq]
  have hu_lt : edToMontU Q < p25519 := edToMontU_lt Q
  have hu_lt256 : edToMontU Q < 256 ^ 32 :=
    Nat.lt_trans hu_lt (by unfold p25519; decide +kernel)
  have hhead : ((natToLeBytes 32 (edToMontU Q)).length == 32 &&
      decide (leBytesToNat (natToLeBytes 32 (edToMontU Q)) < p25519)) = true := by
    rw [natToLeBytes_length, leBytesToNat_natToLeBytes_of_lt hu_lt256]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨trivial, hu_lt⟩
  have htail : (match montToEdwards (natToLeBytes 32 (edToMontU Q)) 0 with
      | none => false
      | some P => edSmul edOrderL P == edZero) = true :=
    match_edPoint_of_some _ Q' (fun P => edSmul edOrderL P == edZero)
      (montToEdwards_edToMontU_sign_zero hQ_on hQ_ne0)
      (beq_iff_eq.mpr hQ'_ord)
  exact (Bool.and_eq_true _ _).mpr ⟨hhead, htail⟩

/-! ## 5. Prime-Order Subgroup Kummer-Line Helpers (`X25519Model` / `ConsumerBridges`) -/

/-- Re-export of `edToMontU (edNeg P) = edToMontU P` (`edOnCurve P = true` is not even needed). -/
theorem edToMontU_edNeg_of_onCurve {P : EdPoint} (_hP : edOnCurve P = true) :
    edToMontU (edNeg P) = edToMontU P :=
  edToMontU_edNeg P

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

private theorem edNatSmul_eq_imp_sub_zero {G : EdPoint} (hG : edOnCurve G = true)
    {i j : Nat} (hij : i ≤ j) (heq : edNatSmul i G = edNatSmul j G) :
    edNatSmul (j - i) G = edZero := by
  have hsplit : j = (j - i) + i := (Nat.sub_add_cancel hij).symm
  have hadd : edAdd (edNatSmul (j - i) G) (edNatSmul i G) = edNatSmul i G := by
    rw [← edNatSmul_add (j - i) i hG, ← hsplit, heq]
  have hsub := congrArg (fun X => edAdd X (edNeg (edNatSmul i G))) hadd
  have hi_on := edOnCurve_edNatSmul i hG
  have hji_on := edOnCurve_edNatSmul (j - i) hG
  rw [edAdd_assoc hji_on hi_on (edOnCurve_edNeg hi_on),
      edAdd_edNeg_self hi_on, edAdd_edZero hji_on] at hsub
  exact hsub

/-- On the half-interval `0 ≤ i, j ≤ (edOrderL - 1) / 2`, the Kummer map
    `i ↦ edToMontU (edSmul i edBasepoint)` is injective. -/
theorem edToMontU_edSmul_edBasepoint_eq_iff {i j : Nat}
    (hi : i ≤ (edOrderL - 1) / 2) (hj : j ≤ (edOrderL - 1) / 2) :
    edToMontU (edSmul i edBasepoint) = edToMontU (edSmul j edBasepoint) ↔ i = j := by
  have hhalf_mul : 2 * ((edOrderL - 1) / 2) = edOrderL - 1 := by
    unfold edOrderL; decide +kernel
  have hL_pos : 0 < edOrderL := edOrderL_pos
  have hi_ltL : i < edOrderL := by omega
  have hj_ltL : j < edOrderL := by omega
  rw [edSmul_eq_edNatSmul (Nat.lt_trans hi_ltL edOrderL_lt_two_pow_256) edOnCurve_edBasepoint,
      edSmul_eq_edNatSmul (Nat.lt_trans hj_ltL edOrderL_lt_two_pow_256) edOnCurve_edBasepoint]
  constructor
  · intro hu
    have hx0_iff : ∀ {k : Nat}, k ≤ (edOrderL - 1) / 2 →
        ((edNatSmul k edBasepoint).x = 0 ↔ k = 0) := by
      intro k hk
      have hk_on := edOnCurve_edNatSmul k edOnCurve_edBasepoint
      rw [← edNatSmul_two_eq_zero_iff hk_on,
          ← edNatSmul_mul 2 k edOnCurve_edBasepoint,
          edNatSmul_edBasepoint_eq_edZero_iff]
      constructor
      · intro hdvd
        by_cases hk0 : k = 0
        · exact hk0
        · exfalso
          exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
      · rintro rfl
        exact ⟨0, rfl⟩
    have hi_on := edOnCurve_edNatSmul i edOnCurve_edBasepoint
    have hj_on := edOnCurve_edNatSmul j edOnCurve_edBasepoint
    by_cases hi0 : i = 0
    · subst hi0
      have hu0 : edToMontU (edNatSmul j edBasepoint) = 0 := by
        rw [← hu]
        exact (edToMontU_eq_zero_iff edOnCurve_edZero).mpr rfl
      exact ((hx0_iff hj).mp ((edToMontU_eq_zero_iff hj_on).mp hu0)).symm
    · by_cases hj0 : j = 0
      · subst hj0
        have hu0 : edToMontU (edNatSmul i edBasepoint) = 0 := by
          rw [hu]
          exact (edToMontU_eq_zero_iff edOnCurve_edZero).mpr rfl
        exact (hx0_iff hi).mp ((edToMontU_eq_zero_iff hi_on).mp hu0)
      · have hix : (edNatSmul i edBasepoint).x ≠ 0 := mt (hx0_iff hi).mp hi0
        have hjx : (edNatSmul j edBasepoint).x ≠ 0 := mt (hx0_iff hj).mp hj0
        rcases edOnCurve_eq_or_edNeg_of_edToMontU_eq hi_on hj_on hix hjx hu with heq | hneg
        · by_cases hle : i ≤ j
          · have hsub0 := edNatSmul_eq_imp_sub_zero edOnCurve_edBasepoint hle heq
            have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff (j - i)).mp hsub0
            by_cases hdiff : j - i = 0
            · omega
            · exfalso
              exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
          · have hle' : j ≤ i := by omega
            have hsub0 := edNatSmul_eq_imp_sub_zero edOnCurve_edBasepoint hle' heq.symm
            have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff (i - j)).mp hsub0
            by_cases hdiff : i - j = 0
            · omega
            · exfalso
              exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
        · exfalso
          have hsum0 : edNatSmul (i + j) edBasepoint = edZero := by
            rw [edNatSmul_add i j edOnCurve_edBasepoint, hneg, edNeg_edAdd_self hj_on]
          have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff (i + j)).mp hsum0
          exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
  · rintro rfl
    rfl

/-- Scalar action of `x25519 s` on the prime-order basepoint subgroup `[i] edBasepoint` (`i < ℓ`). -/
theorem x25519_edSmul_edBasepoint (s : List (BitVec 8)) {i : Nat} (hi : i < edOrderL) :
    x25519 s (natToLeBytes 32 (edToMontU (edSmul i edBasepoint))) =
      natToLeBytes 32 (edToMontU (edSmul ((clampScalar s * i) % edOrderL) edBasepoint)) := by
  unfold x25519
  rw [← x25519Ladder_mod,
      decodeU255_natToLeBytes_edToMontU _,
      edSmul_eq_edNatSmul (Nat.lt_trans hi edOrderL_lt_two_pow_256) edOnCurve_edBasepoint,
      x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s)
        (edOnCurve_edNatSmul i edOnCurve_edBasepoint),
      ← edNatSmul_mul (clampScalar s) i edOnCurve_edBasepoint,
      ← edNatSmul_mod_edOrderL_edBasepoint (clampScalar s * i),
      ← edSmul_eq_edNatSmul
        (Nat.lt_trans (Nat.mod_lt _ edOrderL_pos) edOrderL_lt_two_pow_256)
        edOnCurve_edBasepoint]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
