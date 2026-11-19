/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards -- proof-setup: allow-public-import

/-!
# Point Codec, Scalar Clamping, & `recoverXEven` Proofs (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec`)

Pure `0-sorry` mathematical proofs for:
1. Little-endian byte serialization (`leBytesToNat`, `natToLeBytes`) and RFC 8032 scalar clamping
   (`clampScalarBytes`, `clampScalar`).
2. Soundness of `recoverXEven` (`recoverXEven_some_props`) and twisted Edwards point compression /
   decompression round-trips (`encodeEd_length`, `decodeEdRfc_encodeEd`, `decodeEdDalek_encodeEd`,
   `decodeEdDalek_of_decodeEdRfc`, `edOnCurve_of_decodeEdDalek`, `encodeEd_of_decodeEdRfc`).
3. Pure-specification headline theorems (`ed25519VerifyDalekEqRfc8032_ok` and
   `ed25519SignVerifyRoundtrip_ok`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec

open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpNeg fpMul fpSq fpPow fpInv sqrtM1 edD EdPoint edOnCurve
  leBytesToNat natToLeBytes encodeEd recoverXEven decodeEdDalek decodeEdRfc clampScalarBytes
  clampScalar)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpSub_lt fpNeg_lt fpMul_lt fpMul_assoc fpMul_one fpNeg_fpMul_fpNeg fpSq_fpNeg
  fpSq_fpMul fpSq_sqrtM1_eq_fpNeg_one fpNeg_mod_two_of_ne_zero fpEvenRep fpEvenRep_of_lt
  fpEvenRep_lt fpEvenRep_mod_two fpSq_fpEvenRep fpEvenRep_eq_zero_iff restore_sign_fpEvenRep
  recoverXEven_of_curve_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_of_fp_eq edOnCurve_curve_eq)
attribute [local irreducible] fpInv fpPow

/-! ## 1. Little-Endian Byte Codec (`leBytesToNat` / `natToLeBytes`) & Scalar Clamping -/

@[simp] private theorem natToLeBytes_length (len n : Nat) :
    (natToLeBytes len n).length = len := by
  simp [natToLeBytes]

@[simp] theorem encodeEd_length (P : EdPoint) :
    (encodeEd P).length = 32 := by
  simp [encodeEd, natToLeBytes]

theorem leBytesToNat_nil : leBytesToNat [] = 0 := rfl

theorem leBytesToNat_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    leBytesToNat (b :: bs) = leBytesToNat bs * 256 + b.toNat := rfl

theorem leBytesToNat_lt (bs : List (BitVec 8)) :
    leBytesToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leBytesToNat]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.isLt
    simp only [leBytesToNat_cons, List.length_cons, Nat.pow_succ]
    omega

private theorem getElem_leBytesToNat (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length) :
    (bs[i]'hi).toNat = (leBytesToNat bs / 256 ^ i) % 256 := by
  induction bs generalizing i with
  | nil => contradiction
  | cons b bs ih =>
    cases i with
    | zero =>
      have hb : b.toNat < 256 := b.isLt
      simp only [List.getElem_cons_zero, Nat.pow_zero, Nat.div_one, leBytesToNat_cons]
      omega
    | succ j =>
      have hj : j < bs.length := Nat.lt_of_succ_lt_succ hi
      have hb : b.toNat < 256 := b.isLt
      simp only [List.getElem_cons_succ, ih j hj, leBytesToNat_cons, Nat.pow_succ']
      rw [← Nat.div_div_eq_div_mul,
          show (leBytesToNat bs * 256 + b.toNat) / 256 = leBytesToNat bs by omega]

theorem natToLeBytes_leBytesToNat (bs : List (BitVec 8)) :
    natToLeBytes bs.length (leBytesToNat bs) = bs := by
  apply List.ext_getElem (by simp [natToLeBytes])
  intro i h1 h2
  simp only [natToLeBytes, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_mod, ← getElem_leBytesToNat bs i h2]

private theorem leBytesToNat_eq_of_natToLeBytes_eq {bs : List (BitVec 8)} {n : Nat}
    (h : bs = natToLeBytes bs.length n) (hn : n < 256 ^ bs.length) :
    leBytesToNat bs = n := by
  induction bs generalizing n with
  | nil =>
    simp [leBytesToNat] at hn ⊢
    omega
  | cons b bs ih =>
    rw [List.length_cons, Nat.pow_succ'] at hn
    have h0 : b = BitVec.ofNat 8 (n % 256) := by
      have := congrArg (fun l => l[0]?) h
      simpa [natToLeBytes] using this
    have htail : bs = natToLeBytes bs.length (n / 256) := by
      apply List.ext_getElem (by simp [natToLeBytes])
      intro i hi1 _
      have hget := congrArg (fun l => l[i + 1]?) h
      simp only [List.getElem?_cons_succ, List.getElem?_eq_getElem hi1, natToLeBytes,
        List.length_cons, List.getElem?_map, List.getElem?_range (Nat.succ_lt_succ hi1),
        Option.map_some, Option.some.injEq] at hget
      simp only [natToLeBytes, List.getElem_map, List.getElem_range]
      rw [hget, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    have ih_n := ih htail (by omega)
    simp only [leBytesToNat_cons, ih_n, h0, BitVec.toNat_ofNat]
    omega

theorem leBytesToNat_natToLeBytes_of_lt {len n : Nat} (hn : n < 256 ^ len) :
    leBytesToNat (natToLeBytes len n) = n := by
  have hlen : (natToLeBytes len n).length = len := natToLeBytes_length len n
  exact leBytesToNat_eq_of_natToLeBytes_eq (by rw [hlen]) (by rwa [hlen])

theorem clampScalarBytes_length_le (bs : List (BitVec 8)) :
    (clampScalarBytes bs).length ≤ 32 := by
  unfold clampScalarBytes
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
  omega

private theorem clampScalarBytes_length {bs : List (BitVec 8)} (h : 31 ≤ bs.length) :
    (clampScalarBytes bs).length = 32 := by
  unfold clampScalarBytes
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
  omega

theorem clampScalar_lt_two_pow_256 (bs : List (BitVec 8)) :
    clampScalar bs < 2 ^ 256 := by
  unfold clampScalar
  have hlen : (clampScalarBytes (bs.take 32)).length ≤ 32 :=
    clampScalarBytes_length_le (bs.take 32)
  have hlt := leBytesToNat_lt (clampScalarBytes (bs.take 32))
  have hpow : 256 ^ (clampScalarBytes (bs.take 32)).length ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by omega) hlen
  have h256 : 256 ^ 32 = 2 ^ 256 := by decide
  omega

/-! ## 2. Soundness of `recoverXEven` and Codec Round-Trip Lemmas -/

theorem recoverXEven_some_props {y xEven : Nat} (h : recoverXEven y = some xEven) :
    xEven < p25519 ∧
    xEven % 2 = 0 ∧
    fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq xEven) = fpSub (fpSq y) 1 := by
  unfold recoverXEven at h
  dsimp only [] at h
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
    else none) = some xEven at h
  cases h1 : check == u
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : check == fpNeg u
    · simp [h2] at h
    · simp only [h2, ↓reduceIte, Option.some.injEq] at h
      let r1 := fpMul r0 sqrtM1
      have hr1_lt : r1 < p25519 := fpMul_lt _ _
      have hx_eq : xEven = fpEvenRep r1 := by
        rw [← h, fpEvenRep_of_lt hr1_lt]
      rw [hx_eq]
      refine ⟨fpEvenRep_lt r1, fpEvenRep_mod_two r1, ?_⟩
      have hchk : check = fpNeg u := beq_iff_eq.mp h2
      have hu_lt : u < p25519 := fpSub_lt _ _
      rw [fpSq_fpEvenRep, show r1 = fpMul r0 sqrtM1 from rfl, fpSq_fpMul,
          ← fpMul_assoc, show fpMul v (fpSq r0) = check from rfl,
          hchk, fpSq_sqrtM1_eq_fpNeg_one, fpNeg_fpMul_fpNeg, fpMul_one,
          Nat.mod_eq_of_lt hu_lt]
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    have hr0_lt : r0 < p25519 := fpMul_lt _ _
    have hx_eq : xEven = fpEvenRep r0 := by
      rw [← h, fpEvenRep_of_lt hr0_lt]
    rw [hx_eq]
    refine ⟨fpEvenRep_lt r0, fpEvenRep_mod_two r0, ?_⟩
    have hchk : check = u := beq_iff_eq.mp h1
    rw [fpSq_fpEvenRep]
    exact hchk

theorem edOnCurve_of_curve_eq {P : EdPoint}
    (hx : P.x < p25519) (hy : P.y < p25519)
    (hcurve : fpMul (fpAdd (fpMul edD (fpSq P.y)) 1) (fpSq P.x) = fpSub (fpSq P.y) 1) :
    edOnCurve P = true := by
  apply edOnCurve_of_fp_eq hx hy
  have hfp := congrArg Fp.ofNat hcurve
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_one] at hfp
  grind

theorem decodeEdRfc_encodeEd {P : EdPoint} (hP : edOnCurve P = true) :
    decodeEdRfc (encodeEd P) = some P := by
  have hx : P.x < p25519 := edOnCurve_x_lt hP
  have hy : P.y < p25519 := edOnCurve_y_lt hP
  have hp_lt : p25519 < 2 ^ 255 := by unfold p25519; decide
  have h256 : 256 ^ 32 = 2 ^ 256 := by decide
  have h255_mul2 : 2 ^ 255 * 2 = 2 ^ 256 := by decide
  let sign := P.x % 2
  have hsign_lt : sign < 2 := Nat.mod_lt P.x (by omega)
  let n := P.y + sign * 2 ^ 255
  have hn_lt : n < 256 ^ 32 := by
    rw [h256]
    omega
  have henc : encodeEd P = natToLeBytes 32 n := by
    unfold encodeEd
    dsimp only []
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  unfold decodeEdRfc
  rw [encodeEd_length]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [henc, leBytesToNat_natToLeBytes_of_lt hn_lt]
  have hyRaw : n % 2 ^ 255 = P.y := by
    dsimp only [n]
    omega
  have hsignRaw : (n / 2 ^ 255) % 2 = sign := by
    dsimp only [n]
    have hdiv : (P.y + sign * 2 ^ 255) / 2 ^ 255 = sign := by omega
    rw [hdiv, Nat.mod_eq_of_lt hsign_lt]
  rw [hyRaw, hsignRaw]
  have hy_ge : ¬ (P.y ≥ p25519) := by omega
  simp only [hy_ge, ↓reduceIte]
  rw [recoverXEven_of_curve_eq (edOnCurve_curve_eq hP)]
  dsimp only []
  have hnot_neg_zero : (fpEvenRep P.x == 0 && (sign == 1)) = false := by
    cases h0 : fpEvenRep P.x == 0
    · simp
    · have hx0 : P.x = 0 := (fpEvenRep_eq_zero_iff hx).mp (beq_iff_eq.mp h0)
      simp [sign, hx0]
  rw [hnot_neg_zero]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [restore_sign_fpEvenRep hx]


@[expose] def decodeDalekWith (recFn : Nat → Option Nat) (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    let y := yRaw % p25519
    decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn y)
      (fun _ => none)
      (fun xEven =>
        let x := if sign == 1 then fpNeg xEven else xEven
        some ⟨x, y⟩)

private def decodeRfcWith (recFn : Nat → Option Nat) (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    if yRaw >= p25519 then none
    else
      decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn yRaw)
        (fun _ => none)
        (fun xEven =>
          if xEven == 0 && sign == 1 then none
          else
            let x := if sign == 1 then fpNeg xEven else xEven
            some ⟨x, yRaw⟩)

theorem decodeEdDalek_eq_with (bs : List (BitVec 8)) :
    decodeEdDalek bs = decodeDalekWith recoverXEven bs := rfl

theorem decodeDalekWith_natToLeBytes (recFn : Nat → Option Nat) (y s : Nat)
    (hy_p : y < p25519) (hy_255 : y < 2 ^ 255) (hs : s < 2) :
    decodeDalekWith recFn (natToLeBytes 32 (y + s * 2 ^ 255)) =
      (match recFn y with
       | none => none
       | some xEven =>
         let x := if s == 1 then fpNeg xEven else xEven
         some ⟨x, y⟩) := by
  unfold decodeDalekWith
  have hlen : (natToLeBytes 32 (y + s * 2 ^ 255)).length = 32 := natToLeBytes_length 32 _
  have hlt256 : y + s * 2 ^ 255 < 256 ^ 32 := by
    have : 256 ^ 32 = 2 * 2 ^ 255 := by decide
    omega
  have hleb := leBytesToNat_natToLeBytes_of_lt hlt256
  have hyraw : (y + s * 2 ^ 255) % (2 ^ 255) = y := by omega
  have hsign : ((y + s * 2 ^ 255) / (2 ^ 255)) % 2 = s := by omega
  have hne : ((natToLeBytes 32 (y + s * 2 ^ 255)).length != 32) = false := by rw [hlen]; rfl
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, hleb, hyraw, Nat.mod_eq_of_lt hy_p, hsign]
  cases recFn y <;> rfl

private theorem decodeEdRfc_eq_with (bs : List (BitVec 8)) :
    decodeEdRfc bs = decodeRfcWith recoverXEven bs := rfl

private theorem decodeDalekWith_of_decodeRfcWith (recFn : Nat → Option Nat)
    {bs : List (BitVec 8)} {P : EdPoint}
    (h : decodeRfcWith recFn bs = some P) :
    decodeDalekWith recFn bs = some P := by
  unfold decodeRfcWith at h
  unfold decodeDalekWith
  by_cases hlen : (bs.length != 32) = true
  · simp [hlen] at h
  · simp only [Bool.eq_false_of_ne_true hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hy : leBytesToNat bs % (2 ^ 255) >= p25519
    · simp [hy] at h
    · simp only [hy, ↓reduceIte] at h
      have hy_lt : leBytesToNat bs % (2 ^ 255) < p25519 := Nat.lt_of_not_le hy
      rw [Nat.mod_eq_of_lt hy_lt]
      cases hrec : recFn (leBytesToNat bs % (2 ^ 255)) with
      | none =>
        rw [hrec] at h
        dsimp only [decodeEdDalek.match_1] at h
        nomatch h
      | some xEven =>
        rw [hrec] at h
        dsimp only [decodeEdDalek.match_1] at h ⊢
        cases hnz : (xEven == 0 && ((leBytesToNat bs / (2 ^ 255)) % 2 == 1))
        · rw [hnz] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact h
        · simp [hnz] at h

private theorem edOnCurve_of_decodeDalekWith (recFn : Nat → Option Nat)
    (hprops : ∀ y xEven, recFn y = some xEven →
      xEven < p25519 ∧ xEven % 2 = 0 ∧
      fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq xEven) = fpSub (fpSq y) 1)
    {bs : List (BitVec 8)} {P : EdPoint}
    (h : decodeDalekWith recFn bs = some P) :
    edOnCurve P = true := by
  unfold decodeDalekWith at h
  by_cases hlen : (bs.length != 32) = true
  · simp [hlen] at h
  · simp only [Bool.eq_false_of_ne_true hlen, Bool.false_eq_true, ↓reduceIte] at h
    have hy_lt : (leBytesToNat bs % (2 ^ 255)) % p25519 < p25519 := Nat.mod_lt _ p25519_pos
    cases hrec : recFn ((leBytesToNat bs % (2 ^ 255)) % p25519) with
    | none =>
      rw [hrec] at h
      dsimp only [decodeEdDalek.match_1] at h
      nomatch h
    | some xEven =>
      rw [hrec] at h
      dsimp only [decodeEdDalek.match_1] at h
      injection h with hP
      obtain ⟨hx_lt, _, hcurve⟩ := hprops _ xEven hrec
      subst hP
      cases (leBytesToNat bs / (2 ^ 255)) % 2 == 1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact edOnCurve_of_curve_eq hx_lt hy_lt hcurve
      · simp only [↓reduceIte]
        apply edOnCurve_of_curve_eq (fpNeg_lt xEven) hy_lt
        dsimp only []
        rwa [fpSq_fpNeg]

private theorem encodeEd_of_decodeRfcWith (recFn : Nat → Option Nat)
    (hprops : ∀ y xEven, recFn y = some xEven →
      xEven < p25519 ∧ xEven % 2 = 0 ∧
      fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq xEven) = fpSub (fpSq y) 1)
    {bs : List (BitVec 8)} {P : EdPoint}
    (hbs : bs.length = 32) (h : decodeRfcWith recFn bs = some P) :
    encodeEd P = bs := by
  unfold decodeRfcWith at h
  have hlen : (bs.length != 32) = false := by simp [hbs]
  simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hy : leBytesToNat bs % (2 ^ 255) >= p25519
  · simp [hy] at h
  · simp only [hy, ↓reduceIte] at h
    have hy_lt : leBytesToNat bs % (2 ^ 255) < p25519 := Nat.lt_of_not_le hy
    cases hrec : recFn (leBytesToNat bs % (2 ^ 255)) with
    | none =>
      rw [hrec] at h
      dsimp only [decodeEdDalek.match_1] at h
      nomatch h
    | some xEven =>
      rw [hrec] at h
      dsimp only [decodeEdDalek.match_1] at h
      obtain ⟨hx_lt, hx_even, _⟩ := hprops _ xEven hrec
      cases hnz : (xEven == 0 && ((leBytesToNat bs / (2 ^ 255)) % 2 == 1))
      · rw [hnz] at h
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hn_lt : leBytesToNat bs < 2 ^ 256 := by
          have hlt := leBytesToNat_lt bs
          rw [hbs, show 256 ^ 32 = 2 ^ 256 by decide] at hlt
          exact hlt
        have hdiv_lt : leBytesToNat bs / (2 ^ 255) < 2 := by
          have : 2 ^ 256 = 2 * 2 ^ 255 := by decide
          omega
        have hsign_eq : (leBytesToNat bs / (2 ^ 255)) % 2 = leBytesToNat bs / (2 ^ 255) :=
          Nat.mod_eq_of_lt hdiv_lt
        have hsign_cases :
            (leBytesToNat bs / (2 ^ 255)) % 2 = 0 ∨ (leBytesToNat bs / (2 ^ 255)) % 2 = 1 := by omega
        have hn_decomp :
            leBytesToNat bs % (2 ^ 255) + ((leBytesToNat bs / (2 ^ 255)) % 2) * (2 ^ 255) = leBytesToNat bs := by
          rw [hsign_eq]
          have := Nat.div_add_mod (leBytesToNat bs) (2 ^ 255)
          omega
        have hx_sign :
            ((if ((leBytesToNat bs / (2 ^ 255)) % 2 == 1) = true then fpNeg xEven else xEven) % p25519) % 2 =
              (leBytesToNat bs / (2 ^ 255)) % 2 := by
          rcases hsign_cases with hs0 | hs1
          · simp only [hs0, show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte,
              Nat.mod_eq_of_lt hx_lt, hx_even]
          · simp only [hs1, beq_self_eq_true, ↓reduceIte]
            have hx_ne0 : xEven ≠ 0 := by
              intro hx0
              simp [hx0, hs1] at hnz
            have hx_mod_ne0 : xEven % p25519 ≠ 0 := by
              rwa [Nat.mod_eq_of_lt hx_lt]
            rw [Nat.mod_eq_of_lt (fpNeg_lt xEven), fpNeg_mod_two_of_ne_zero hx_mod_ne0,
                Nat.mod_eq_of_lt hx_lt, hx_even]
        have hsum :
            (leBytesToNat bs % (2 ^ 255)) % p25519 +
              (((if ((leBytesToNat bs / (2 ^ 255)) % 2 == 1) = true then fpNeg xEven else xEven) % p25519) % 2) *
                (2 ^ 255) = leBytesToNat bs := by
          rw [Nat.mod_eq_of_lt hy_lt, hx_sign]
          exact hn_decomp
        unfold encodeEd
        dsimp only []
        exact (congrArg (natToLeBytes 32) hsum).trans (hbs ▸ natToLeBytes_leBytesToNat bs)
      · simp [hnz] at h

attribute [local irreducible] decodeDalekWith decodeRfcWith recoverXEven

theorem decodeEdDalek_of_decodeEdRfc {bs : List (BitVec 8)} {P : EdPoint}
    (h : decodeEdRfc bs = some P) :
    decodeEdDalek bs = some P := by
  rw [decodeEdRfc_eq_with] at h
  rw [decodeEdDalek_eq_with]
  exact decodeDalekWith_of_decodeRfcWith recoverXEven h

theorem decodeEdDalek_encodeEd {P : EdPoint} (hP : edOnCurve P = true) :
    decodeEdDalek (encodeEd P) = some P :=
  decodeEdDalek_of_decodeEdRfc (decodeEdRfc_encodeEd hP)

theorem edOnCurve_of_decodeEdDalek {bs : List (BitVec 8)} {P : EdPoint}
    (h : decodeEdDalek bs = some P) :
    edOnCurve P = true := by
  rw [decodeEdDalek_eq_with] at h
  exact edOnCurve_of_decodeDalekWith recoverXEven (fun _ _ hr => recoverXEven_some_props hr) h

theorem edOnCurve_of_decodeEdRfc {bs : List (BitVec 8)} {P : EdPoint}
    (h : decodeEdRfc bs = some P) :
    edOnCurve P = true :=
  edOnCurve_of_decodeEdDalek (decodeEdDalek_of_decodeEdRfc h)

theorem encodeEd_of_decodeEdRfc {bs : List (BitVec 8)} {P : EdPoint}
    (hbs : bs.length = 32) (h : decodeEdRfc bs = some P) :
    encodeEd P = bs := by
  rw [decodeEdRfc_eq_with] at h
  exact encodeEd_of_decodeRfcWith recoverXEven (fun _ _ hr => recoverXEven_some_props hr) hbs h


theorem edOrderL_pos : 0 < edOrderL := by
  unfold edOrderL; decide

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
