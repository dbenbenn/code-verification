/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec

/-!
# Curve25519 Bridges for Symbolic Refinement

Bridges `dalekPrimsRef` and `montLiftEd` (`Phase4RefBridge`) without importing `Symbolic.*`:
little-endian byte-list recursions, `decodeU255`, algebraic zero-`fpInv` Montgomery lifts,
Curve25519 8-torsion shift rejection, closed-form torsion rejection on `ekATorsionNat`
(`compEkATorsion`), and closed-form lift and torsion-free witnesses for `u = 9`, `ekAPubNat`,
`toEdIn0Nat`, `toEdIn1Nat`, and `toEdIn2Nat`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge

open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpMul fpNeg fpSq fpInv edD recoverXEven
  leBytesToNat natToLeBytes EdPoint EdExtPoint edZero edExtZero edBasepoint
  edOnCurve edAdd edNeg edSmul edExtSmulLoop edExtToAffine edExtOfAffine
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  DalekPrims montLiftEd signalMontLiftEd_eq natToLeBytes_len encEd160 decEd160 dalekPrimsRef
  montLiftEd_eq_montToEdwards montLiftEd_some_onCurve decEd160_encEd160_of_onCurve edSmul_edNeg
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (
  fpAdd_lt fpSq_lt fpAdd_comm zero_fpMul fpInv_mod_p fpInv_ne_zero fpMul_ne_zero
  fpMul_fpInv_cancel fpMul_cancel_left fpInv_eq_of_fpMul_eq_one fpSq_eq_fpSq_iff
  fpAdd_one_edD_fpSq_ne_zero
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  EdPoint.ext edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edBasepoint
  edOnCurve_edNeg edOnCurve_curve_eq edOnCurve_edAdd edAdd_edZero edZero_edAdd
  edAdd_edNeg_self edNeg_edZero edNeg_edNeg edAdd_assoc
  edNatSmul edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one
  edNatSmul_add edNatSmul_mul edNatSmul_edAdd
  edSmul_eq_edNatSmul edSmul_edOrderL_edBasepoint edOrderL_lt_two_pow_256
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (
  edToMontU edToMontU_edBasepoint birational_y_of_u edOnCurve_eq_edZero_iff_y_eq_one
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero
  montToEdwards_some_edToMontU decodeU255_natToLeBytes_of_lt montToEdwards_edToMontU
  edBasepoint_ne_edZero
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_nil leBytesToNat_cons
)

/-! ## 1. Little-Endian Codec, `decodeU255`, & `montLiftEd` Congruence Bridges -/

/-- Any structural byte-list evaluator `f [] = 0`, `f (b :: bs) = b.toNat + 256 * f bs`
agrees with `leBytesToNat`. -/
theorem leBytesToNat_eq_rec (f : List (BitVec 8) → Nat)
    (hnil : f [] = 0)
    (hcons : ∀ b bs, f (b :: bs) = b.toNat + 256 * f bs)
    (bs : List (BitVec 8)) :
    f bs = leBytesToNat bs := by
  induction bs with
  | nil => rw [hnil, leBytesToNat_nil]
  | cons b tl ih => rw [hcons, ih, leBytesToNat_cons]; omega

/-- Any `List Nat` little-endian evaluator (such as `Symbolic`'s `DY.X25519.leValue`) applied to
`bs.map BitVec.toNat` equals `leBytesToNat bs`. -/
theorem leBytesToNat_eq_nat_rec (g : List Nat → Nat)
    (hnil : g [] = 0)
    (hcons : ∀ x xs, g (x :: xs) = x + 256 * g xs)
    (bs : List (BitVec 8)) :
    g (bs.map BitVec.toNat) = leBytesToNat bs :=
  leBytesToNat_eq_rec (fun l => g (l.map BitVec.toNat)) hnil
    (fun b l => hcons b.toNat (l.map BitVec.toNat)) bs

theorem natToLeBytes_zero (w : Nat) : natToLeBytes 0 w = [] := rfl

theorem natToLeBytes_succ (n w : Nat) :
    natToLeBytes (n + 1) w = BitVec.ofNat 8 w :: natToLeBytes n (w / 256) := by
  unfold natToLeBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  · apply List.map_congr_left
    intro i _
    change BitVec.ofNat 8 ((w / 256 ^ (i + 1)) % 256) =
      BitVec.ofNat 8 (((w / 256) / 256 ^ i) % 256)
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]

/-- Any structural little-endian encoder (such as `Symbolic`'s `leBytes`) agrees with
`natToLeBytes`. -/
theorem eq_natToLeBytes_of_rec (enc : Nat → Nat → List (BitVec 8))
    (h0 : ∀ w, enc 0 w = [])
    (hsucc : ∀ n w, enc (n + 1) w = BitVec.ofNat 8 w :: enc n (w / 256))
    (n w : Nat) :
    enc n w = natToLeBytes n w := by
  induction n generalizing w with
  | zero => rw [h0, natToLeBytes_zero]
  | succ k ih => rw [hsucc, natToLeBytes_succ, ih]

/-- On 32-byte lists, `decodeU255 bs` is `leBytesToNat bs % 2 ^ 255`. -/
theorem decodeU255_of_length_32 {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    decodeU255 bs = leBytesToNat bs % (2 ^ 255) := by
  unfold decodeU255
  rw [List.take_of_length_le (by omega)]

/-- Direct bridge from a `List Nat` little-endian evaluator modulo `2 ^ 255` to `decodeU255`
on 32-byte lists. -/
theorem decodeU255_eq_nat_rec_of_length_32 (g : List Nat → Nat)
    (hnil : g [] = 0)
    (hcons : ∀ x xs, g (x :: xs) = x + 256 * g xs)
    {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    g (bs.map BitVec.toNat) % (2 ^ 255) = decodeU255 bs := by
  rw [leBytesToNat_eq_nat_rec g hnil hcons bs, decodeU255_of_length_32 hlen]

/-- Direct bridge from `Symbolic`'s `uCoord (bs.map BitVec.toNat)` (`g (...) % 2^255 % p25519`)
to `decodeU255 bs % p25519` on 32-byte lists. -/
theorem decodeU255_mod_p_eq_nat_rec_of_length_32 (g : List Nat → Nat)
    (hnil : g [] = 0)
    (hcons : ∀ x xs, g (x :: xs) = x + 256 * g xs)
    {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    g (bs.map BitVec.toNat) % (2 ^ 255) % p25519 = decodeU255 bs % p25519 := by
  rw [decodeU255_eq_nat_rec_of_length_32 g hnil hcons hlen]

/-- Congruence of `montLiftEd` under equal `decodeU255 _ % p25519` and equal low sign bit. -/
theorem montLiftEd_congr_decodeU255_mod_p {u1 u2 : List.Vector (BitVec 8) 32}
    {s1 s2 : BitVec 8}
    (hu : decodeU255 u1.toList % p25519 = decodeU255 u2.toList % p25519)
    (hs : (s1 &&& 1#8) = (s2 &&& 1#8)) :
    montLiftEd u1 s1 = montLiftEd u2 s2 := by
  have hu1 : leBytesToNat u1.toList % (2 ^ 255) = decodeU255 u1.toList :=
    (decodeU255_of_length_32 u1.2).symm
  have hu2 : leBytesToNat u2.toList % (2 ^ 255) = decodeU255 u2.toList :=
    (decodeU255_of_length_32 u2.2).symm
  unfold montLiftEd
  rw [hu1, hu2, hu, hs]

/-- Congruence of `montLiftEd` under equal `decodeU255` and equal low sign bit `sign &&& 1#8`. -/
theorem montLiftEd_congr_decodeU255 {u1 u2 : List.Vector (BitVec 8) 32} {s1 s2 : BitVec 8}
    (hu : decodeU255 u1.toList = decodeU255 u2.toList)
    (hs : (s1 &&& 1#8) = (s2 &&& 1#8)) :
    montLiftEd u1 s1 = montLiftEd u2 s2 :=
  montLiftEd_congr_decodeU255_mod_p (congrArg (· % p25519) hu) hs

/-- If `montLiftEd` succeeds with low sign bit `0`, flipping the low sign bit to `1` negates the
lifted Edwards point. -/
theorem montLiftEd_odd_eq_edNeg_of_even {u1 u2 : List.Vector (BitVec 8) 32}
    {s0 s1 : BitVec 8} {P : EdPoint}
    (hu : decodeU255 u1.toList % p25519 = decodeU255 u2.toList % p25519)
    (hs0 : (s0 &&& 1#8) = 0#8)
    (hs1 : (s1 &&& 1#8) = 1#8)
    (hlift : montLiftEd u1 s0 = some P) :
    montLiftEd u2 s1 = some (edNeg P) := by
  have hy_lt : P.y < p25519 := by
    have hon : edOnCurve P = true := by
      rw [montLiftEd_eq_montToEdwards] at hlift
      exact montToEdwards_some_onCurve hlift
    exact edOnCurve_y_lt hon
  have hu1 : (leBytesToNat u1.toList % (2 ^ 255)) % p25519 = decodeU255 u1.toList % p25519 :=
    congrArg (· % p25519) (decodeU255_of_length_32 u1.2).symm
  have hu2 : (leBytesToNat u2.toList % (2 ^ 255)) % p25519 = decodeU255 u1.toList % p25519 :=
    (congrArg (· % p25519) (decodeU255_of_length_32 u2.2).symm).trans hu.symm
  unfold montLiftEd at hlift ⊢
  rw [hu1, hs0] at hlift
  rw [hu2, hs1]
  by_cases hc : (decodeU255 u1.toList % p25519 == p25519 - 1) = true
  · simp only [hc, ↓reduceIte] at hlift
    cases hlift
  · simp only [hc, Bool.false_eq_true, ↓reduceIte,
      show (0#8 == 1#8) = false by decide, show (1#8 == 1#8) = true by decide,
      Option.map_eq_some_iff] at hlift ⊢
    rcases hlift with ⟨xEven, hrec, hP⟩
    have hxP : P.x = xEven := (congrArg EdPoint.x hP).symm
    have hyP : P.y = fpMul (fpSub (decodeU255 u1.toList % p25519) 1)
        (fpInv (fpAdd (decodeU255 u1.toList % p25519) 1)) :=
      (congrArg EdPoint.y hP).symm
    refine ⟨xEven, hrec, ?_⟩
    apply EdPoint.ext
    · dsimp only [edNeg]
      rw [hxP]
    · dsimp only [edNeg]
      rw [Nat.mod_eq_of_lt hy_lt, hyP]

private theorem dalekPrimsRef_montToEd_def (u : List.Vector (BitVec 8) 32) (s : BitVec 8) :
    dalekPrimsRef.montToEd u s = (montLiftEd u s).map encEd160 := rfl

private theorem dalekPrims_mk_isTorsionFree (f1 f2 f3 f4 f5 f6 f7)
    (v : List.Vector (BitVec 8) 160) :
    (DalekPrims.mk f1 f2 f3 f4 f5 f6 f7).isTorsionFree v = f4 v := rfl

private theorem dalekPrimsRef_isTorsionFree_def (v : List.Vector (BitVec 8) 160) :
    dalekPrimsRef.isTorsionFree v = (edSmul edOrderL (decEd160 v) == edZero) :=
  (congrArg (fun d => d.isTorsionFree v) dalekPrimsRef.eq_1).trans
    (dalekPrims_mk_isTorsionFree _ _ _ _ _ _ _ v)

attribute [local irreducible] fpInv recoverXEven montLiftEd montToEdwards dalekPrimsRef

/-- Congruence of `dalekPrimsRef.montToEd` under equal `decodeU255 _ % p25519` and sign bit. -/
theorem dalekPrimsRef_montToEd_congr_decodeU255_mod_p {u1 u2 : List.Vector (BitVec 8) 32}
    {s1 s2 : BitVec 8}
    (hu : decodeU255 u1.toList % p25519 = decodeU255 u2.toList % p25519)
    (hs : (s1 &&& 1#8) = (s2 &&& 1#8)) :
    dalekPrimsRef.montToEd u1 s1 = dalekPrimsRef.montToEd u2 s2 := by
  rw [dalekPrimsRef_montToEd_def, dalekPrimsRef_montToEd_def,
    montLiftEd_congr_decodeU255_mod_p hu hs]

/-- Congruence of `dalekPrimsRef.montToEd` under equal `decodeU255` and equal low sign bit. -/
theorem dalekPrimsRef_montToEd_congr_decodeU255 {u1 u2 : List.Vector (BitVec 8) 32}
    {s1 s2 : BitVec 8}
    (hu : decodeU255 u1.toList = decodeU255 u2.toList)
    (hs : (s1 &&& 1#8) = (s2 &&& 1#8)) :
    dalekPrimsRef.montToEd u1 s1 = dalekPrimsRef.montToEd u2 s2 :=
  dalekPrimsRef_montToEd_congr_decodeU255_mod_p (congrArg (· % p25519) hu) hs

theorem dalekPrimsRef_montToEd_eq_some_iff {u : List.Vector (BitVec 8) 32} {s : BitVec 8}
    {pt : List.Vector (BitVec 8) 160} :
    dalekPrimsRef.montToEd u s = some pt ↔ ∃ P, montLiftEd u s = some P ∧ encEd160 P = pt := by
  rw [dalekPrimsRef_montToEd_def, Option.map_eq_some_iff]

theorem dalekPrimsRef_montToEd_toList_length {u : List.Vector (BitVec 8) 32} {s : BitVec 8}
    {out : List (BitVec 8)}
    (h : (dalekPrimsRef.montToEd u s).map List.Vector.toList = some out) :
    out.length = 160 := by
  rw [Option.map_eq_some_iff] at h
  rcases h with ⟨pt, _, rfl⟩
  exact pt.2

theorem dalekPrimsRef_isTorsionFree_encEd160_of_onCurve {P : EdPoint} (hP : edOnCurve P = true) :
    dalekPrimsRef.isTorsionFree (encEd160 P) = (edSmul edOrderL P == edZero) :=
  (dalekPrimsRef_isTorsionFree_def (encEd160 P)).trans
    (congrArg (fun Q => edSmul edOrderL Q == edZero) (decEd160_encEd160_of_onCurve hP))

/-! ## 2. Zero-`fpInv` Algebraic Lift, Extended-Coordinate Torsion, & Curve Torsion Rejection -/

theorem montLiftEd_some_props {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {P : EdPoint}
    (h : montLiftEd u s = some P) :
    edOnCurve P = true ∧ P ≠ edZero ∧ edToMontU P = decodeU255 u.toList % p25519 := by
  rw [montLiftEd_eq_montToEdwards] at h
  exact ⟨montToEdwards_some_onCurve h, montToEdwards_some_ne_edZero h,
    montToEdwards_some_edToMontU h⟩

/-- Two non-identity curve points with equal Montgomery `u`-coordinate are equal or negatives. -/
theorem edPoint_eq_or_edNeg_of_edToMontU_eq {A B : EdPoint}
    (hA : edOnCurve A = true) (hB : edOnCurve B = true)
    (hneA : A ≠ edZero) (hneB : B ≠ edZero)
    (hu : edToMontU A = edToMontU B) :
    A = B ∨ A = edNeg B := by
  have hyA1 : A.y ≠ 1 := fun h1 => hneA ((edOnCurve_eq_edZero_iff_y_eq_one hA).mpr h1)
  have hyB1 : B.y ≠ 1 := fun h1 => hneB ((edOnCurve_eq_edZero_iff_y_eq_one hB).mpr h1)
  have hy : A.y = B.y := by
    have h1 := birational_y_of_u (edOnCurve_y_lt hA) hyA1
    have h2 := birational_y_of_u (edOnCurve_y_lt hB) hyB1
    dsimp only [] at h1 h2
    change fpMul (fpSub (edToMontU A) 1) (fpInv (fpAdd (edToMontU A) 1)) = A.y at h1
    change fpMul (fpSub (edToMontU B) 1) (fpInv (fpAdd (edToMontU B) 1)) = B.y at h2
    rw [← h1, ← h2, hu]
  have hcurvA := edOnCurve_curve_eq hA
  have hcurvB := edOnCurve_curve_eq hB
  rw [hy] at hcurvA
  have hden_ne : fpAdd (fpMul edD (fpSq B.y)) 1 % p25519 ≠ 0 := by
    rw [fpAdd_comm, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_edD_fpSq_ne_zero B.y
  have hsq_mod : fpSq A.x % p25519 = fpSq B.x % p25519 :=
    (fpMul_cancel_left hden_ne).mp (hcurvA.trans hcurvB.symm)
  have hsq : fpSq A.x = fpSq B.x := by
    rw [Nat.mod_eq_of_lt (fpSq_lt _), Nat.mod_eq_of_lt (fpSq_lt _)] at hsq_mod
    exact hsq_mod
  have hxA := edOnCurve_x_lt hA
  have hxB := edOnCurve_x_lt hB
  have hyB := edOnCurve_y_lt hB
  rcases (fpSq_eq_fpSq_iff A.x B.x).mp hsq with hxeq | hxneg
  · left
    rw [Nat.mod_eq_of_lt hxA, Nat.mod_eq_of_lt hxB] at hxeq
    exact EdPoint.ext hxeq hy
  · right
    rw [Nat.mod_eq_of_lt hxA] at hxneg
    exact EdPoint.ext hxneg (by simp [edNeg, hy, Nat.mod_eq_of_lt hyB])

private theorem nat_lt_two_cases {n : Nat} (h : n < 2) : n = 0 ∨ n = 1 := by omega

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide

private theorem bv8_and_one_dichotomy (s : BitVec 8) :
    (s &&& 1#8) = 0#8 ∨ (s &&& 1#8) = 1#8 := by
  have hlt : (s &&& 1#8).toNat < 2 := by
    rw [BitVec.toNat_and]
    change s.toNat &&& (2 ^ 1 - 1) < 2
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  rcases nat_lt_two_cases hlt with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq h0
  · right; exact BitVec.eq_of_toNat_eq h1

/-- Zero-`fpInv` Montgomery-to-Edwards lift witness theorem: given `P` on the curve with `P ≠ edZero`,
`P.x % 2 = 0`, and an explicit inverse witness `inv1my` for `1 - P.y`, `montLiftEd` evaluates to
`some P` on even sign and `some (edNeg P)` on odd sign without unfolding `fpInv` or `recoverXEven`. -/
theorem montLiftEd_eq_some_of_witness {uNat inv1my : Nat} {P : EdPoint}
    (hu_lt : uNat < p25519)
    (hinv_lt : inv1my < p25519)
    (hP : edOnCurve P = true)
    (hne : P ≠ edZero)
    (hpar : P.x % 2 = 0)
    (hinv : fpMul (fpSub 1 P.y) inv1my = 1)
    (hu_eq : fpMul (fpAdd 1 P.y) inv1my = uNat) :
    (∀ (u : List.Vector (BitVec 8) 32) (s : BitVec 8),
      decodeU255 u.toList % p25519 = uNat → (s &&& 1#8) = 0#8 → montLiftEd u s = some P) ∧
    (∀ (u : List.Vector (BitVec 8) 32) (s : BitVec 8),
      decodeU255 u.toList % p25519 = uNat → (s &&& 1#8) = 1#8 → montLiftEd u s = some (edNeg P)) := by
  have hfpInv : fpInv (fpSub 1 P.y) = inv1my := by
    rw [fpInv_eq_of_fpMul_eq_one hinv, Nat.mod_eq_of_lt hinv_lt]
  have hmontU : edToMontU P = uNat := by
    unfold edToMontU
    rw [hfpInv, hu_eq]
  let uRef : List.Vector (BitVec 8) 32 := ⟨natToLeBytes 32 uNat, natToLeBytes_len 32 uNat⟩
  have huRef_dec : decodeU255 uRef.toList % p25519 = uNat := by
    change decodeU255 (natToLeBytes 32 uNat) % p25519 = uNat
    rw [decodeU255_natToLeBytes_of_lt (Nat.lt_trans hu_lt p25519_lt_two_pow_255),
      Nat.mod_eq_of_lt hu_lt]
  have href_lift : montLiftEd uRef 0#8 = some P := by
    rw [montLiftEd_eq_montToEdwards]
    change montToEdwards (natToLeBytes 32 uNat) 0 = some P
    have hm := montToEdwards_edToMontU hP hne
    rw [hmontU, hpar] at hm
    exact hm
  refine ⟨?_, ?_⟩
  · intro u s hu hs
    have hs' : (s &&& 1#8) = (0#8 &&& 1#8) := hs.trans (by decide)
    rw [montLiftEd_congr_decodeU255_mod_p (hu.trans huRef_dec.symm) hs']
    exact href_lift
  · intro u s hu hs
    have h0 : (0#8 &&& 1#8) = 0#8 := by decide
    exact montLiftEd_odd_eq_edNeg_of_even (huRef_dec.trans hu.symm) h0 hs href_lift

/-- Zero-`fpInv` extended-coordinate positive criterion for `edSmul edOrderL P = edZero`. -/
theorem edSmul_edOrderL_eq_edZero_of_extLoop {P : EdPoint}
    (h : let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine P) edExtZero
         Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0) :
    edSmul edOrderL P = edZero := by
  rcases h with ⟨hX, hYZ, hZ⟩
  unfold edSmul edExtToAffine edZero
  dsimp only []
  apply EdPoint.ext
  · rw [hX, zero_fpMul]
  · rw [hYZ, fpMul_fpInv_cancel hZ]

/-- Zero-`fpInv` extended-coordinate negative criterion for `edSmul edOrderL P ≠ edZero`. -/
theorem edSmul_edOrderL_ne_edZero_of_extLoop {P : EdPoint}
    (h : let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine P) edExtZero
         Q.X % p25519 ≠ 0 ∧ Q.Z % p25519 ≠ 0) :
    edSmul edOrderL P ≠ edZero := by
  rcases h with ⟨hX, hZ⟩
  intro heq
  have hx0 : (edSmul edOrderL P).x = 0 := congrArg EdPoint.x heq
  unfold edSmul edExtToAffine at hx0
  dsimp only [] at hx0
  have hinv_ne : fpInv (edExtSmulLoop 256 edOrderL (edExtOfAffine P) edExtZero).Z % p25519 ≠ 0 := by
    rw [fpInv_mod_p]
    exact fpInv_ne_zero hZ
  exact fpMul_ne_zero hX hinv_ne hx0

attribute [local irreducible] edSmul

theorem edSmul_edOrderL_edNeg_eq_edZero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    (edSmul edOrderL (edNeg P) == edZero) = (edSmul edOrderL P == edZero) := by
  rw [edSmul_edNeg edOrderL_lt_two_pow_256 hP]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h1 := congrArg edNeg h
    have honL : edOnCurve (edSmul edOrderL P) = true := by
      rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP]
      exact edOnCurve_edNatSmul edOrderL hP
    rw [edNeg_edNeg honL, edNeg_edZero] at h1
    exact h1
  · intro h
    rw [h, edNeg_edZero]

private theorem five_mul_edOrderL_eq_eight_mul_add_one :
    5 * edOrderL = 8 * ((5 * edOrderL) / 8) + 1 := by
  unfold edOrderL; decide

private theorem edNatSmul_eq_edZero_of_eight_and_edOrderL {T : EdPoint}
    (hT : edOnCurve T = true)
    (h8 : edNatSmul 8 T = edZero)
    (hL : edNatSmul edOrderL T = edZero) :
    T = edZero := by
  have h5L : edNatSmul (5 * edOrderL) T = edZero := by
    rw [edNatSmul_mul 5 edOrderL hT, hL, edNatSmul_edZero]
  have h8k : edNatSmul (8 * ((5 * edOrderL) / 8)) T = edZero := by
    rw [Nat.mul_comm, edNatSmul_mul ((5 * edOrderL) / 8) 8 hT, h8, edNatSmul_edZero]
  rw [five_mul_edOrderL_eq_eight_mul_add_one,
    edNatSmul_add (8 * ((5 * edOrderL) / 8)) 1 hT, h8k, edNatSmul_one hT,
    edZero_edAdd hT] at h5L
  exact h5L

/-- General Curve25519 8-torsion shift rejection: for any torsion-free curve point `P_pk ≠ edZero`
(`[ℓ] P_pk = O`) and 8-torsion curve point `T` (`[8] T = O`) whose sum `P_pk + T` changes the
Montgomery `u`-coordinate, `dalekPrimsRef.isTorsionFree` rejects every `montToEd` lift of
`edToMontU (edAdd P_pk T)`. -/
theorem dalekPrimsRef_torsionShift_rejected_of_onCurve {P_pk T : EdPoint}
    (hP : edOnCurve P_pk = true) (hneP : P_pk ≠ edZero)
    (hLP : edSmul edOrderL P_pk = edZero)
    (hT : edOnCurve T = true) (h8T : edSmul 8 T = edZero)
    (hu_ne : edToMontU (edAdd P_pk T) ≠ edToMontU P_pk)
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = edToMontU (edAdd P_pk T))
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = false := by
  rcases dalekPrimsRef_montToEd_eq_some_iff.mp hmont with ⟨R, hlift, rfl⟩
  rcases montLiftEd_some_props hlift with ⟨hR, hneR, huR⟩
  rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve hR]
  have hQ_on : edOnCurve (edAdd P_pk T) = true := edOnCurve_edAdd hP hT
  have hLP_nat : edNatSmul edOrderL P_pk = edZero := by
    rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP]; exact hLP
  have h8T_nat : edNatSmul 8 T = edZero := by
    rw [← edSmul_eq_edNatSmul (by decide) hT]; exact h8T
  have hQ_ne : edAdd P_pk T ≠ edZero := by
    intro hQ0
    have hP_eq_negT : P_pk = edNeg T := by
      have h1 := congrArg (fun X => edAdd X (edNeg T)) hQ0
      change edAdd (edAdd P_pk T) (edNeg T) = edAdd edZero (edNeg T) at h1
      rw [edAdd_assoc hP hT (edOnCurve_edNeg hT), edAdd_edNeg_self hT,
        edAdd_edZero hP, edZero_edAdd (edOnCurve_edNeg hT)] at h1
      exact h1
    have h8P : edNatSmul 8 P_pk = edZero := by
      have hs : edSmul 8 P_pk = edZero := by
        rw [hP_eq_negT, edSmul_edNeg (by decide) hT, h8T, edNeg_edZero]
      rw [← edSmul_eq_edNatSmul (by decide) hP]; exact hs
    exact hneP (edNatSmul_eq_edZero_of_eight_and_edOrderL hP h8P hLP_nat)
  have hR_eq := edPoint_eq_or_edNeg_of_edToMontU_eq hR hQ_on hneR hQ_ne (huR.trans hu)
  have hLQ_ne : (edSmul edOrderL (edAdd P_pk T) == edZero) = false := by
    apply Bool.eq_false_iff.mpr
    intro hbeq
    have hLQ : edNatSmul edOrderL (edAdd P_pk T) = edZero := by
      rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hQ_on]
      exact beq_iff_eq.mp hbeq
    rw [edNatSmul_edAdd edOrderL hP hT, hLP_nat,
      edZero_edAdd (edOnCurve_edNatSmul edOrderL hT)] at hLQ
    have hT0 : T = edZero := edNatSmul_eq_edZero_of_eight_and_edOrderL hT h8T_nat hLQ
    rw [hT0, edAdd_edZero hP] at hu_ne
    exact hu_ne rfl
  rcases hR_eq with rfl | rfl
  · exact hLQ_ne
  · rw [edSmul_edOrderL_edNeg_eq_edZero_iff hQ_on]
    exact hLQ_ne

/-! ## 3. Closed-Form Torsion Rejection on `ekATorsionNat` (`compEkATorsion`) -/

/-- 8-torsion-shifted ephemeral public key `compEkATorsion` u-coordinate. -/
@[expose] def ekATorsionNat : Nat :=
  0x7a88b2f8abf8cf55bbf89780412fb7004b64bde0e16095c1234eddde08497135

/-- Alice's ephemeral public key `compEkAPub` u-coordinate. -/
@[expose] def ekAPubNat : Nat :=
  0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab

/-- Recorded X25519 public key `compToEdIn0` (`compPubOfIdx 4`) u-coordinate. -/
@[expose] def toEdIn0Nat : Nat :=
  0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7

/-- Recorded X25519 public key `compToEdIn1` (`compPubOfIdx 6`) u-coordinate. -/
@[expose] def toEdIn1Nat : Nat :=
  0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f

/-- Recorded X25519 public key `compToEdIn2` (`compPubOfIdx 9`) u-coordinate. -/
@[expose] def toEdIn2Nat : Nat :=
  0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897

/-- Even-`x` affine Edwards lift of `ekATorsionNat`. -/
@[expose] def ekATorsionPoint : EdPoint :=
  ⟨0x37736883dd9c5dff65b589e242fe30e7471635d5e39ffc3c522222b99d05f50a,
   0x6dcfc770aba1fea4819ec776e9826f0daaa7236eafc8a2d5e928bb54fac63d13⟩

private def ekATorsionInv1my : Nat :=
  0x3d44597c55fc67aaddfc4bc02097db8025b25ef070b04ae091a76eef0424b89b

private theorem ekATorsion_lift_facts :
    ekATorsionNat < p25519 ∧
    ekATorsionInv1my < p25519 ∧
    edOnCurve ekATorsionPoint = true ∧
    ekATorsionPoint ≠ edZero ∧
    ekATorsionPoint.x % 2 = 0 ∧
    fpMul (fpSub 1 ekATorsionPoint.y) ekATorsionInv1my = 1 ∧
    fpMul (fpAdd 1 ekATorsionPoint.y) ekATorsionInv1my = ekATorsionNat := by
  decide

set_option maxRecDepth 50000 in
private theorem ekATorsion_extLoop_ne_zero :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine ekATorsionPoint) edExtZero
    Q.X % p25519 ≠ 0 ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem edSmul_edOrderL_ekATorsionPoint_ne_edZero :
    edSmul edOrderL ekATorsionPoint ≠ edZero :=
  edSmul_edOrderL_ne_edZero_of_extLoop ekATorsion_extLoop_ne_zero

theorem montLiftEd_ekATorsion_even {u : List.Vector (BitVec 8) 32} {s : BitVec 8}
    (hu : decodeU255 u.toList % p25519 = ekATorsionNat) (hs : (s &&& 1#8) = 0#8) :
    montLiftEd u s = some ekATorsionPoint := by
  rcases ekATorsion_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact (montLiftEd_eq_some_of_witness h1 h2 h3 h4 h5 h6 h7).1 u s hu hs

theorem dalekPrimsRef_montToEd_ekATorsion_isSome {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = ekATorsionNat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = false := by
  rcases ekATorsion_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hw := montLiftEd_eq_some_of_witness h1 h2 h3 h4 h5 h6 h7
  have hfalse : (edSmul edOrderL ekATorsionPoint == edZero) = false :=
    Bool.eq_false_iff.mpr (fun heq => edSmul_edOrderL_ekATorsionPoint_ne_edZero (beq_iff_eq.mp heq))
  rcases bv8_and_one_dichotomy s with hs0 | hs1
  · refine ⟨encEd160 ekATorsionPoint, ?_, ?_⟩
    · rw [dalekPrimsRef_montToEd_eq_some_iff]
      exact ⟨ekATorsionPoint, hw.1 u s hu hs0, rfl⟩
    · rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve h3, hfalse]
  · refine ⟨encEd160 (edNeg ekATorsionPoint), ?_, ?_⟩
    · rw [dalekPrimsRef_montToEd_eq_some_iff]
      exact ⟨edNeg ekATorsionPoint, hw.2 u s hu hs1, rfl⟩
    · rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve (edOnCurve_edNeg h3),
        edSmul_edOrderL_edNeg_eq_edZero_iff h3, hfalse]

/-- Closed-form torsion rejection for any 32-byte key whose `decodeU255 _ % p25519` equals
`ekATorsionNat` (`compEkATorsion`) under any sign byte `s`. -/
theorem dalekPrimsRef_isTorsionFree_ekATorsion_false_of_mod_p
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = ekATorsionNat)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = false := by
  rcases dalekPrimsRef_montToEd_ekATorsion_isSome s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'
  cases hmont'
  exact htf'

/-- Exact closed-form torsion rejection theorem for `CompI0Laws.compI0_torsionShiftsRejected`:
if `decodeU255 u.toList = ekATorsionNat % 2 ^ 255` and `dalekPrimsRef.montToEd u 0#8 = some pt`,
then `dalekPrimsRef.isTorsionFree pt = false`. -/
theorem dalekPrimsRef_isTorsionFree_ekATorsion_false
    {u : List.Vector (BitVec 8) 32} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList = ekATorsionNat % (2 ^ 255))
    (hmont : dalekPrimsRef.montToEd u 0#8 = some pt) :
    dalekPrimsRef.isTorsionFree pt = false := by
  have hmod : (ekATorsionNat % (2 ^ 255)) % p25519 = ekATorsionNat := by decide
  exact dalekPrimsRef_isTorsionFree_ekATorsion_false_of_mod_p
    ((congrArg (· % p25519) hu).trans hmod) hmont

/-! ## 4. Positive Lift & Torsion-Free Witnesses (`u = 9`, `ekAPub`, `toEdIn0/1/2`) -/

private theorem dalekPrimsRef_montToEd_torsionFree_of_witness
    {uNat inv1my : Nat} {P : EdPoint}
    (hu_lt : uNat < p25519)
    (hinv_lt : inv1my < p25519)
    (hP : edOnCurve P = true)
    (hne : P ≠ edZero)
    (hpar : P.x % 2 = 0)
    (hinv : fpMul (fpSub 1 P.y) inv1my = 1)
    (hu_eq : fpMul (fpAdd 1 P.y) inv1my = uNat)
    (hLP : edSmul edOrderL P = edZero)
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = uNat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  have hw := montLiftEd_eq_some_of_witness hu_lt hinv_lt hP hne hpar hinv hu_eq
  have htrue : (edSmul edOrderL P == edZero) = true := beq_iff_eq.mpr hLP
  rcases bv8_and_one_dichotomy s with hs0 | hs1
  · refine ⟨encEd160 P, ?_, ?_⟩
    · rw [dalekPrimsRef_montToEd_eq_some_iff]
      exact ⟨P, hw.1 u s hu hs0, rfl⟩
    · rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve hP, htrue]
  · refine ⟨encEd160 (edNeg P), ?_, ?_⟩
    · rw [dalekPrimsRef_montToEd_eq_some_iff]
      exact ⟨edNeg P, hw.2 u s hu hs1, rfl⟩
    · rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve (edOnCurve_edNeg hP),
        edSmul_edOrderL_edNeg_eq_edZero_iff hP, htrue]

/-- X25519 basepoint `u = 9` (`compDefaultPub` / `exampleBasepoint`): `dalekPrimsRef.montToEd`
succeeds for every sign byte `s` and `dalekPrimsRef.isTorsionFree` returns `true`. -/
theorem dalekPrimsRef_montToEd_u9_torsionFree
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = 9) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  have hfacts :
      9 < p25519 ∧
      5 < p25519 ∧
      edBasepoint.x % 2 = 0 ∧
      fpMul (fpSub 1 edBasepoint.y) 5 = 1 ∧
      fpMul (fpAdd 1 edBasepoint.y) 5 = 9 := by
    decide
  rcases hfacts with ⟨h1, h2, h5, h6, h7⟩
  exact dalekPrimsRef_montToEd_torsionFree_of_witness h1 h2 edOnCurve_edBasepoint
    edBasepoint_ne_edZero h5 h6 h7 edSmul_edOrderL_edBasepoint s hu

theorem montLiftEd_u9_even {u : List.Vector (BitVec 8) 32} {s : BitVec 8}
    (hu : decodeU255 u.toList % p25519 = 9) (hs : (s &&& 1#8) = 0#8) :
    montLiftEd u s = some edBasepoint := by
  have hfacts :
      9 < p25519 ∧ 5 < p25519 ∧ edBasepoint.x % 2 = 0 ∧
      fpMul (fpSub 1 edBasepoint.y) 5 = 1 ∧ fpMul (fpAdd 1 edBasepoint.y) 5 = 9 := by
    decide
  rcases hfacts with ⟨h1, h2, h5, h6, h7⟩
  exact (montLiftEd_eq_some_of_witness h1 h2 edOnCurve_edBasepoint
    edBasepoint_ne_edZero h5 h6 h7).1 u s hu hs

theorem dalekPrimsRef_isTorsionFree_u9_true
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = 9)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = true := by
  rcases dalekPrimsRef_montToEd_u9_torsionFree s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'; cases hmont'; exact htf'

/-- Even-`x` affine Edwards lift of `ekAPubNat` (`compEkAPub`). -/
@[expose] def ekAPubPoint : EdPoint :=
  ⟨0x7a1fce69dc8e986115af7d4f254b79cd826e9df3582f7e792825ee7cae118f5c,
   0x3ac633ae0ea8b35dd8b6a57d617b571b3917d6e8ee898fadf56c29e5eb756fae⟩

private def ekAPubInv1my : Nat :=
  0x26e1a488072daf243dc9429699bdd6e5d0d889c982dc1909fbc3479627c85dd6

private theorem ekAPub_lift_facts :
    ekAPubNat < p25519 ∧ ekAPubInv1my < p25519 ∧ edOnCurve ekAPubPoint = true ∧
    ekAPubPoint ≠ edZero ∧ ekAPubPoint.x % 2 = 0 ∧
    fpMul (fpSub 1 ekAPubPoint.y) ekAPubInv1my = 1 ∧
    fpMul (fpAdd 1 ekAPubPoint.y) ekAPubInv1my = ekAPubNat := by
  decide

set_option maxRecDepth 50000 in
private theorem ekAPub_extLoop_zero :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine ekAPubPoint) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem dalekPrimsRef_montToEd_ekAPub_torsionFree
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = ekAPubNat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  rcases ekAPub_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact dalekPrimsRef_montToEd_torsionFree_of_witness h1 h2 h3 h4 h5 h6 h7
    (edSmul_edOrderL_eq_edZero_of_extLoop ekAPub_extLoop_zero) s hu

theorem dalekPrimsRef_isTorsionFree_ekAPub_true
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = ekAPubNat)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = true := by
  rcases dalekPrimsRef_montToEd_ekAPub_torsionFree s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'; cases hmont'; exact htf'

/-- Even-`x` affine Edwards lift of `toEdIn0Nat` (`compToEdIn0`). -/
@[expose] def toEdIn0Point : EdPoint :=
  ⟨0x392e984646ec3abb5117bb413aa314649bd3aacc04696a7e17d7196f4b6dc9ba,
   0x7ef254c93b0794516bca5e01ba07c4824696e78424aadcb0b2938fb47820a1bb⟩

private def toEdIn0Inv1my : Nat :=
  0x313fd645ff81a45860195a8af2c2f441551412262c6756fdb796443b79a836fc

private theorem toEdIn0_lift_facts :
    toEdIn0Nat < p25519 ∧ toEdIn0Inv1my < p25519 ∧ edOnCurve toEdIn0Point = true ∧
    toEdIn0Point ≠ edZero ∧ toEdIn0Point.x % 2 = 0 ∧
    fpMul (fpSub 1 toEdIn0Point.y) toEdIn0Inv1my = 1 ∧
    fpMul (fpAdd 1 toEdIn0Point.y) toEdIn0Inv1my = toEdIn0Nat := by
  decide

set_option maxRecDepth 50000 in
private theorem toEdIn0_extLoop_zero :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine toEdIn0Point) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem dalekPrimsRef_montToEd_toEdIn0_torsionFree
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = toEdIn0Nat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  rcases toEdIn0_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact dalekPrimsRef_montToEd_torsionFree_of_witness h1 h2 h3 h4 h5 h6 h7
    (edSmul_edOrderL_eq_edZero_of_extLoop toEdIn0_extLoop_zero) s hu

theorem dalekPrimsRef_isTorsionFree_toEdIn0_true
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = toEdIn0Nat)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = true := by
  rcases dalekPrimsRef_montToEd_toEdIn0_torsionFree s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'; cases hmont'; exact htf'

/-- Even-`x` affine Edwards lift of `toEdIn1Nat` (`compToEdIn1`). -/
@[expose] def toEdIn1Point : EdPoint :=
  ⟨0x6bcf8f1ad64e3d97bc68fd5ae521c233e4371d2d36b546cc0aae7d22beee5436,
   0x47a30b25a4682215b6f3cabe0808d8e57cde3d4f879b1bb95eff8dbefecf5ddf⟩

private def toEdIn1Inv1my : Nat :=
  0x1c3b687912d516c2b4124c730f17f4bde0c4f240ae4b57710f410c67ccbd83c8

private theorem toEdIn1_lift_facts :
    toEdIn1Nat < p25519 ∧ toEdIn1Inv1my < p25519 ∧ edOnCurve toEdIn1Point = true ∧
    toEdIn1Point ≠ edZero ∧ toEdIn1Point.x % 2 = 0 ∧
    fpMul (fpSub 1 toEdIn1Point.y) toEdIn1Inv1my = 1 ∧
    fpMul (fpAdd 1 toEdIn1Point.y) toEdIn1Inv1my = toEdIn1Nat := by
  decide

set_option maxRecDepth 50000 in
private theorem toEdIn1_extLoop_zero :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine toEdIn1Point) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem dalekPrimsRef_montToEd_toEdIn1_torsionFree
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = toEdIn1Nat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  rcases toEdIn1_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact dalekPrimsRef_montToEd_torsionFree_of_witness h1 h2 h3 h4 h5 h6 h7
    (edSmul_edOrderL_eq_edZero_of_extLoop toEdIn1_extLoop_zero) s hu

theorem dalekPrimsRef_isTorsionFree_toEdIn1_true
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = toEdIn1Nat)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = true := by
  rcases dalekPrimsRef_montToEd_toEdIn1_torsionFree s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'; cases hmont'; exact htf'

/-- Even-`x` affine Edwards lift of `toEdIn2Nat` (`compToEdIn2`). -/
@[expose] def toEdIn2Point : EdPoint :=
  ⟨0x5be2c37e8251d9af9922c31d71d750c9e3dede90c66a22e3b0bc96286d2cfd72,
   0x33e156af78bbc13b73278b19081993c383d3c220f493326c947d0ce0879dea27⟩

private def toEdIn2Inv1my : Nat :=
  0x0c8c99fa9a9766764b0c16f712e5b7e24f92094040d25810afe63136fdafd44c

private theorem toEdIn2_lift_facts :
    toEdIn2Nat < p25519 ∧ toEdIn2Inv1my < p25519 ∧ edOnCurve toEdIn2Point = true ∧
    toEdIn2Point ≠ edZero ∧ toEdIn2Point.x % 2 = 0 ∧
    fpMul (fpSub 1 toEdIn2Point.y) toEdIn2Inv1my = 1 ∧
    fpMul (fpAdd 1 toEdIn2Point.y) toEdIn2Inv1my = toEdIn2Nat := by
  decide

set_option maxRecDepth 50000 in
private theorem toEdIn2_extLoop_zero :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine toEdIn2Point) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem dalekPrimsRef_montToEd_toEdIn2_torsionFree
    {u : List.Vector (BitVec 8) 32} (s : BitVec 8)
    (hu : decodeU255 u.toList % p25519 = toEdIn2Nat) :
    ∃ pt, dalekPrimsRef.montToEd u s = some pt ∧ dalekPrimsRef.isTorsionFree pt = true := by
  rcases toEdIn2_lift_facts with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact dalekPrimsRef_montToEd_torsionFree_of_witness h1 h2 h3 h4 h5 h6 h7
    (edSmul_edOrderL_eq_edZero_of_extLoop toEdIn2_extLoop_zero) s hu

theorem dalekPrimsRef_isTorsionFree_toEdIn2_true
    {u : List.Vector (BitVec 8) 32} {s : BitVec 8} {pt : List.Vector (BitVec 8) 160}
    (hu : decodeU255 u.toList % p25519 = toEdIn2Nat)
    (hmont : dalekPrimsRef.montToEd u s = some pt) :
    dalekPrimsRef.isTorsionFree pt = true := by
  rcases dalekPrimsRef_montToEd_toEdIn2_torsionFree s hu with ⟨pt', hmont', htf'⟩
  rw [hmont] at hmont'; cases hmont'; exact htf'

/-! ## 5. Direct `SignalPqxdh.montLiftEd` Bridges for `X25519TorsionFree` -/

theorem signalMontLiftEd_torsionFree_iff_dalekPrimsRef
    {b : List (BitVec 8)} (hb : b.length = 32) :
    (∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧ (edSmul edOrderL P == edZero) = true) ↔
    (∃ pt, dalekPrimsRef.montToEd ⟨b, hb⟩ 0#8 = some pt ∧ dalekPrimsRef.isTorsionFree pt = true) := by
  have hsig : SignalPqxdh.montLiftEd b 0#8 = montLiftEd ⟨b, hb⟩ 0#8 := signalMontLiftEd_eq ⟨b, hb⟩ 0#8
  rw [hsig]
  constructor
  · rintro ⟨P, hlift, htf⟩
    have hP : edOnCurve P = true := montLiftEd_some_onCurve hlift
    refine ⟨encEd160 P, dalekPrimsRef_montToEd_eq_some_iff.mpr ⟨P, hlift, rfl⟩, ?_⟩
    rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve hP, htf]
  · rintro ⟨pt, hmont, htf⟩
    rcases dalekPrimsRef_montToEd_eq_some_iff.mp hmont with ⟨P, hlift, rfl⟩
    have hP : edOnCurve P = true := montLiftEd_some_onCurve hlift
    rw [dalekPrimsRef_isTorsionFree_encEd160_of_onCurve hP] at htf
    exact ⟨P, hlift, htf⟩

theorem signalMontLiftEd_torsionShift_rejected_of_onCurve {P_pk T : EdPoint}
    (hP : edOnCurve P_pk = true) (hneP : P_pk ≠ edZero)
    (hLP : edSmul edOrderL P_pk = edZero)
    (hT : edOnCurve T = true) (h8T : edSmul 8 T = edZero)
    (hu_ne : edToMontU (edAdd P_pk T) ≠ edToMontU P_pk)
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = edToMontU (edAdd P_pk T)) :
    ¬ ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
        (edSmul edOrderL P == edZero) = true := by
  rw [signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb]
  rintro ⟨pt, hmont, htf⟩
  have hf := dalekPrimsRef_torsionShift_rejected_of_onCurve hP hneP hLP hT h8T hu_ne
    (u := ⟨b, hb⟩) hu hmont
  rw [hf] at htf
  cases htf

theorem signalMontLiftEd_ekATorsion_not_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b = ekATorsionNat % (2 ^ 255)) :
    ¬ ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
        (edSmul edOrderL P == edZero) = true := by
  rw [signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb]
  rintro ⟨pt, hmont, htf⟩
  have hf := dalekPrimsRef_isTorsionFree_ekATorsion_false (u := ⟨b, hb⟩) hu hmont
  rw [hf] at htf
  cases htf

theorem signalMontLiftEd_u9_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = 9) :
    ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
      (edSmul edOrderL P == edZero) = true :=
  (signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb).mpr
    (dalekPrimsRef_montToEd_u9_torsionFree 0#8 hu)

theorem signalMontLiftEd_ekAPub_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = ekAPubNat) :
    ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
      (edSmul edOrderL P == edZero) = true :=
  (signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb).mpr
    (dalekPrimsRef_montToEd_ekAPub_torsionFree 0#8 hu)

theorem signalMontLiftEd_toEdIn0_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = toEdIn0Nat) :
    ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
      (edSmul edOrderL P == edZero) = true :=
  (signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb).mpr
    (dalekPrimsRef_montToEd_toEdIn0_torsionFree 0#8 hu)

theorem signalMontLiftEd_toEdIn1_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = toEdIn1Nat) :
    ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
      (edSmul edOrderL P == edZero) = true :=
  (signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb).mpr
    (dalekPrimsRef_montToEd_toEdIn1_torsionFree 0#8 hu)

theorem signalMontLiftEd_toEdIn2_torsionFree
    {b : List (BitVec 8)} (hb : b.length = 32)
    (hu : decodeU255 b % p25519 = toEdIn2Nat) :
    ∃ P : EdPoint, SignalPqxdh.montLiftEd b 0#8 = some P ∧
      (edSmul edOrderL P == edZero) = true :=
  (signalMontLiftEd_torsionFree_iff_dalekPrimsRef hb).mpr
    (dalekPrimsRef_montToEd_toEdIn2_torsionFree 0#8 hu)

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
