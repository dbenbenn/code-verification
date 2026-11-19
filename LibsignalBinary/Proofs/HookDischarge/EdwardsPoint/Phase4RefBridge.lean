/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge

/-!
# `dalekPrimsRef` Soundness and Congruence Bridges

Defines the closed Curve25519 reference `dalekPrimsRef : DalekPrims` and the
representation-invariance relation `DalekPrimsSound`, proves `dalekPrimsRef_sound`,
proves congruence of `SignalPqxdh.isCanonicalRef`, `SignalPqxdh.xeddsaVerifyRef`, and
`SignalPqxdh.Model.{initiateKeys, acceptKeys, initiate, accept}` across any two
`DalekPrimsSound` implementations, and bridges `dalekCliMultiLib` machine-code postconditions
(`B01`, `B02`, `B08`, `B14`, `B17`, `B19`, and `EdwardsNeg`) to `SignalPqxdh.isCanonicalRef`
and `SignalPqxdh.xeddsaVerifyRef` at `dalekPrimsRef`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge

open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (
  Sha512State PqxdhPrims PEParams UnreachedPqxdhPrimitives
  ofU8 toU8 fitVec u8Vec vecU8 blockLevelPrims modelPrims
)
open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven
  leBytesToNat natToLeBytes EdPoint edZero edBasepoint
  edOnCurve edAdd edSub edNeg edSmul edExtToAffine edExtOfAffine encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards fe51Point4Bounded edExtOfBytes edDoubleScalarMulBasepoint
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_natToLeBytes_of_lt
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edNeg edAdd_x_lt edAdd_y_lt
  edAdd_comm edNeg_edZero edNeg_edAdd edNatSmul edSmul_eq_edNatSmul
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (
  montToEdwards_eq_some_iff montToEdwards_eq_none_iff_raw montToEdwards_some_onCurve
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (
  dalekEdNegBytes pipeline2_xeddsa_verify_compress_eq
)

attribute [local irreducible] fpInv recoverXEven edSmul edDoubleScalarMulBasepoint

/-! ## 1. Closed Curve25519 Reference (`dalekPrimsRef`) -/

/-- The 7 directly verified `curve25519-dalek` operations used in PQXDH (`is_canonical` and
XEdDSA `verify_signature_for_multipart_message`), separated from `PqxdhPrims`. -/
structure DalekPrims where
  /-- `MontgomeryPoint::to_edwards`: u-coordinate and sign bit (`0` or `1`) to a 160-byte point. -/
  montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160)
  /-- `EdwardsPoint::compress`. -/
  compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32
  /-- `<EdwardsPoint as Neg>::neg`. -/
  edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160
  /-- `EdwardsPoint::is_torsion_free`. -/
  isTorsionFree : List.Vector (BitVec 8) 160 → Bool
  /-- `vartime_double_scalar_mul_basepoint a A b = [a]A + [b]B`. -/
  dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 160
  /-- `Scalar::from_bytes_mod_order` (32 bytes, reduced mod `ℓ`). -/
  scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32
  /-- `Scalar::from_bytes_mod_order_wide` (64 bytes, reduced mod `ℓ`). -/
  scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32

/-- Compatibility alias for `PqxdhPrims`, which contains the 4 externally hooked
PQXDH/SPQR primitives (`F512`, `encaps`, `decaps`, `K`). -/
abbrev PqxdhHookPrims := PqxdhPrims

/-- Identity projection (`PqxdhPrims` does not carry the 7 Curve25519 operations). -/
@[expose] def pqxdhPrimsOfHooks (Qh : PqxdhHookPrims) (_Qd : DalekPrims) : PqxdhPrims := Qh

/-- Birational lift from a 32-byte little-endian Montgomery `u`-coordinate (RFC 7748 §5 bit-255
masked, reduced mod `p = 2^255 - 19`) and low sign bit `sign &&& 1` to the affine twisted Edwards
curve (`y = (u - 1) / (u + 1) mod p`, rejecting `u = p - 1` where `u + 1 ≡ 0` and `u` on the
quadratic twist (`u³+486662u²+u` non-square, detected by `recoverXEven`)). Reducing `u ≥ p` mod `p`
deliberately follows `libsignal` / `curve25519-dalek` (`MontgomeryPoint::to_edwards`), not Perrin's
XEdDSA §2.5 (which rejects `u ≥ p` in verify; e.g., `pk = edff…ff7f` reduces to `u = 0` and lifts to
`(0, p - 1)`). -/
@[expose] def montLiftEd (uBytes : List.Vector (BitVec 8) 32) (sign : BitVec 8) :
    Option EdPoint :=
  let u := (leBytesToNat uBytes.toList % (2 ^ 255)) % p25519
  if u == p25519 - 1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    (recoverXEven y).map fun xEven =>
      ⟨if (sign &&& 1#8) == 1#8 then fpNeg xEven else xEven, y⟩

theorem natToLeBytes_len (len n : Nat) : (natToLeBytes len n).length = len := by
  unfold natToLeBytes
  rw [List.length_map, List.length_range]

/-- Reference 160-byte packing of an affine `EdPoint` `(x mod p, y mod p)` as `x_le32 ‖ y_le32 ‖ 0^96`
(no limb representation). -/
@[expose] def encEd160 (P : EdPoint) : List.Vector (BitVec 8) 160 :=
  ⟨natToLeBytes 32 (P.x % p25519) ++ natToLeBytes 32 (P.y % p25519) ++ List.replicate 96 0#8,
   by simp only [List.length_append, List.length_replicate, natToLeBytes_len]⟩

/-- Inverse projection reading `(x mod p, y mod p)` from the first 64 bytes of `v`. -/
@[expose] def decEd160 (v : List.Vector (BitVec 8) 160) : EdPoint :=
  ⟨leBytesToNat (v.toList.take 32) % p25519,
   leBytesToNat ((v.toList.drop 32).take 32) % p25519⟩

/-- Closed computable mathematical reference for the 7 linked `curve25519-dalek` operations
over `VerifiedLibraries.Common.Spec.Curve25519`. -/
@[expose] def dalekPrimsRef : DalekPrims where
  montToEd u s := (montLiftEd u s).map encEd160
  compress v := ⟨encodeEd (decEd160 v), by unfold encodeEd; exact natToLeBytes_len 32 _⟩
  edNeg v := encEd160 (edNeg (decEd160 v))
  isTorsionFree v := edSmul edOrderL (decEd160 v) == edZero
  dsmb a v b :=
    encEd160 (edAdd (edSmul (leBytesToNat a.toList) (decEd160 v))
      (edSmul (leBytesToNat b.toList) edBasepoint))
  scalarMod a := ⟨natToLeBytes 32 (leBytesToNat a.toList % edOrderL), natToLeBytes_len 32 _⟩
  scalarWide a := ⟨natToLeBytes 32 (leBytesToNat a.toList % edOrderL), natToLeBytes_len 32 _⟩

/-! ## 2. Byte / Vector Round-Trip & Codec Lemmas -/

@[simp]
theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  unfold ofU8 toU8
  rw [List.map_map]
  change bs.map (fun b => (UInt8.ofBitVec b).toBitVec) = bs
  simp

@[simp]
theorem toU8_ofU8 (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  unfold ofU8 toU8
  rw [List.map_map]
  change bs.map (fun b => UInt8.ofBitVec b.toBitVec) = bs
  simp

@[simp]
theorem ofU8_length (bs : List UInt8) : (ofU8 bs).length = bs.length := by
  simp [ofU8]

@[simp]
theorem toU8_length (bs : List (BitVec 8)) : (toU8 bs).length = bs.length := by
  simp [toU8]

@[simp]
theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) : (vecU8 v).length = n := by
  unfold vecU8
  rw [toU8_length]
  exact v.2

theorem u8Vec_toList_of_length {n : Nat} {bs : List UInt8} (h : bs.length = n) :
    (u8Vec n bs).toList = ofU8 bs := by
  unfold u8Vec fitVec
  change ((ofU8 bs ++ List.replicate n 0#8).take n) = ofU8 bs
  have hlen : (ofU8 bs).length = n := by rw [ofU8_length, h]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

@[simp]
theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : u8Vec n (vecU8 v) = v := by
  apply Subtype.ext
  change (u8Vec n (vecU8 v)).toList = v.toList
  rw [u8Vec_toList_of_length (vecU8_length v)]
  unfold vecU8
  exact ofU8_toU8 v.toList

theorem sign_and_one_eq_iff (sign : BitVec 8) :
    ((sign &&& 1#8) == 1#8) = (sign.toNat % 2 == 1) := by
  have hand : (sign &&& 1#8).toNat = sign.toNat % 2 := by
    rw [BitVec.toNat_and]
    change sign.toNat &&& (2 ^ 1 - 1) = sign.toNat % 2 ^ 1
    exact Nat.and_two_pow_sub_one_eq_mod sign.toNat 1
  have hinj : (sign &&& 1#8 = 1#8) ↔ (sign.toNat % 2 = 1) := by
    rw [← BitVec.toNat_inj, hand]
    rfl
  exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using hinj)

private def montLiftEdWith (recFn : Nat → Option Nat)
    (u p1 : Nat) (signOdd : Bool) : Option EdPoint :=
  if u == p1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    (recFn y).map fun xEven =>
      ⟨if signOdd then fpNeg xEven else xEven, y⟩

private theorem montLiftEd_eq_liftWith (uBytes : List.Vector (BitVec 8) 32) (sign : BitVec 8) :
    montLiftEd uBytes sign =
      montLiftEdWith recoverXEven
        ((leBytesToNat uBytes.toList % (2 ^ 255)) % p25519) (p25519 - 1)
        ((sign &&& 1#8) == 1#8) := rfl

private theorem montLiftEdWith_of_eq (recFn : Nat → Option Nat) (u : Nat) (signOdd : Bool) :
    montLiftEdWith recFn u u signOdd = none := by
  unfold montLiftEdWith
  simp

private theorem montLiftEdWith_of_ne_none (recFn : Nat → Option Nat) {u p1 : Nat} (signOdd : Bool)
    (hne : u ≠ p1) (hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = none) :
    montLiftEdWith recFn u p1 signOdd = none := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1)))).map _ = none
  rw [hrec]
  rfl

private theorem montLiftEdWith_of_ne_some (recFn : Nat → Option Nat) {u p1 xEven : Nat}
    (signOdd : Bool) (hne : u ≠ p1)
    (hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = some xEven) :
    montLiftEdWith recFn u p1 signOdd =
      some ⟨if signOdd then fpNeg xEven else xEven, fpMul (fpSub u 1) (fpInv (fpAdd u 1))⟩ := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1)))).map _ = _
  rw [hrec]
  rfl

theorem montLiftEd_eq_montToEdwards (u : List.Vector (BitVec 8) 32) (sign : BitVec 8) :
    montLiftEd u sign = montToEdwards u.toList sign.toNat := by
  have hu : leBytesToNat u.toList % (2 ^ 255) = decodeU255 u.toList := by
    unfold decodeU255
    have hlen : u.toList.length = 32 := u.2
    rw [List.take_of_length_le (by omega)]
  rw [montLiftEd_eq_liftWith, hu]
  cases hm : montToEdwards u.toList sign.toNat with
  | none =>
    rcases (montToEdwards_eq_none_iff_raw u.toList sign.toNat).mp hm with hup | ⟨hne, hrec⟩
    · rw [hup]
      exact montLiftEdWith_of_eq _ _ _
    · exact montLiftEdWith_of_ne_none _ _ hne hrec
  | some P =>
    rcases (montToEdwards_eq_some_iff u.toList sign.toNat P).mp hm with ⟨hne, xEven, hrec, rfl⟩
    rw [montLiftEdWith_of_ne_some _ _ hne hrec, sign_and_one_eq_iff]

attribute [local irreducible] montLiftEd montToEdwards

theorem montLiftEd_some_onCurve {u : List.Vector (BitVec 8) 32} {sign : BitVec 8} {P : EdPoint}
    (h : montLiftEd u sign = some P) : edOnCurve P = true := by
  rw [montLiftEd_eq_montToEdwards] at h
  exact montToEdwards_some_onCurve h

theorem decEd160_encEd160 (P : EdPoint) :
    decEd160 (encEd160 P) = ⟨P.x % p25519, P.y % p25519⟩ := by
  unfold decEd160 encEd160
  dsimp only [List.Vector.toList]
  let bx := natToLeBytes 32 (P.x % p25519)
  let by_ := natToLeBytes 32 (P.y % p25519)
  let bz := List.replicate 96 0#8
  have hbx : bx.length = 32 := natToLeBytes_len 32 _
  have hby : by_.length = 32 := natToLeBytes_len 32 _
  have hassoc : bx ++ by_ ++ bz = bx ++ (by_ ++ bz) := List.append_assoc bx by_ bz
  change EdPoint.mk (leBytesToNat ((bx ++ by_ ++ bz).take 32) % p25519)
      (leBytesToNat (((bx ++ by_ ++ bz).drop 32).take 32) % p25519) =
    ⟨P.x % p25519, P.y % p25519⟩
  rw [hassoc,
    List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show 32 - bx.length = 0 by omega, List.drop_zero,
    List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hp_lt : p25519 < 256 ^ 32 := by unfold p25519; decide
  have hx_lt : P.x % p25519 < 256 ^ 32 := Nat.lt_trans (Nat.mod_lt _ (by unfold p25519; decide)) hp_lt
  have hy_lt : P.y % p25519 < 256 ^ 32 := Nat.lt_trans (Nat.mod_lt _ (by unfold p25519; decide)) hp_lt
  dsimp only [bx, by_]
  rw [leBytesToNat_natToLeBytes_of_lt hx_lt, leBytesToNat_natToLeBytes_of_lt hy_lt,
    Nat.mod_mod, Nat.mod_mod]

theorem decEd160_encEd160_of_lt {P : EdPoint} (hx : P.x < p25519) (hy : P.y < p25519) :
    decEd160 (encEd160 P) = P := by
  rw [decEd160_encEd160, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem decEd160_encEd160_of_onCurve {P : EdPoint} (hP : edOnCurve P = true) :
    decEd160 (encEd160 P) = P :=
  decEd160_encEd160_of_lt (edOnCurve_x_lt hP) (edOnCurve_y_lt hP)

private theorem edNatSmul_edNeg (n : Nat) (P : EdPoint) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero =>
    unfold edNatSmul
    exact edNeg_edZero.symm
  | succ k ih =>
    unfold edNatSmul
    rw [ih, edNeg_edAdd]

theorem edSmul_edNeg {n : Nat} {P : EdPoint} (hn : n < 2 ^ 256) (hP : edOnCurve P = true) :
    edSmul n (edNeg P) = edNeg (edSmul n P) := by
  rw [edSmul_eq_edNatSmul hn (edOnCurve_edNeg hP), edSmul_eq_edNatSmul hn hP, edNatSmul_edNeg]

theorem edAdd_edSmul_edNeg_eq_edSub {h s : Nat} {Apt : EdPoint}
    (hh : h < 2 ^ 256) (hApt : edOnCurve Apt = true) :
    edAdd (edSmul h (edNeg Apt)) (edSmul s edBasepoint) =
      edSub (edSmul s edBasepoint) (edSmul h Apt) := by
  rw [edAdd_comm, edSmul_edNeg hh hApt]
  rfl

/-! ## 3. `DalekPrimsSound` Relation and `dalekPrimsRef_sound` -/

/-- Curve25519 representation-soundness relation:
`Qd : DalekPrims` implements the twisted Edwards Curve25519 operations modulo some internal
160-byte point representation `Rep`. -/
@[expose] def DalekPrimsSound (Qd : DalekPrims) : Prop :=
  ∃ Rep : List.Vector (BitVec 8) 160 → EdPoint → Prop,
    (∀ u sign, montLiftEd u sign = none → Qd.montToEd u sign = none) ∧
    (∀ u sign P, montLiftEd u sign = some P → ∃ pt, Qd.montToEd u sign = some pt ∧ Rep pt P) ∧
    (∀ pt P, Rep pt P → (Qd.compress pt).toList = encodeEd P) ∧
    (∀ pt P, Rep pt P → Rep (Qd.edNeg pt) (edNeg P)) ∧
    (∀ pt P, Rep pt P → Qd.isTorsionFree pt = (edSmul edOrderL P == edZero)) ∧
    (∀ a pt P b, Rep pt P → leBytesToNat a.toList < edOrderL → leBytesToNat b.toList < edOrderL →
      Rep (Qd.dsmb a pt b)
        (edAdd (edSmul (leBytesToNat a.toList) P) (edSmul (leBytesToNat b.toList) edBasepoint))) ∧
    (∀ a, (Qd.scalarMod a).toList = natToLeBytes 32 (leBytesToNat a.toList % edOrderL)) ∧
    (∀ a, (Qd.scalarWide a).toList = natToLeBytes 32 (leBytesToNat a.toList % edOrderL))

private theorem dalekPrimsRef_montToEd (u : List.Vector (BitVec 8) 32) (s : BitVec 8) :
    dalekPrimsRef.montToEd u s = (montLiftEd u s).map encEd160 := rfl
private theorem dalekPrimsRef_compress_toList (v : List.Vector (BitVec 8) 160) :
    (dalekPrimsRef.compress v).toList = encodeEd (decEd160 v) := rfl
private theorem dalekPrimsRef_edNeg (v : List.Vector (BitVec 8) 160) :
    dalekPrimsRef.edNeg v = encEd160 (edNeg (decEd160 v)) := rfl
private theorem dalekPrims_mk_isTorsionFree (f1 f2 f3 f4 f5 f6 f7)
    (v : List.Vector (BitVec 8) 160) :
    (DalekPrims.mk f1 f2 f3 f4 f5 f6 f7).isTorsionFree v = f4 v := rfl
private theorem dalekPrimsRef_isTorsionFree (v : List.Vector (BitVec 8) 160) :
    dalekPrimsRef.isTorsionFree v = (edSmul edOrderL (decEd160 v) == edZero) :=
  (congrArg (fun d => d.isTorsionFree v) dalekPrimsRef.eq_1).trans
    (dalekPrims_mk_isTorsionFree _ _ _ _ _ _ _ v)
private theorem dalekPrimsRef_dsmb (a : List.Vector (BitVec 8) 32)
    (v : List.Vector (BitVec 8) 160) (b : List.Vector (BitVec 8) 32) :
    dalekPrimsRef.dsmb a v b =
      encEd160 (edAdd (edSmul (leBytesToNat a.toList) (decEd160 v))
        (edSmul (leBytesToNat b.toList) edBasepoint)) := rfl
private theorem dalekPrimsRef_scalarMod_toList (a : List.Vector (BitVec 8) 32) :
    (dalekPrimsRef.scalarMod a).toList = natToLeBytes 32 (leBytesToNat a.toList % edOrderL) := rfl
private theorem dalekPrimsRef_scalarWide_toList (a : List.Vector (BitVec 8) 64) :
    (dalekPrimsRef.scalarWide a).toList = natToLeBytes 32 (leBytesToNat a.toList % edOrderL) := rfl

attribute [local irreducible] dalekPrimsRef

/-- The closed affine Curve25519 reference `dalekPrimsRef` satisfies `DalekPrimsSound`. -/
theorem dalekPrimsRef_sound : DalekPrimsSound dalekPrimsRef := by
  refine ⟨fun v P => P.x < p25519 ∧ P.y < p25519 ∧ decEd160 v = P,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u sign hnone
    rw [dalekPrimsRef_montToEd, hnone]
    rfl
  · intro u sign P hsome
    have hon : edOnCurve P = true := montLiftEd_some_onCurve hsome
    refine ⟨encEd160 P, by rw [dalekPrimsRef_montToEd, hsome]; rfl,
      edOnCurve_x_lt hon, edOnCurve_y_lt hon, decEd160_encEd160_of_onCurve hon⟩
  · rintro pt P ⟨_hx, _hy, hdec⟩
    rw [dalekPrimsRef_compress_toList, hdec]
  · rintro pt P ⟨_hx, _hy, hdec⟩
    rw [dalekPrimsRef_edNeg, hdec]
    have hnx : (edNeg P).x < p25519 := by
      unfold edNeg fpNeg; exact Nat.mod_lt _ (by unfold p25519; decide)
    have hny : (edNeg P).y < p25519 := by
      unfold edNeg; exact Nat.mod_lt _ (by unfold p25519; decide)
    exact ⟨hnx, hny, decEd160_encEd160_of_lt hnx hny⟩
  · rintro pt P ⟨_hx, _hy, hdec⟩
    rw [dalekPrimsRef_isTorsionFree, hdec]
  · rintro a pt P b ⟨_hx, _hy, hdec⟩ _ha _hb
    rw [dalekPrimsRef_dsmb, hdec]
    exact ⟨edAdd_x_lt _ _, edAdd_y_lt _ _, decEd160_encEd160_of_lt (edAdd_x_lt _ _) (edAdd_y_lt _ _)⟩
  · exact dalekPrimsRef_scalarMod_toList
  · exact dalekPrimsRef_scalarWide_toList

/-- Concrete `5×51`-limb `curve25519-dalek` representation relation satisfied by `dalekCliMultiLib`
(`B08`, `B14`, `EdwardsNeg`, `B17`, `B19`). -/
@[expose] def dalekLimbRep (pt : List.Vector (BitVec 8) 160) (P : EdPoint) : Prop :=
  edOnCurve P = true ∧
  fe51Point4Bounded pt.toList (2 ^ 52) ∧
  edExtOfBytes pt.toList = edExtOfAffine P

/-! ## 4. Closed Reduction & Congruence of `isCanonicalRef` and `xeddsaVerifyRef` -/

theorem signalMontLiftEd_eq (u : List.Vector (BitVec 8) 32) (s : BitVec 8) :
    SignalPqxdh.montLiftEd u.toList s = montLiftEd u s := by
  have htake : u.toList.take 32 = u.toList := List.take_of_length_le (by simp)
  simp only [SignalPqxdh.montLiftEd, montLiftEd, htake]

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

private theorem match_edPoint_fun_congr (m : Option EdPoint) {f1 f2 : EdPoint → Bool}
    (hf : ∀ P, f1 P = f2 P) :
    (match m with | some P => f1 P | none => false) =
      (match m with | some P => f2 P | none => false) := by
  cases m with
  | none => rfl
  | some P => exact hf P

/-- Closed Curve25519 evaluation of `SignalPqxdh.isCanonicalRef` at `blockLevelPrims X W`. -/
theorem isCanonicalRef_blockLevelPrims_eq
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef (blockLevelPrims X W) pk =
      if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk then
        match montLiftEd (u8Vec 32 pk) 0#8 with
        | some P => edSmul edOrderL P == edZero
        | none => false
      else false := by
  rw [SignalPqxdh.isCanonicalRef.eq_def]
  split
  · have hm : (blockLevelPrims X W).montToEd pk 0 = montLiftEd (u8Vec 32 pk) 0#8 := by
      change SignalPqxdh.montLiftEd (u8Vec 32 pk).toList (0 : UInt8).toBitVec = _
      rw [show (0 : UInt8).toBitVec = 0#8 from rfl, signalMontLiftEd_eq]
    rw [hm]
    exact match_edPoint_fun_congr _ (blockLevelPrims_isTorsionFree X W)
  · rfl

/-- Closed Curve25519 evaluation of `SignalPqxdh.isCanonicalRef` for any `DalekPrimsSound Qd`. -/
theorem isCanonicalRef_eq_closed_of_sound {Qd : DalekPrims} (_hQd : DalekPrimsSound Qd)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd⟩) pk =
      if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk then
        match montLiftEd (u8Vec 32 pk) 0#8 with
        | some P => edSmul edOrderL P == edZero
        | none => false
      else false :=
  isCanonicalRef_blockLevelPrims_eq X ⟨C, Qh⟩ pk

/-- Any two `DalekPrimsSound` witnesses `Qd₁, Qd₂` induce identical
`SignalPqxdh.isCanonicalRef` predicates on all inputs. -/
theorem isCanonicalRef_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (_h₁ : DalekPrimsSound Qd₁) (_h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) pk := rfl

/-- Closed Curve25519 evaluation of `SignalPqxdh.xeddsaVerifyRef` at `blockLevelPrims X W`. -/
theorem xeddsaVerifyRef_blockLevelPrims_eq
    (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (sha512 : List UInt8 → List UInt8) (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X W with sha512 }) pk m sig =
      if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
        let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
        match montLiftEd (u8Vec 32 pk) signBit.toBitVec with
        | none => false
        | some Apt =>
          let capA := toU8 (encodeEd Apt)
          let capR := sig.take 32
          let sRaw := sig.drop 32
          let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
          let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
          let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
          let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
          capRCheck == capR
      else false := by
  unfold SignalPqxdh.xeddsaVerifyRef
  split
  · let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    let P_blk := blockLevelPrims X W
    change (match SignalPqxdh.montLiftEd (u8Vec 32 pk).toList signBit.toBitVec with
      | none => false
      | some aPt =>
        let capA := P_blk.compress aPt
        let capR := sig.take 32
        let sRaw := sig.drop 32
        let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
        let h := P_blk.scalarFromWide (sha512 (capR ++ capA ++ m))
        let negA := P_blk.edNeg aPt
        let s := P_blk.scalarFromBytesModOrder sClamped
        let capRCheck := P_blk.compress (P_blk.doubleScalarMulBasepoint h negA s)
        capRCheck == capR) =
      (match montLiftEd (u8Vec 32 pk) signBit.toBitVec with
      | none => false
      | some Apt =>
        let capA := toU8 (encodeEd Apt)
        let capR := sig.take 32
        let sRaw := sig.drop 32
        let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
        let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
        let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
        let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
        capRCheck == capR)
    rw [signalMontLiftEd_eq]
    cases hlift : montLiftEd (u8Vec 32 pk) signBit.toBitVec with
    | none => rfl
    | some Apt =>
      have hApt_curve : edOnCurve Apt = true := montLiftEd_some_onCurve hlift
      let capA := toU8 (encodeEd Apt)
      let capR := sig.take 32
      let sRaw := sig.drop 32
      let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
      let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
      have hl_lt_256_32 : edOrderL < 256 ^ 32 := by unfold edOrderL; decide
      have hh_lt_l : hNat < edOrderL := Nat.mod_lt _ (by unfold edOrderL; decide)
      have hs_lt_l : sNat < edOrderL := Nat.mod_lt _ (by unfold edOrderL; decide)
      have hh_vec : (u8Vec 32 (toU8 (natToLeBytes 32 hNat))).toList = natToLeBytes 32 hNat := by
        rw [u8Vec_toList_of_length (by rw [toU8_length, natToLeBytes_len]), ofU8_toU8]
      have hs_vec : (u8Vec 32 (toU8 (natToLeBytes 32 sNat))).toList = natToLeBytes 32 sNat := by
        rw [u8Vec_toList_of_length (by rw [toU8_length, natToLeBytes_len]), ofU8_toU8]
      have hh_val :
          leBytesToNat (u8Vec 32 (P_blk.scalarFromWide (sha512 (capR ++ capA ++ m)))).toList =
            hNat := by
        change leBytesToNat (u8Vec 32 (toU8 (natToLeBytes 32 hNat))).toList = hNat
        rw [hh_vec, leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans hh_lt_l hl_lt_256_32)]
      have hs_val :
          leBytesToNat (u8Vec 32 (P_blk.scalarFromBytesModOrder sClamped)).toList = sNat := by
        change leBytesToNat (u8Vec 32 (toU8 (natToLeBytes 32 sNat))).toList = sNat
        rw [hs_vec, leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans hs_lt_l hl_lt_256_32)]
      have hcapRCheck :
          P_blk.compress (P_blk.doubleScalarMulBasepoint
            (P_blk.scalarFromWide (sha512 (capR ++ P_blk.compress Apt ++ m)))
            (P_blk.edNeg Apt)
            (P_blk.scalarFromBytesModOrder sClamped)) =
            toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt))) := by
        change toU8 (encodeEd (edAdd
          (edSmul (leBytesToNat (u8Vec 32 (P_blk.scalarFromWide (sha512 (capR ++ capA ++ m)))).toList)
            (edNeg Apt))
          (edSmul (leBytesToNat (u8Vec 32 (P_blk.scalarFromBytesModOrder sClamped)).toList)
            edBasepoint))) = _
        rw [hh_val, hs_val,
          edAdd_edSmul_edNeg_eq_edSub (Nat.lt_trans hh_lt_l (by unfold edOrderL; decide)) hApt_curve]
      exact congrArg (· == capR) hcapRCheck
  · rfl

/-- Closed Curve25519 evaluation of `SignalPqxdh.xeddsaVerifyRef` for any `DalekPrimsSound Qd`. -/
theorem xeddsaVerifyRef_eq_closed_of_sound {Qd : DalekPrims} (_hQd : DalekPrimsSound Qd)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (sha512 : List UInt8 → List UInt8) (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd⟩ with sha512 })
      pk m sig =
      if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
        let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
        match montLiftEd (u8Vec 32 pk) signBit.toBitVec with
        | none => false
        | some Apt =>
          let capA := toU8 (encodeEd Apt)
          let capR := sig.take 32
          let sRaw := sig.drop 32
          let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
          let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
          let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
          let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
          capRCheck == capR
      else false :=
  xeddsaVerifyRef_blockLevelPrims_eq X ⟨C, Qh⟩ sha512 pk m sig

/-- Any two `DalekPrimsSound` witnesses `Qd₁, Qd₂` induce identical
`SignalPqxdh.xeddsaVerifyRef` predicates on all inputs. -/
theorem xeddsaVerifyRef_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (_h₁ : DalekPrimsSound Qd₁) (_h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (sha512 : List UInt8 → List UInt8) (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩ with sha512 })
      pk m sig =
    SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩ with sha512 })
      pk m sig := rfl

/-! ## 5. Protocol-Level Congruence (`initiateKeys`, `acceptKeys`, `initiate`, `accept`) -/

private theorem sha512Step_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha512Compress = P₂.sha512Compress) :
    SignalPqxdh.sha512Step P₁ = SignalPqxdh.sha512Step P₂ := by
  funext s b; unfold SignalPqxdh.sha512Step; rw [h]

private theorem sha512Ref_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha512Compress = P₂.sha512Compress) :
    SignalPqxdh.sha512Ref P₁ = SignalPqxdh.sha512Ref P₂ := by
  funext m; unfold SignalPqxdh.sha512Ref; rw [sha512Step_congr h]

private theorem sha512Ref_ofHooks_indep (X : UnreachedPqxdhPrimitives) (C : Crypto)
    (Qh : PqxdhHookPrims) (Qd₁ Qd₂ : DalekPrims) :
    SignalPqxdh.sha512Ref (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) =
      SignalPqxdh.sha512Ref (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) :=
  sha512Ref_congr rfl

private theorem sha256Step_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.sha256Step P₁ = SignalPqxdh.sha256Step P₂ := by
  funext s b; unfold SignalPqxdh.sha256Step; rw [h]

private theorem sha256Ref_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.sha256Ref P₁ = SignalPqxdh.sha256Ref P₂ := by
  funext m; unfold SignalPqxdh.sha256Ref; rw [sha256Step_congr h]

private theorem hmacSha256Ref_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.hmacSha256Ref P₁ = SignalPqxdh.hmacSha256Ref P₂ := by
  funext k m; unfold SignalPqxdh.hmacSha256Ref; rw [sha256Ref_congr h]

private theorem hkdfExtractRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.hkdfExtractRef P₁ = SignalPqxdh.hkdfExtractRef P₂ := by
  funext s ikm; unfold SignalPqxdh.hkdfExtractRef; rw [hmacSha256Ref_congr h]

private theorem hkdfExpand96Ref_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.hkdfExpand96Ref P₁ = SignalPqxdh.hkdfExpand96Ref P₂ := by
  funext prk info; unfold SignalPqxdh.hkdfExpand96Ref; rw [hmacSha256Ref_congr h]

private theorem hkdfDerive96Ref_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.hkdfDerive96Ref P₁ = SignalPqxdh.hkdfDerive96Ref P₂ := by
  funext s; unfold SignalPqxdh.hkdfDerive96Ref; rw [hkdfExtractRef_congr h, hkdfExpand96Ref_congr h]

private theorem rootCreateChainRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.rootCreateChainRef P₁ = SignalPqxdh.rootCreateChainRef P₂ := by
  funext rk dh; unfold SignalPqxdh.rootCreateChainRef
  rw [hkdfExtractRef_congr h, hmacSha256Ref_congr h]

private theorem chainKdfSeedRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.chainKdfSeedRef P₁ = SignalPqxdh.chainKdfSeedRef P₂ := by
  funext ck; unfold SignalPqxdh.chainKdfSeedRef; rw [hmacSha256Ref_congr h]

private theorem chainKdfNextRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.chainKdfNextRef P₁ = SignalPqxdh.chainKdfNextRef P₂ := by
  funext ck; unfold SignalPqxdh.chainKdfNextRef; rw [hmacSha256Ref_congr h]

private theorem deriveMsgKeysRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (h : P₁.sha256Compress = P₂.sha256Compress) :
    SignalPqxdh.deriveMsgKeysRef P₁ = SignalPqxdh.deriveMsgKeysRef P₂ := by
  funext mk s; unfold SignalPqxdh.deriveMsgKeysRef
  rw [hkdfExtractRef_congr h, hmacSha256Ref_congr h]

private theorem aes256CbcEncRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (he : P₁.aesEncBlock = P₂.aesEncBlock) :
    SignalPqxdh.aes256CbcEncRef P₁ = SignalPqxdh.aes256CbcEncRef P₂ := by
  funext k iv pt; unfold SignalPqxdh.aes256CbcEncRef SignalPqxdh.cbcEncBlocks; rw [he]

private theorem aes256CbcDecRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hd : P₁.aesDecBlock = P₂.aesDecBlock) :
    SignalPqxdh.aes256CbcDecRef P₁ = SignalPqxdh.aes256CbcDecRef P₂ := by
  funext k iv ct; unfold SignalPqxdh.aes256CbcDecRef SignalPqxdh.cbcDecBlocks; rw [hd]

private theorem aes256CbcHmacEncRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hs : P₁.sha256Compress = P₂.sha256Compress) (he : P₁.aesEncBlock = P₂.aesEncBlock) :
    SignalPqxdh.aes256CbcHmacEncRef P₁ = SignalPqxdh.aes256CbcHmacEncRef P₂ := by
  funext mk ad pt; unfold SignalPqxdh.aes256CbcHmacEncRef
  rw [aes256CbcEncRef_congr he, hmacSha256Ref_congr hs]

private theorem aes256CbcHmacDecRef_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hs : P₁.sha256Compress = P₂.sha256Compress) (hd : P₁.aesDecBlock = P₂.aesDecBlock) :
    SignalPqxdh.aes256CbcHmacDecRef P₁ = SignalPqxdh.aes256CbcHmacDecRef P₂ := by
  funext mk ad ct; unfold SignalPqxdh.aes256CbcHmacDecRef
  rw [hmacSha256Ref_congr hs, aes256CbcDecRef_congr hd]

private theorem model_initiateKeys_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hsig : P₁.sigVerify = P₂.sigVerify)
    (henc : P₁.kemEncaps = P₂.kemEncaps)
    (hxBase : P₁.x25519Base = P₂.x25519Base)
    (hx : P₁.x25519 = P₂.x25519)
    (hhkdf : P₁.hkdfDerive96 = P₂.hkdfDerive96)
    (inp : SignalPqxdh.InitiateKeysInput) :
    SignalPqxdh.Model.initiateKeys P₁ inp = SignalPqxdh.Model.initiateKeys P₂ inp := by
  unfold SignalPqxdh.Model.initiateKeys
  rw [hsig, henc, hxBase, hx, hhkdf]

private theorem model_acceptKeys_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hcan : P₁.isCanonical = P₂.isCanonical)
    (hx : P₁.x25519 = P₂.x25519)
    (hdec : P₁.kemDecaps = P₂.kemDecaps)
    (hhkdf : P₁.hkdfDerive96 = P₂.hkdfDerive96)
    (inp : SignalPqxdh.AcceptKeysInput) :
    SignalPqxdh.Model.acceptKeys P₁ inp = SignalPqxdh.Model.acceptKeys P₂ inp := by
  unfold SignalPqxdh.Model.acceptKeys
  rw [hcan, hx, hdec, hhkdf]

private theorem model_initiate_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hk : ∀ i, SignalPqxdh.Model.initiateKeys P₁ i = SignalPqxdh.Model.initiateKeys P₂ i)
    (hxBase : P₁.x25519Base = P₂.x25519Base)
    (hx : P₁.x25519 = P₂.x25519)
    (hroot : P₁.rootCreateChain = P₂.rootCreateChain)
    (hseed : P₁.chainKdfSeed = P₂.chainKdfSeed)
    (hnext : P₁.chainKdfNext = P₂.chainKdfNext)
    (hspqr : P₁.spqrInitSend = P₂.spqrInitSend)
    (hdmk : P₁.deriveMsgKeys = P₂.deriveMsgKeys)
    (haead : P₁.aeadEnc = P₂.aeadEnc)
    (inp : SignalPqxdh.InitiateInput) :
    SignalPqxdh.Model.initiate P₁ inp = SignalPqxdh.Model.initiate P₂ inp := by
  unfold SignalPqxdh.Model.initiate
  rw [hk inp.toInitiateKeysInput, hxBase, hx, hroot, hseed, hnext, hspqr, hdmk, haead]

private theorem model_accept_congr {P₁ P₂ : SignalPqxdh.Primitives}
    (hk : ∀ i, SignalPqxdh.Model.acceptKeys P₁ i = SignalPqxdh.Model.acceptKeys P₂ i)
    (hx : P₁.x25519 = P₂.x25519)
    (hroot : P₁.rootCreateChain = P₂.rootCreateChain)
    (hseed : P₁.chainKdfSeed = P₂.chainKdfSeed)
    (hnext : P₁.chainKdfNext = P₂.chainKdfNext)
    (hspqr : P₁.spqrInitRecv = P₂.spqrInitRecv)
    (hdmk : P₁.deriveMsgKeys = P₂.deriveMsgKeys)
    (haead : P₁.aeadDec = P₂.aeadDec)
    (inp : SignalPqxdh.AcceptInput) :
    SignalPqxdh.Model.accept P₁ inp = SignalPqxdh.Model.accept P₂ inp := by
  unfold SignalPqxdh.Model.accept
  rw [hk inp.keysInp, hx, hroot, hseed, hnext, hspqr, hdmk, haead]

private theorem modelPrims_sigVerify (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).sigVerify =
      SignalPqxdh.xeddsaVerifyRef
        { blockLevelPrims X W with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X W) } := rfl

private theorem modelPrims_eq_def (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    modelPrims X W =
      let B := blockLevelPrims X W
      let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
      { B1 with
        sigVerify := SignalPqxdh.xeddsaVerifyRef B1
        isCanonical := SignalPqxdh.isCanonicalRef B1
        hkdfDerive96 := SignalPqxdh.hkdfDerive96Ref B1
        rootCreateChain := SignalPqxdh.rootCreateChainRef B1
        chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1
        chainKdfNext := SignalPqxdh.chainKdfNextRef B1
        deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1
        aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1
        aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 } := rfl

private theorem upd_isCanonical (B : SignalPqxdh.Primitives) (sv f h96 rcc cks ckn dmk ae ad)
    (pk : List UInt8) :
    ({ B with sigVerify := sv, isCanonical := f, hkdfDerive96 := h96, rootCreateChain := rcc,
              chainKdfSeed := cks, chainKdfNext := ckn, deriveMsgKeys := dmk,
              aeadEnc := ae, aeadDec := ad } : SignalPqxdh.Primitives).isCanonical pk = f pk := rfl

private theorem upd_sha512_isCanonicalRef (B : SignalPqxdh.Primitives)
    (s : List UInt8 → List UInt8) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl

private theorem modelPrims_isCanonical (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).isCanonical = SignalPqxdh.isCanonicalRef (blockLevelPrims X W) := by
  funext pk
  exact (congrArg (fun M : SignalPqxdh.Primitives => M.isCanonical pk)
    (modelPrims_eq_def X W)).trans
    ((upd_isCanonical _ _ _ _ _ _ _ _ _ _ pk).trans
      (upd_sha512_isCanonicalRef _ _ pk))

/-- `Model.initiateKeys` at `modelPrims` is invariant across any two `DalekPrimsSound` witnesses. -/
theorem initiateKeys_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (h₁ : DalekPrimsSound Qd₁) (h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (inp : SignalPqxdh.InitiateKeysInput) :
    SignalPqxdh.Model.initiateKeys (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) inp =
      SignalPqxdh.Model.initiateKeys (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) inp := by
  apply model_initiateKeys_congr
  · rw [modelPrims_sigVerify, modelPrims_sigVerify, sha512Ref_ofHooks_indep X C Qh Qd₁ Qd₂]
    funext pk m sig
    exact xeddsaVerifyRef_congr_of_sound h₁ h₂ X C Qh _ pk m sig
  · rfl
  · rfl
  · rfl
  · exact hkdfDerive96Ref_congr rfl

/-- `Model.acceptKeys` at `modelPrims` is invariant across any two `DalekPrimsSound` witnesses. -/
theorem acceptKeys_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (h₁ : DalekPrimsSound Qd₁) (h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (inp : SignalPqxdh.AcceptKeysInput) :
    SignalPqxdh.Model.acceptKeys (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) inp =
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) inp := by
  apply model_acceptKeys_congr
  · rw [modelPrims_isCanonical, modelPrims_isCanonical]
    funext pk
    exact isCanonicalRef_congr_of_sound h₁ h₂ X C Qh pk
  · rfl
  · rfl
  · exact hkdfDerive96Ref_congr rfl

/-- `Model.initiate` at `modelPrims` is invariant across any two `DalekPrimsSound` witnesses. -/
theorem initiate_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (h₁ : DalekPrimsSound Qd₁) (h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (inp : SignalPqxdh.InitiateInput) :
    SignalPqxdh.Model.initiate (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) inp =
      SignalPqxdh.Model.initiate (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) inp :=
  model_initiate_congr (initiateKeys_congr_of_sound h₁ h₂ X C Qh)
    rfl rfl (rootCreateChainRef_congr rfl) (chainKdfSeedRef_congr rfl)
    (chainKdfNextRef_congr rfl) rfl (deriveMsgKeysRef_congr rfl)
    (aes256CbcHmacEncRef_congr rfl rfl) inp

/-- `Model.accept` at `modelPrims` is invariant across any two `DalekPrimsSound` witnesses. -/
theorem accept_congr_of_sound {Qd₁ Qd₂ : DalekPrims}
    (h₁ : DalekPrimsSound Qd₁) (h₂ : DalekPrimsSound Qd₂)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (inp : SignalPqxdh.AcceptInput) :
    SignalPqxdh.Model.accept (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₁⟩) inp =
      SignalPqxdh.Model.accept (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh Qd₂⟩) inp :=
  model_accept_congr (acceptKeys_congr_of_sound h₁ h₂ X C Qh)
    rfl (rootCreateChainRef_congr rfl) (chainKdfSeedRef_congr rfl)
    (chainKdfNextRef_congr rfl) rfl (deriveMsgKeysRef_congr rfl)
    (aes256CbcHmacDecRef_congr rfl rfl) inp

/-! ## 6. Direct Machine-Code Postcondition Bridges at `dalekPrimsRef` (Blocks 202 & 204) -/

/-- Direct Block 202 (`<PublicKey>::is_canonical`) reduction at `dalekPrimsRef`: when `pk` has
length 32, `montToEdwards (ofU8 pk) 0` and `edSmul edOrderL P == edZero` (`B08` + `B19`) compute
`SignalPqxdh.isCanonicalRef` at `dalekPrimsRef` directly. -/
theorem isCanonicalRef_dalekPrimsRef_eq
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) pk =
      if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk then
        match montToEdwards (ofU8 pk) 0 with
        | some P => edSmul edOrderL P == edZero
        | none => false
      else false := by
  rw [isCanonicalRef_eq_closed_of_sound dalekPrimsRef_sound X C Qh pk]
  split
  · rename_i hcond
    have hlen : pk.length = 32 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1.1
    have h0 : (0#8 : BitVec 8).toNat = 0 := rfl
    rw [montLiftEd_eq_montToEdwards, u8Vec_toList_of_length hlen, h0]
  · rfl

/-- Direct Block 204 (`verify_signature_for_multipart_message`) reduction at `dalekPrimsRef`:
matches `montToEdwards (ofU8 pk) signBit.toNat` (`B08`) and `edDoubleScalarMulBasepoint` +
`encodeEd` (`B14`, `EdwardsNeg`, `B02`, `B01`, `B17`, `B14`) directly against
`SignalPqxdh.xeddsaVerifyRef` at `dalekPrimsRef`. -/
theorem xeddsaVerifyRef_dalekPrimsRef_eq
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (sha512 : List UInt8 → List UInt8) (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef
      ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩ with sha512 }) pk m sig =
      if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
        let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
        match montToEdwards (ofU8 pk) signBit.toNat with
        | none => false
        | some Apt =>
          let capA := toU8 (encodeEd Apt)
          let capR := sig.take 32
          let sRaw := sig.drop 32
          let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
          let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
          let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
          let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
          capRCheck == capR
      else false := by
  rw [xeddsaVerifyRef_eq_closed_of_sound dalekPrimsRef_sound X C Qh sha512 pk m sig]
  split
  · rename_i hcond
    have hlen : pk.length = 32 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1.1
    change (match montLiftEd (u8Vec 32 pk) ((sig.getD 63 0 &&& 0x80) >>> 7).toBitVec with
      | none => false
      | some Apt => _) =
      (match montToEdwards (ofU8 pk) ((sig.getD 63 0 &&& 0x80) >>> 7).toNat with
      | none => false
      | some Apt => _)
    rw [montLiftEd_eq_montToEdwards, u8Vec_toList_of_length hlen, UInt8.toNat_toBitVec]
  · rfl

/-- Connects `B08` + `EdwardsNeg` + `B02` + `B01` + `B17` + `B14` (`edDoubleScalarMulBasepoint` on
`dalekEdNegBytes pt_bs`) directly to the `capRCheck` byte list of `xeddsaVerifyRef_dalekPrimsRef_eq`. -/
theorem xeddsaVerifyRef_dalekPrimsRef_capRCheck_eq
    {pk_bs pt_bs : List (BitVec 8)} {sign : Nat} {Apt : EdPoint}
    {hIn : List.Vector (BitVec 8) 64} {sIn : List.Vector (BitVec 8) 32}
    (hmont : montToEdwards pk_bs sign = some Apt)
    (hpt_bnd : fe51Point4Bounded pt_bs (2 ^ 52))
    (hpt_eq : edExtOfBytes pt_bs = edExtOfAffine Apt) :
    toU8 (encodeEd (edExtToAffine (edDoubleScalarMulBasepoint
      (natToLeBytes 32 (leBytesToNat hIn.toList % edOrderL))
      (dalekEdNegBytes pt_bs)
      (natToLeBytes 32 (leBytesToNat sIn.toList % edOrderL))))) =
      toU8 (encodeEd (edSub
        (edSmul (leBytesToNat sIn.toList % edOrderL) edBasepoint)
        (edSmul (leBytesToNat hIn.toList % edOrderL) Apt))) := by
  let hNat := leBytesToNat hIn.toList % edOrderL
  let sNat := leBytesToNat sIn.toList % edOrderL
  have hl_lt_256_32 : edOrderL < 256 ^ 32 := by unfold edOrderL; decide
  have hh_lt : hNat < edOrderL := Nat.mod_lt _ (by unfold edOrderL; decide)
  have hs_lt : sNat < edOrderL := Nat.mod_lt _ (by unfold edOrderL; decide)
  have hh_len : (natToLeBytes 32 hNat).length = 32 := natToLeBytes_len 32 hNat
  have hs_len : (natToLeBytes 32 sNat).length = 32 := natToLeBytes_len 32 sNat
  have hh_val : leBytesToNat (natToLeBytes 32 hNat) = hNat :=
    leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans hh_lt hl_lt_256_32)
  have hs_val : leBytesToNat (natToLeBytes 32 sNat) = sNat :=
    leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans hs_lt hl_lt_256_32)
  have hpipe := pipeline2_xeddsa_verify_compress_eq hmont hpt_bnd hpt_eq
    hh_len (by rw [hh_val]; exact hh_lt) hs_len (by rw [hs_val]; exact hs_lt)
  rw [hpipe, hh_val, hs_val]

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge
