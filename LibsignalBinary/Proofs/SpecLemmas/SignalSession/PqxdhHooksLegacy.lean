/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.HooksCommonLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec

/-!
# Legacy / Ghost PQXDH & SPQR Hook Helpers (`LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy`)

Proof-side definitions for the 9 directly linked primitive symbols (`7` `curve25519-dalek`
operations and `2` ML-KEM-768 compressed-keypair projections `pk1`/`pk2`), bump-allocator
`libcruxHmacHook`, the 160-byte `EdPoint` codec (`packEd160` / `unpackEd160` / `packEdBytes` /
`unpackEdBytes`) bridging fixed-image stub proofs to `VerifiedLibraries.Common.EdPoint`, and the
legacy demangled tables (`spqrHookTable`, `pqxdhHookTable`), moved out of
`LibsignalBinary/Specifications/LibsignalE2E/PqxdhHooksCommon.lean`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames

/-- `libcrux_hmac::hmac(alg = w0, key = (x1, x2), data = (x3, x4), tag_len = (w5, x6))` with sret
`x8` (legacy bump-allocator hook): fails closed (`Exception`) when `alg != Algorithm::Sha256`
(`w0 != 0#32`); panics when `key.len() ≥ 2^32` or `data.len() ≥ 2^32`; otherwise allocates a 32-byte
`Vec<u8>` (`cap = 32`) at `x8` holding `HMAC.hmacWith F key data`, truncated (`Vec::truncate`) to
`min x6 32` when `tag_len` is `Some` (`w5 & 1 != 0`). -/
@[expose] def libcruxHmacHook (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState)
    (s : State) : State :=
  if (s.readReg64 .x0).setWidth 32 != 0#32 then
    s.setStatus (.Exception "libcrux_hmac::hmac: alg != Sha256")
  else
    let keyLen := (s.readReg64 .x2).toNat
    let dataLen := (s.readReg64 .x4).toNat
    if keyLen < 2 ^ 32 ∧ dataLen < 2 ^ 32 then
      let key := s.mem.readBytes (s.readReg64 .x1) keyLen
      let data := s.mem.readBytes (s.readReg64 .x3) dataLen
      let tag := HMAC.hmacWith F key data
      let outLen :=
        if (s.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
          min (s.readReg64 .x6).toNat tag.length
        else
          tag.length
      bumpThen tag.length 1
        (fun s p =>
          retHook (fun s =>
            s.setMem (writeVecHeader (s.mem.writeBytes p tag) (s.readReg64 .x8)
              (BitVec.ofNat 64 tag.length) p (BitVec.ofNat 64 outLen))) s)
        allocPanicHook s
    else
      Rust.panicked s

end CryptoVerification.E2E

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalSpqrV1
  (MlKem mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemEncaps1Name mlkemEncaps2Name
   mlkemDecapsName mlkemValidatePkName libcruxHmacName)
open CryptoVerification.E2E
  (PqxdhPrims readVecN ofU8 toU8 fitVec u8Vec vecU8
   compress512Hook kemEncapsHook kemDecapsHook
   mlkemFromSeedHook mlkemEncaps1Hook mlkemEncaps2Hook mlkemDecapsHook mlkemValidatePkHook
   libcruxHmacHook)
open VerifiedLibraries.Common
  (EdPoint p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven leBytesToNat natToLeBytes
   edZero edBasepoint edAdd edNeg edSmul encodeEd)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
  (natToLeBytes_leBytesToNat leBytesToNat_natToLeBytes_of_lt leBytesToNat_lt recoverXEven_some_props)

/-! ## 1. 160-Byte `EdPoint` Codec (`80 + 80` Little-Endian Bytes) -/

theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  simp [ofU8, toU8, List.map_map, Function.comp_def]

theorem toU8_ofU8 (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  simp [ofU8, toU8, List.map_map, Function.comp_def]

/-- Pack `P : EdPoint` into 160 little-endian `BitVec 8` bytes (`80` bytes for `x`, `80` for `y`). -/
@[expose] def packEdBv8 (P : EdPoint) : List (BitVec 8) :=
  natToLeBytes 80 P.x ++ natToLeBytes 80 P.y

@[simp] theorem packEdBv8_length (P : EdPoint) : (packEdBv8 P).length = 160 := by
  simp [packEdBv8, natToLeBytes]

/-- Pack `P : EdPoint` into a 160-byte `List.Vector (BitVec 8) 160`. -/
@[expose] def packEd160 (P : EdPoint) : List.Vector (BitVec 8) 160 :=
  ⟨packEdBv8 P, packEdBv8_length P⟩

/-- Unpack 160 little-endian `BitVec 8` bytes into `EdPoint`. -/
@[expose] def unpackEdBv8 (bs : List (BitVec 8)) : EdPoint :=
  ⟨leBytesToNat (bs.take 80), leBytesToNat ((bs.drop 80).take 80)⟩

/-- Unpack a 160-byte `List.Vector (BitVec 8) 160` into `EdPoint`. -/
@[expose] def unpackEd160 (v : List.Vector (BitVec 8) 160) : EdPoint :=
  unpackEdBv8 v.toList

/-- Pack `P : EdPoint` into 160 `UInt8` bytes (`SignalPqxdh.Bytes`). -/
@[expose] def packEdBytes (P : EdPoint) : List UInt8 :=
  toU8 (packEdBv8 P)

@[simp] theorem packEdBytes_length (P : EdPoint) : (packEdBytes P).length = 160 := by
  simp [packEdBytes, toU8]

/-- Unpack `bs : List UInt8` (fitted to 160 bytes via `u8Vec 160`) into `EdPoint`. -/
@[expose] def unpackEdBytes (bs : List UInt8) : EdPoint :=
  unpackEd160 (u8Vec 160 bs)

theorem unpackEdBv8_packEdBv8 {P : EdPoint} (hx : P.x < 256 ^ 80) (hy : P.y < 256 ^ 80) :
    unpackEdBv8 (packEdBv8 P) = P := by
  have hlx : (natToLeBytes 80 P.x).length = 80 := by simp [natToLeBytes]
  have hly : (natToLeBytes 80 P.y).length = 80 := by simp [natToLeBytes]
  rcases P with ⟨x, y⟩
  simp only [unpackEdBv8, packEdBv8, List.take_left' hlx, List.drop_left' hlx,
    List.take_of_length_le (Nat.le_of_eq hly)]
  rw [leBytesToNat_natToLeBytes_of_lt hx, leBytesToNat_natToLeBytes_of_lt hy]

theorem unpackEdBytes_packEdBytes {P : EdPoint} (hx : P.x < 256 ^ 80) (hy : P.y < 256 ^ 80) :
    unpackEdBytes (packEdBytes P) = P := by
  have hu : (u8Vec 160 (packEdBytes P)).toList = packEdBv8 P := by
    simp only [u8Vec, fitVec, packEdBytes, ofU8_toU8]
    exact List.take_left' (packEdBv8_length P)
  simp only [unpackEdBytes, unpackEd160, hu]
  exact unpackEdBv8_packEdBv8 hx hy

theorem packEdBv8_unpackEdBv8 {bs : List (BitVec 8)} (h : bs.length = 160) :
    packEdBv8 (unpackEdBv8 bs) = bs := by
  have hl1 : (bs.take 80).length = 80 := by simp [h]
  have hd : (bs.drop 80).take 80 = bs.drop 80 := List.take_of_length_le (by simp [h])
  have hdl : (bs.drop 80).length = 80 := by simp [h]
  unfold packEdBv8 unpackEdBv8
  dsimp only
  rw [hd]
  have h1 := natToLeBytes_leBytesToNat (bs.take 80)
  rw [hl1] at h1
  have h2 := natToLeBytes_leBytesToNat (bs.drop 80)
  rw [hdl] at h2
  rw [h1, h2, List.take_append_drop]

theorem packEdBytes_unpackEdBytes {bs : List UInt8} (h : bs.length = 160) :
    packEdBytes (unpackEdBytes bs) = bs := by
  have ho : (ofU8 bs).length = 160 := by simp [ofU8, h]
  have hu : (u8Vec 160 bs).toList = ofU8 bs := by
    simp only [u8Vec, fitVec]
    exact List.take_left' ho
  simp only [packEdBytes, unpackEdBytes, unpackEd160, hu, packEdBv8_unpackEdBv8 ho, toU8_ofU8]

theorem unpackEdBv8_coords_lt (bs : List (BitVec 8)) :
    (unpackEdBv8 bs).x < 256 ^ 80 ∧ (unpackEdBv8 bs).y < 256 ^ 80 := by
  refine ⟨Nat.lt_of_lt_of_le (leBytesToNat_lt _) (Nat.pow_le_pow_right (by decide) (by simp)),
    Nat.lt_of_lt_of_le (leBytesToNat_lt _) (Nat.pow_le_pow_right (by decide) (by simp))⟩

theorem unpackEdBytes_coords_lt (bs : List UInt8) :
    (unpackEdBytes bs).x < 256 ^ 80 ∧ (unpackEdBytes bs).y < 256 ^ 80 :=
  unpackEdBv8_coords_lt _

theorem p25519_lt_pow256_80 : p25519 < 256 ^ 80 := by decide

attribute [local irreducible] fpInv recoverXEven in
theorem montLiftEd_coords_lt {u : List (BitVec 8)} {s : BitVec 8} {pt : EdPoint}
    (h : SignalPqxdh.montLiftEd u s = some pt) :
    pt.x < 256 ^ 80 ∧ pt.y < 256 ^ 80 := by
  have hp0 : 0 < p25519 := by decide
  dsimp only [SignalPqxdh.montLiftEd] at h
  by_cases hu : ((leBytesToNat (u.take 32) % (2 ^ 255)) % p25519 == p25519 - 1) = true
  · rw [hu] at h; cases h
  · rw [Bool.not_eq_true] at hu
    rw [hu] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
    rcases h with ⟨xEven, hxEven, rfl⟩
    have hx : (if (s &&& 1#8) == 1#8 then VerifiedLibraries.Common.fpNeg xEven else xEven) < p25519 := by
      split
      · exact Nat.mod_lt _ hp0
      · exact (recoverXEven_some_props hxEven).1
    exact ⟨Nat.lt_trans hx p25519_lt_pow256_80,
      Nat.lt_trans (Nat.mod_lt _ hp0) p25519_lt_pow256_80⟩

theorem edNeg_coords_lt (pt : EdPoint) :
    (edNeg pt).x < 256 ^ 80 ∧ (edNeg pt).y < 256 ^ 80 := by
  have hp0 : 0 < p25519 := by decide
  exact ⟨Nat.lt_trans (Nat.mod_lt _ hp0) p25519_lt_pow256_80,
    Nat.lt_trans (Nat.mod_lt _ hp0) p25519_lt_pow256_80⟩

theorem edAdd_coords_lt (P Q : EdPoint) :
    (edAdd P Q).x < 256 ^ 80 ∧ (edAdd P Q).y < 256 ^ 80 := by
  have hp0 : 0 < p25519 := by decide
  exact ⟨Nat.lt_trans (Nat.mod_lt _ hp0) p25519_lt_pow256_80,
    Nat.lt_trans (Nat.mod_lt _ hp0) p25519_lt_pow256_80⟩

/-! ## 2. Closed Curve25519 Legacy Functions Matching `modelPrims` -/

/-- Closed 160-byte `MontgomeryPoint::to_edwards` matching `SignalPqxdh.montLiftEd` via `packEd160`. -/
@[expose] def legacyMontToEd (u : List.Vector (BitVec 8) 32) (sign : BitVec 8) :
    Option (List.Vector (BitVec 8) 160) :=
  (SignalPqxdh.montLiftEd u.toList sign).map packEd160

/-- Closed 160-byte `EdwardsPoint::compress` matching `encodeEd` via `unpackEd160`. -/
@[expose] def legacyCompress (v : List.Vector (BitVec 8) 160) : List.Vector (BitVec 8) 32 :=
  ⟨encodeEd (unpackEd160 v), by simp [encodeEd, natToLeBytes]⟩

/-- Closed 160-byte `<EdwardsPoint as Neg>::neg` matching `edNeg` via `packEd160 ∘ edNeg ∘ unpackEd160`. -/
@[expose] def legacyEdNeg (v : List.Vector (BitVec 8) 160) : List.Vector (BitVec 8) 160 :=
  packEd160 (edNeg (unpackEd160 v))

/-- Point-at-infinity check `Q == O` isolated behind a `regular`-hint `def` so Lean 4.35 kernel
`whnf_core` stops before `BEq.beq` / `Decidable.decide` when `Q` is `edSmul edOrderL _`. -/
@[expose] def eqEdZero (Q : EdPoint) : Bool := Q == edZero

theorem eqEdZero_eq (Q : EdPoint) : eqEdZero Q = (Q == edZero) := rfl

/-- Closed 160-byte `EdwardsPoint::is_torsion_free` matching `[ℓ]P == O` via `unpackEd160`. -/
@[expose] def legacyIsTorsionFree (v : List.Vector (BitVec 8) 160) : Bool :=
  eqEdZero (edSmul edOrderL (unpackEd160 v))

/-- Closed 160-byte `vartime_double_scalar_mul_basepoint` matching `[h]A + [s]B` via `packEd160`/`unpackEd160`. -/
@[expose] def legacyDsmb (h : List.Vector (BitVec 8) 32) (a : List.Vector (BitVec 8) 160)
    (s : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) 160 :=
  packEd160 (edAdd (edSmul (leBytesToNat h.toList) (unpackEd160 a))
    (edSmul (leBytesToNat s.toList) edBasepoint))

/-- Closed 32-byte `Scalar::from_bytes_mod_order` (`leBytesToNat b % edOrderL`). -/
@[expose] def legacyScalarMod (b : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) 32 :=
  ⟨natToLeBytes 32 (leBytesToNat b.toList % edOrderL), by simp [natToLeBytes]⟩

/-- Closed 64-byte `Scalar::from_bytes_mod_order_wide` (`leBytesToNat b % edOrderL`). -/
@[expose] def legacyScalarWide (b : List.Vector (BitVec 8) 64) : List.Vector (BitVec 8) 32 :=
  ⟨natToLeBytes 32 (leBytesToNat b.toList % edOrderL), by simp [natToLeBytes]⟩

/-! ## 3. Legacy Demangled Stub Names -/

/-- `sha2::sha512::compress512(state = x0, blocks = x1, n = x2)`. -/
abbrev compress512Name : String := "sha2::sha512::compress512"
/-- `MontgomeryPoint::to_edwards(&self = x0, sign = w1) -> Option<EdwardsPoint>` (sret `x8`). -/
abbrev toEdwardsName : String :=
  "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
/-- `EdwardsPoint::compress(&self = x0) -> CompressedEdwardsY` (sret `x8`). -/
abbrev compressName : String := "<curve25519_dalek::edwards::EdwardsPoint>::compress"
/-- `<EdwardsPoint as Neg>::neg(self = x0) -> EdwardsPoint` (sret `x8`). -/
abbrev edNegName : String :=
  "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg"
/-- `EdwardsPoint::is_torsion_free(&self = x0) -> bool`. -/
abbrev torsionFreeName : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint(a = x0, A = x1, b = x2)` (sret `x8`). -/
abbrev dsmbName : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"
/-- `Scalar::from_bytes_mod_order(bytes = x0) -> Scalar` (sret `x8`). -/
abbrev scalarModName : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
/-- `Scalar::from_bytes_mod_order_wide(bytes = x0) -> Scalar` (sret `x8`). -/
abbrev scalarWideName : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
/-- `mlkem1024::kyber::encapsulate(pk = x0, randomness = x1) -> (ct, ss)` (sret `x8`). -/
abbrev kemEncapsName : String := "libcrux_ml_kem::mlkem1024::kyber::encapsulate"
/-- `mlkem1024::kyber::decapsulate(sk = x0, ct = x1) -> ss` (sret `x8`). -/
abbrev kemDecapsName : String := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"

/-! ## 4. Legacy Primitive Hook Functions & Demangled Tables -/

/-- `MontgomeryPoint::to_edwards(&u = x0, sign = w1)` with `Option<EdwardsPoint>` at sret `x8`. -/
@[expose] def toEdwardsHook
    (montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160))
    (s : State) : State :=
  let r := s.readReg64 .x8
  let m := match montToEd (readVecN s.mem (s.readReg64 .x0) 32)
      ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
    | some p => (s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList
    | none => s.mem.write64 r 0#64
  returnToLinkRegister (s.setMem m)

/-- `EdwardsPoint::compress(&p = x0)`: `mem[x8 .. +32] := compress mem[x0 .. +160]`; `pc := lr`. -/
@[expose] def compressHook (compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32)
    (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (compress (readVecN s.mem (s.readReg64 .x0) 160)).toList))

/-- `<EdwardsPoint as Neg>::neg(&p = x0)`: `mem[x8 .. +160] := edNeg mem[x0 .. +160]`; `pc := lr`. -/
@[expose] def edNegHook (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160)
    (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (edNeg (readVecN s.mem (s.readReg64 .x0) 160)).toList))

/-- `EdwardsPoint::is_torsion_free(&p = x0) -> bool`: `x0 := 1` if true, else `0`; `pc := lr`. -/
@[expose] def torsionFreeHook (isTorsionFree : List.Vector (BitVec 8) 160 → Bool)
    (s : State) : State :=
  returnToLinkRegister (s.writeReg64 .x0
    (if isTorsionFree (readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64))

/-- `vartime_double_scalar_mul_basepoint(&a = x0, &A = x1, &b = x2)` with sret `x8`. -/
@[expose] def dsmbHook (dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (dsmb (readVecN s.mem (s.readReg64 .x0) 32) (readVecN s.mem (s.readReg64 .x1) 160)
      (readVecN s.mem (s.readReg64 .x2) 32)).toList))

/-- `Scalar::from_bytes_mod_order(&b = x0)`: `mem[x8 .. +32] := scalarMod mem[x0 .. +32]`. -/
@[expose] def scalarModHook (scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32)
    (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (scalarMod (readVecN s.mem (s.readReg64 .x0) 32)).toList))

/-- `Scalar::from_bytes_mod_order_wide(&b = x0)`: `mem[x8 .. +32] := scalarWide mem[x0 .. +64]`. -/
@[expose] def scalarWideHook (scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32)
    (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (scalarWide (readVecN s.mem (s.readReg64 .x0) 64)).toList))

/-- `<KeyPairCompressedBytes>::pk1(&kp = x0) -> &[u8; 64]`: returns `x0 + 2304#64`. -/
@[expose] def mlkemPk1Hook : State → State :=
  retHook fun s => s.writeReg64 .x0 (s.readReg64 .x0 + 2304#64)

/-- `<KeyPairCompressedBytes>::pk2(&kp = x0) -> &[u8; 1152]`: returns `x0 + 1152#64`. -/
@[expose] def mlkemPk2Hook : State → State :=
  retHook fun s => s.writeReg64 .x0 (s.readReg64 .x0 + 1152#64)

/-- Legacy demangled SPQR V1 rows (8) for fixed-image / intermediate ghost proofs. -/
@[expose] def spqrHookTable (C : Crypto) (K : MlKem) :
    List (String × (State → State)) :=
  [(mlkemFromSeedName,   mlkemFromSeedHook K),
   (mlkemPk1Name,        mlkemPk1Hook),
   (mlkemPk2Name,        mlkemPk2Hook),
   (mlkemEncaps1Name,    mlkemEncaps1Hook K),
   (mlkemEncaps2Name,    mlkemEncaps2Hook K),
   (mlkemDecapsName,     mlkemDecapsHook K),
   (mlkemValidatePkName, mlkemValidatePkHook K),
   (libcruxHmacName,     libcruxHmacHook C.F)]

/-- Legacy demangled PQXDH + SPQR rows (18) for fixed-image / intermediate ghost proofs. -/
@[expose] def pqxdhHookTable (C : Crypto) (Q : PqxdhPrims) :
    List (String × (State → State)) :=
  [(compress512Name,     compress512Hook Q.F512),
   (toEdwardsName,       toEdwardsHook legacyMontToEd),
   (compressName,        compressHook legacyCompress),
   (edNegName,           edNegHook legacyEdNeg),
   (torsionFreeName,     torsionFreeHook legacyIsTorsionFree),
   (dsmbName,            dsmbHook legacyDsmb),
   (scalarModName,       scalarModHook legacyScalarMod),
   (scalarWideName,      scalarWideHook legacyScalarWide),
   (kemEncapsName,       kemEncapsHook Q.encaps),
   (kemDecapsName,       kemDecapsHook Q.decaps)] ++ spqrHookTable C Q.K

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
