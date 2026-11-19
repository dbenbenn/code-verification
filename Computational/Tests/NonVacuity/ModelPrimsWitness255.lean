/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SignalPqxdh.CwfPrimitives
public import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
public import Computational.Proofs.E2E.ComposedBinaryLinkV1
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
import Computational.Tests.XeddsaRomNonVac
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod
import VCVio.EvalDist.Monad.Basic

/-!
# Concrete `BitVec 255` Primitive Witness

Constructs a concrete primitive witness `(Pt := BitVec 255, dh255, c255, K255, Q255, W255, X255)`
backed by Curve25519 scalar multiplication on canonical prime-order points (and the identity on
non-canonical `BitVec 255` encodings), and proves `dh255.Commutes`, `DhKerUniform dh255`,
`X25519RealizesDh c255 dh255 encPt255 encT255`, and `ModelPrimsCryptoAssumptions X255 W255` against
the closed Curve25519 operations in `modelPrims`.

Points in `BitVec 255` embed into 32-byte keys with top bit clear (`encPt255`). The witness is
intentionally insecure (`X255_pre.kemKeyGen` exposes its 32-byte seed in the public key and
`K255`/`Q255` return constant shared secrets) and is used only to witness joint consistency of the
primitive hypotheses.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoGames.LibsignalSM.Proofs.Correctness
open _root_.SignalPqxdh (
  fitBytes word256ToBytes clampScalar25519 clampScalar25519_length sampleScalar32 sampleBytes32
  scalarIsInRange isCanonicalRef xeddsaVerifyRef isValidDhTripleRef
  sha512Pad encodeBitLen128BE encodeBitLen64BE chunkBlocks sha512Step sha512Ref
)
open SpecTests.SignalPqxdh
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 clampedScalarZMod clampedScalarZMod_clamp clampedScalarZMod_ne_zero
)
open Computational.Tests.XeddsaRomNonVac (
  edSignZMod_bool edSignZMod_neg clampScalar25519_eq_of_clampedScalarZMod_eq
)
open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven
  leBytesToNat natToLeBytes EdPoint edZero edBasepoint
  edOnCurve edAdd edSub edNeg edSmul encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  montLiftEd natToLeBytes_len u8Vec_toList_of_length
  montLiftEd_eq_montToEdwards montLiftEd_some_onCurve edSmul_edNeg
  isCanonicalRef_blockLevelPrims_eq xeddsaVerifyRef_blockLevelPrims_eq
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge (
  montLiftEd_some_props edPoint_eq_or_edNeg_of_edToMontU_eq
  montLiftEd_u9_even edSmul_edOrderL_edNeg_eq_edZero_iff
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg edOnCurve_edAdd
  edAdd_edZero edZero_edAdd edAdd_edNeg_self edNeg_edZero edNeg_edNeg edAdd_assoc
  edNatSmul edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_add edNatSmul_mul
  edSmul_eq_edNatSmul edSmul_edOrderL_edBasepoint edOrderL_lt_two_pow_256
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (
  edToMontU edToMontU_lt edToMontU_edBasepoint
  decodeU255_natToLeBytes_of_lt montToEdwards_edToMontU
  edBasepoint_ne_edZero edSmul_eight_eq_edZero_iff
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_natToLeBytes_of_lt
)

attribute [local irreducible] fpInv recoverXEven montLiftEd montToEdwards edSmul

/-- 32-byte little-endian encoding of `Q : BitVec 255` with top bit clear. -/
@[expose] def encPt255 (Q : BitVec 255) : List (BitVec 8) :=
  HMAC.keyToBytes32 (Q.zeroExtend 256)

theorem encPt255_length (Q : BitVec 255) : (encPt255 Q).length = 32 :=
  length_keyToBytes32 (Q.zeroExtend 256)

@[expose] def encT255 (Q : BitVec 255) : PublicKey := ⟨vec32 (encPt255 Q)⟩

/-- Left inverse of `encT255` that truncates a 32-byte little-endian key to 255 bits. -/
@[expose] def decT255 (pk : PublicKey) : Option (BitVec 255) :=
  some ((HKDF.bytesToKey32 pk.1.toList).truncate 255)

/-- 32-byte key predicate requiring top bit clear (`bit 255 = 0`). -/
@[expose] def good255 (pk : List UInt8) : Bool :=
  (pk.length == 32) && ((pk.getD 31 0 &&& 0x80) == 0)

/-- Canonical Curve25519 lift of `Q : BitVec 255`: checks `< p25519` (`scalarIsInRange`), lifts with
even sign (`0#8`), and checks prime-order torsion (`[edOrderL] P == edZero`). -/
def liftCanon255 (Q : BitVec 255) : Option EdPoint :=
  if scalarIsInRange (toU8 (encPt255 Q)) then
    match montLiftEd ⟨encPt255 Q, encPt255_length Q⟩ 0#8 with
    | some P => if edSmul edOrderL P == edZero then some P else none
    | none => none
  else none

/-- `DHFun` instance on `BitVec 255` acting via Curve25519 scalar multiplication on canonical
prime-order points and as the identity on non-canonical encodings. -/
def dh255 : DHFun (BitVec 256) (BitVec 255) where
  base := 9#255
  dh k Q :=
    match liftCanon255 Q with
    | some P =>
      let c := (clampedScalarZMod (word256ToBytes k)).val
      BitVec.ofNat 255 (edToMontU (edSmul c P))
    | none => Q

theorem dh255_base_eq : dh255.base = 9#255 := by rfl

/-- `Crypto` instance with identity block primitives and `dh255`-backed X25519 hooks. -/
@[expose] def c255 : Crypto where
  F := fun st _ => st
  E := fun _ b => b
  D := fun _ b => b
  X := fun s u =>
    if good255 (vecU8 u) then
      vec32 (encPt255 (dh255.dh (HKDF.bytesToKey32 s.toList)
        ((HKDF.bytesToKey32 u.toList).truncate 255)))
    else
      List.Vector.replicate 32 0#8
  pubKey := fun s =>
    vec32 (encPt255 (dh255.dh (HKDF.bytesToKey32 s.toList) dh255.base))

/-- Constant `MlKem` witness with total `encaps1`. -/
@[expose] def K255 : MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
    List.Vector.replicate 32 0#8)
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 0#8
  validPk := fun _ _ => true

/-- `PqxdhPrims` witness with zero SHA-512 compression and `K255`. -/
@[expose] def Q255 : PqxdhPrims where
  F512 := fun _ _ => List.Vector.replicate 8 0#64
  encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps := fun _ _ => List.Vector.replicate 32 0#8
  K := K255

@[expose] def W255 : PEParams := ⟨c255, Q255⟩

/-- Identity-point XEdDSA signature `encodeEd edZero ‖ 0^32 = (1 :: 0^63)`. -/
def sigZeroEd64 : List UInt8 :=
  (1 : UInt8) :: List.replicate 63 0

/-- Base `UnreachedPqxdhPrimitives` witness whose `kemKeyGen` places the first 32 seed bytes in the
public key (sufficient for `cwfPrimitives_kem_coll_bound`). -/
def X255_pre : UnreachedPqxdhPrimitives where
  sigPkGen := fun a => vecU8 (c255.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
  sigSign := fun _ _ _ => sigZeroEd64
  scalarMul := fun _ _ => List.replicate 32 0
  scalarAdd := fun _ _ => List.replicate 32 0
  kemKeyGen := fun seed => (fitBytes 1568 (seed.take 32), fitBytes 3168 seed)
  pow8 := fun pk => if good255 pk then pk else List.replicate 32 0
  isValidDhTriple := fun _ _ _ => false

private def existsByteAll : Nat → (UInt8 → Bool) → Bool
  | 0, _ => false
  | k + 1, p => p (UInt8.ofNat k) || existsByteAll k p

private def existsBytesOfLen : Nat → (List UInt8 → Bool) → Bool
  | 0, p => p []
  | n + 1, p => existsByteAll 256 (fun b => existsBytesOfLen n (fun bs => p (b :: bs)))

private def onCurveKeyModelB (P₀ : SignalPqxdh.Primitives) (pk : List UInt8) : Bool :=
  P₀.isCanonical pk || existsBytesOfLen 32 (fun e => P₀.pow8 pk == P₀.pow8 (P₀.x25519Base e))

/-- Constructive finite-domain decision procedure for `isValidDhTripleRef (modelPrims X₀ W₀)`.
Enumerates up to `256 ^ 32` 32-byte candidate scalars, so while computable, running it in practice
(e.g. `#eval X255.isValidDhTriple [] [] []`) will not finish unless an early check short-circuits. -/
def isValidDhTripleModelB (X₀ : UnreachedPqxdhPrimitives) (W₀ : PEParams)
    (A B Z : List UInt8) : Bool :=
  let P₀ := modelPrims X₀ W₀
  onCurveKeyModelB P₀ A && onCurveKeyModelB P₀ B &&
    (existsBytesOfLen 32 (fun a => A == P₀.x25519Base a && P₀.pow8 Z == P₀.pow8 (P₀.x25519 a B)) ||
     existsBytesOfLen 32 (fun b => B == P₀.x25519Base b && P₀.pow8 Z == P₀.pow8 (P₀.x25519 b A)))

/-- `X255_pre` with `isValidDhTriple` set to the constructive `256 ^ 32`-scalar search
`isValidDhTripleModelB` (computable, though infeasible to evaluate exhaustively in practice). -/
def X255 : UnreachedPqxdhPrimitives :=
  { X255_pre with
    isValidDhTriple := isValidDhTripleModelB X255_pre W255 }

/-! ## 1. Byte, `BitVec 255`, and `< p25519` Range-Check Bridges -/

private theorem existsByteAll_iff_aux (p : UInt8 → Bool) :
    ∀ m : Nat, existsByteAll m p = true ↔ ∃ k < m, p (UInt8.ofNat k) = true
  | 0 => by simp [existsByteAll]
  | k + 1 => by
    simp only [existsByteAll, Bool.or_eq_true, existsByteAll_iff_aux p k]
    exact ⟨fun h => h.elim (fun hk => ⟨k, Nat.lt_succ_self k, hk⟩)
        (fun ⟨j, hj, hpj⟩ => ⟨j, Nat.lt_succ_of_lt hj, hpj⟩),
      fun ⟨j, hj, hpj⟩ => (Nat.lt_succ_iff_lt_or_eq.mp hj).elim
        (fun hlt => Or.inr ⟨j, hlt, hpj⟩) (fun hjk => Or.inl (hjk ▸ hpj))⟩

private theorem existsByteAll_256_iff (p : UInt8 → Bool) :
    existsByteAll 256 p = true ↔ ∃ b : UInt8, p b = true := by
  rw [existsByteAll_iff_aux]
  exact ⟨fun ⟨k, _, hk⟩ => ⟨UInt8.ofNat k, hk⟩,
    fun ⟨b, hb⟩ => ⟨b.toNat, b.toBitVec.isLt, by rwa [UInt8.ofNat_toNat]⟩⟩

private theorem existsBytesOfLen_iff :
    ∀ (n : Nat) (p : List UInt8 → Bool),
      existsBytesOfLen n p = true ↔ ∃ bs : List UInt8, bs.length = n ∧ p bs = true
  | 0, p => by
    simp only [existsBytesOfLen]
    exact ⟨fun hp => ⟨[], rfl, hp⟩, fun ⟨bs, hlen, hp⟩ => List.eq_nil_of_length_eq_zero hlen ▸ hp⟩
  | n + 1, p => by
    simp only [existsBytesOfLen, existsByteAll_256_iff, existsBytesOfLen_iff n]
    refine ⟨fun ⟨b, bs, hlen, hp⟩ => ⟨b :: bs, congrArg Nat.succ hlen, hp⟩, ?_⟩
    rintro ⟨_ | ⟨b, bs⟩, hlen, hp⟩
    · cases hlen
    · exact ⟨b, bs, Nat.succ.inj hlen, hp⟩

private theorem u8Vec_32_vecU8_u8Vec (a : List UInt8) :
    u8Vec 32 (vecU8 (u8Vec 32 a)) = u8Vec 32 a := by
  apply List.Vector.eq
  have hlen : (vecU8 (u8Vec 32 a)).length = 32 := by simp [vecU8, toU8]
  rw [u8Vec_toList_of_length hlen]
  simp [vecU8]

theorem isValidDhTripleModelB_eq_ref (X₀ : UnreachedPqxdhPrimitives) (W₀ : PEParams)
    (A B Z : List UInt8) :
    isValidDhTripleModelB X₀ W₀ A B Z = true ↔
      isValidDhTripleRef (modelPrims X₀ W₀) A B Z := by
  let P₀ := modelPrims X₀ W₀
  have hOn (pk : List UInt8) : onCurveKeyModelB P₀ pk = true ↔ SignalPqxdh.onCurveKey P₀ pk := by
    unfold onCurveKeyModelB SignalPqxdh.onCurveKey
    simp only [Bool.or_eq_true, existsBytesOfLen_iff, beq_iff_eq]
  have hBr (U V : List UInt8) :
      existsBytesOfLen 32 (fun a => U == P₀.x25519Base a && P₀.pow8 Z == P₀.pow8 (P₀.x25519 a V)) =
          true ↔
        ∃ a, U = P₀.x25519Base a ∧ P₀.pow8 Z = P₀.pow8 (P₀.x25519 a V) := by
    rw [existsBytesOfLen_iff]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨fun ⟨a, _, h1, h2⟩ => ⟨a, h1, h2⟩, fun ⟨a, h1, h2⟩ => ?_⟩
    refine ⟨vecU8 (u8Vec 32 a), by simp [vecU8, toU8], ?_, ?_⟩
    · dsimp only [P₀, modelPrims, blockLevelPrims] at h1 ⊢
      rwa [u8Vec_32_vecU8_u8Vec]
    · dsimp only [P₀, modelPrims, blockLevelPrims] at h2 ⊢
      rwa [u8Vec_32_vecU8_u8Vec]
  unfold isValidDhTripleModelB isValidDhTripleRef
  simp only [Bool.and_eq_true, Bool.or_eq_true, and_assoc]
  exact ⟨fun ⟨hA, hB, hAB⟩ => ⟨(hOn A).mp hA, (hOn B).mp hB,
      hAB.elim (fun h => Or.inl ((hBr A B).mp h)) (fun h => Or.inr ((hBr B A).mp h))⟩,
    fun ⟨hA, hB, hAB⟩ => ⟨(hOn A).mpr hA, (hOn B).mpr hB,
      hAB.elim (fun h => Or.inl ((hBr A B).mpr h)) (fun h => Or.inr ((hBr B A).mpr h))⟩⟩

private theorem if_true_eq {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

private theorem if_false_eq {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

private theorem bitVec255_ofNat_inj {x y : Nat} (hx : x < 2 ^ 255) (hy : y < 2 ^ 255)
    (h : BitVec.ofNat 255 x = BitVec.ofNat 255 y) : x = y := by
  have ht := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at ht

private theorem edOrderL_eq_l25519 : edOrderL = l25519 := by
  unfold edOrderL l25519; decide

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide

private theorem zeroExtend_truncate_255 (Q : BitVec 255) :
    (Q.zeroExtend 256).truncate 255 = Q := by
  ext i hi; simp

private theorem zeroExtend_255_toNat (Q : BitVec 255) :
    (Q.zeroExtend 256).toNat = Q.toNat := by
  have hlt : Q.toNat < 2 ^ 256 := lt_trans Q.isLt (by decide)
  change (Q.setWidth 256).toNat = Q.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]

private theorem zeroExtend_255_toNat_lt (Q : BitVec 255) :
    (Q.zeroExtend 256).toNat < 2 ^ 255 := by
  rw [zeroExtend_255_toNat]; exact Q.isLt

private theorem truncate_zeroExtend_255_of_testBit_false (w : BitVec 256)
    (h : w.toNat.testBit 255 = false) :
    (w.truncate 255).zeroExtend 256 = w := by
  have hdiv : (w.toNat / 2 ^ 255).testBit 0 = false := by
    rw [Nat.testBit_div_two_pow]; exact h
  have hlt : w.toNat < 2 ^ 255 := by
    have hw := w.isLt
    by_contra hge
    have h1 : w.toNat / 2 ^ 255 = 1 := by omega
    rw [h1] at hdiv; revert hdiv; decide
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

private theorem keyToBytes32_eq_natToLeBytes (w : BitVec 256) :
    HMAC.keyToBytes32 w = natToLeBytes 32 w.toNat := by
  refine List.ext_getElem (by simp [HMAC.keyToBytes32, natToLeBytes_len]) fun j h1 h2 => ?_
  simp only [HMAC.keyToBytes32, natToLeBytes, List.getElem_ofFn, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (8 * j) = 256 ^ j := by rw [Nat.pow_mul]
  rw [hpow, Nat.mod_mod]

theorem encPt255_eq_natToLeBytes (Q : BitVec 255) :
    encPt255 Q = natToLeBytes 32 Q.toNat := by
  unfold encPt255
  rw [keyToBytes32_eq_natToLeBytes, zeroExtend_255_toNat]

theorem encPt255_ofNat_of_lt {u : Nat} (hu : u < 2 ^ 255) :
    encPt255 (BitVec.ofNat 255 u) = natToLeBytes 32 u := by
  rw [encPt255_eq_natToLeBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]

private theorem word256ToBytes_bytesToKey32_ofU8 (bs : List UInt8) (h : bs.length = 32) :
    word256ToBytes (HKDF.bytesToKey32 (ofU8 bs)) = bs := by
  rw [word256ToBytes_eq_toU8_keyToBytes32, keyToBytes32_bytesToKey32 _ (by simp [h]), toU8_ofU8]

private theorem uint8_testBit_7_of_and_80 (b : UInt8) (h : (b &&& 0x80) = 0) :
    b.toNat.testBit 7 = false := by
  have h1 := congrArg (fun x : UInt8 => x.toNat.testBit 7) h
  simp only [UInt8.toNat_and, Nat.testBit_and] at h1
  exact Bool.eq_false_iff.mpr fun hb => by rw [hb] at h1; exact Bool.noConfusion h1

private theorem good255_spec {pk : List UInt8} :
    good255 pk = true ↔ pk.length = 32 ∧ (pk.getD 31 0 &&& 0x80) = 0 := by
  unfold good255
  simp [Bool.and_eq_true, beq_iff_eq]

private theorem encPt255_truncate_of_good255 {pk : List UInt8} (h : good255 pk = true) :
    encPt255 ((HKDF.bytesToKey32 (ofU8 pk)).truncate 255) = ofU8 pk := by
  obtain ⟨hlen, h80⟩ := good255_spec.mp h
  have hw := word256ToBytes_bytesToKey32_ofU8 pk hlen
  have hbit := word_byte_testBit (HKDF.bytesToKey32 (ofU8 pk)).toNat 31 7 (by decide)
  rw [← word256ToBytes_getD _ 31 (by decide), hw] at hbit
  have ht : (HKDF.bytesToKey32 (ofU8 pk)).toNat.testBit 255 = false := by
    rw [← hbit]; exact uint8_testBit_7_of_and_80 _ h80
  unfold encPt255
  rw [truncate_zeroExtend_255_of_testBit_false _ ht,
    keyToBytes32_bytesToKey32 _ (by simp [hlen])]

private theorem toU8_encPt255_truncate_of_good255 {pk : List UInt8} (h : good255 pk = true) :
    toU8 (encPt255 ((HKDF.bytesToKey32 (ofU8 pk)).truncate 255)) = pk := by
  rw [encPt255_truncate_of_good255 h, toU8_ofU8]

theorem encPt255_inj : Function.Injective encPt255 := by
  intro a b h
  have h1 := congrArg HKDF.bytesToKey32 h
  simp only [encPt255, bytesToKey32_keyToBytes32] at h1
  rw [← zeroExtend_truncate_255 a, ← zeroExtend_truncate_255 b, h1]

theorem encPt255_zero : encPt255 0 = List.replicate 32 0#8 := by decide

theorem encPt255_base : encPt255 dh255.base = x25519Base := by decide

private theorem vec32_toList_of_length {bs : List (BitVec 8)} (h : bs.length = 32) :
    (vec32 bs).toList = bs := by
  simp [vec32, h]

private theorem encT255_toList (Q : BitVec 255) : (encT255 Q).1.toList = encPt255 Q :=
  vec32_toList_of_length (encPt255_length Q)

theorem decT255_encT255 (Q : BitVec 255) : decT255 (encT255 Q) = some Q := by
  unfold decT255
  rw [encT255_toList, encPt255, bytesToKey32_keyToBytes32, zeroExtend_truncate_255]

theorem encT255_inj : Function.Injective encT255 := by
  intro a b h
  exact Option.some.inj ((decT255_encT255 a).symm.trans (by rw [h, decT255_encT255]))

theorem encT255_ne_dummyKey (Q : BitVec 255) : encT255 Q ≠ dummyKey := by
  intro h
  have h1 := congrArg
    (fun pk : PublicKey => decide ((HKDF.bytesToKey32 pk.1.toList).toNat < 2 ^ 255)) h
  rw [encT255_toList, encPt255, bytesToKey32_keyToBytes32,
      decide_eq_true (zeroExtend_255_toNat_lt Q)] at h1
  have h2 : decide ((HKDF.bytesToKey32 dummyKey.1.toList).toNat < 2 ^ 255) = false := by decide
  rw [h2] at h1; exact Bool.noConfusion h1

private theorem u8_ofBitVec_ofNat_and80_lt128 :
    ∀ x : Fin 128, (UInt8.ofBitVec (BitVec.ofNat 8 x.val) &&& 0x80) = 0 := by decide

private theorem u8_ofBitVec_ofNat_and7f_eq7f :
    ∀ x : Fin 128, ((UInt8.ofBitVec (BitVec.ofNat 8 x.val) &&& 0x7F) == 0x7F) = (x.val == 127) := by
  decide

private theorem u8_ofBitVec_ofNat_ge_ed (x : Fin 256) :
    (UInt8.ofBitVec (BitVec.ofNat 8 x.val) ≥ (0xED : UInt8)) ↔ x.val ≥ 237 := by
  revert x; decide

private theorem toU8_natToLeBytes_getD {n u i : Nat} (hi : i < n) :
    (toU8 (natToLeBytes n u)).getD i 0 = UInt8.ofBitVec (BitVec.ofNat 8 ((u / 256 ^ i) % 256)) := by
  unfold toU8 natToLeBytes
  rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem good255_toU8_encPt255 (Q : BitVec 255) :
    good255 (toU8 (encPt255 Q)) = true := by
  rw [good255_spec]
  refine ⟨by rw [toU8_length, encPt255_length], ?_⟩
  rw [encPt255_eq_natToLeBytes, toU8_natToLeBytes_getD (by decide : 31 < 32)]
  have hdiv : Q.toNat / 256 ^ 31 < 128 := by
    have := Q.isLt
    have hp : 2 ^ 255 = 128 * 256 ^ 31 := by decide
    omega
  rw [Nat.mod_eq_of_lt (by omega : Q.toNat / 256 ^ 31 < 256)]
  exact u8_ofBitVec_ofNat_and80_lt128 ⟨Q.toNat / 256 ^ 31, hdiv⟩

private theorem good255_replicate_zero : good255 (List.replicate 32 0) = true := by decide

private theorem drop1_take30_toU8_natToLeBytes (u : Nat) :
    ((toU8 (natToLeBytes 32 u)).drop 1).take 30 = toU8 (natToLeBytes 30 ((u / 256) % 256 ^ 30)) := by
  refine List.ext_getElem (by simp [toU8, natToLeBytes]) fun j h1 h2 => ?_
  simp only [toU8, natToLeBytes, List.map_map, Function.comp_apply, List.getElem_take,
    List.getElem_drop, List.getElem_map, List.getElem_range]
  congr 2
  have hj30 : j < 30 := by simp [toU8, natToLeBytes] at h2; exact h2
  have hpow : 256 ^ (1 + j) = 256 * 256 ^ j := by rw [Nat.pow_add]
  have hmod_dvd : 256 ^ j * 256 ∣ 256 ^ 30 := by
    have heq : 30 = (j + 1) + (29 - j) := by omega
    rw [heq, Nat.pow_add, Nat.pow_succ]
    exact Nat.dvd_mul_right _ _
  rcases hmod_dvd with ⟨k, hk⟩
  set q := u / 256
  have hq : q % 256 ^ 30 = (q % 256 ^ 30) % (256 ^ j * 256) +
      (256 ^ j * 256) * ((q % 256 ^ 30) / (256 ^ j * 256)) := (Nat.mod_add_div _ _).symm
  rw [hpow, ← Nat.div_div_eq_div_mul]
  change (q / 256 ^ j) % 256 = ((q % 256 ^ 30) / 256 ^ j) % 256
  have hrem : (q % 256 ^ 30) % (256 ^ j * 256) = q % (256 ^ j * 256) := by
    rw [hk, Nat.mod_mul_right_mod]
  have hdiv1 : q / 256 ^ j = (q % (256 ^ j * 256)) / 256 ^ j + 256 * (q / (256 ^ j * 256)) := by
    conv_lhs => rw [← Nat.mod_add_div q (256 ^ j * 256)]
    have hpos : 0 < 256 ^ j := by positivity
    rw [show 256 ^ j * 256 * (q / (256 ^ j * 256)) = 256 ^ j * (256 * (q / (256 ^ j * 256))) by ring,
      Nat.add_mul_div_left _ _ hpos]
  have hdiv2 : (q % 256 ^ 30) / 256 ^ j =
      (q % (256 ^ j * 256)) / 256 ^ j + 256 * ((q % 256 ^ 30) / (256 ^ j * 256)) := by
    conv_lhs => rw [hq, hrem]
    have hpos : 0 < 256 ^ j := by positivity
    rw [show 256 ^ j * 256 * ((q % 256 ^ 30) / (256 ^ j * 256)) =
        256 ^ j * (256 * ((q % 256 ^ 30) / (256 ^ j * 256))) by ring,
      Nat.add_mul_div_left _ _ hpos]
  rw [hdiv1, hdiv2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

private theorem toU8_natToLeBytes_30_eq_ff_iff {m : Nat} (hm : m < 256 ^ 30) :
    (toU8 (natToLeBytes 30 m) == List.replicate 30 0xFF) = (m == 256 ^ 30 - 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h1 := congrArg (fun l => leBytesToNat (ofU8 l)) h
    rw [ofU8_toU8, leBytesToNat_natToLeBytes_of_lt hm] at h1
    have hff : leBytesToNat (ofU8 (List.replicate 30 (0xFF : UInt8))) = 256 ^ 30 - 1 := by decide
    exact h1.trans hff
  · rintro rfl
    decide

theorem scalarIsInRange_encPt255_iff (Q : BitVec 255) :
    scalarIsInRange (toU8 (encPt255 Q)) = true ↔ Q.toNat < p25519 := by
  have hu : Q.toNat < 2 ^ 255 := Q.isLt
  rw [encPt255_eq_natToLeBytes]
  set u := Q.toNat
  have hb31_lt : u / 256 ^ 31 < 128 := by
    have hp : 2 ^ 255 = 128 * 256 ^ 31 := by decide
    omega
  have hb0_lt : u % 256 < 256 := Nat.mod_lt _ (by decide)
  have hm_lt : (u / 256) % 256 ^ 30 < 256 ^ 30 := Nat.mod_lt _ (by decide)
  have hb0_eq : (toU8 (natToLeBytes 32 u)).getD 0 0 = UInt8.ofBitVec (BitVec.ofNat 8 (u % 256)) := by
    rw [toU8_natToLeBytes_getD (by decide : 0 < 32), Nat.pow_zero, Nat.div_one]
  have hb31_eq : (toU8 (natToLeBytes 32 u)).getD 31 0 =
      UInt8.ofBitVec (BitVec.ofNat 8 (u / 256 ^ 31)) := by
    rw [toU8_natToLeBytes_getD (by decide : 31 < 32),
      Nat.mod_eq_of_lt (by omega : u / 256 ^ 31 < 256)]
  unfold scalarIsInRange
  simp only [hb31_eq, hb0_eq, drop1_take30_toU8_natToLeBytes,
    u8_ofBitVec_ofNat_and80_lt128 ⟨u / 256 ^ 31, hb31_lt⟩,
    u8_ofBitVec_ofNat_and7f_eq7f ⟨u / 256 ^ 31, hb31_lt⟩,
    u8_ofBitVec_ofNat_ge_ed ⟨u % 256, hb0_lt⟩,
    toU8_natToLeBytes_30_eq_ff_iff hm_lt]
  have hdecomp : u = u % 256 + 256 * ((u / 256) % 256 ^ 30) + 256 ^ 31 * (u / 256 ^ 31) := by
    have h1 := (Nat.mod_add_div u 256).symm
    have h2 := (Nat.mod_add_div (u / 256) (256 ^ 30)).symm
    have h3 : (u / 256) / 256 ^ 30 = u / 256 ^ 31 := by
      rw [Nat.div_div_eq_div_mul]; rfl
    omega
  have hp_eq : p25519 = 237 + 256 * (256 ^ 30 - 1) + 256 ^ 31 * 127 := by
    unfold p25519; decide
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

/-! ## 2. Prime-Order Subgroup Arithmetic on `EdPoint` & `liftCanon255` -/

theorem edToMontU_edNeg {P : EdPoint} (hP : edOnCurve P = true) :
    edToMontU (edNeg P) = edToMontU P := by
  unfold edToMontU
  dsimp only [edNeg]
  rw [Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

theorem edNatSmul_mod_edOrderL {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (n : Nat) :
    edNatSmul n P = edNatSmul (n % edOrderL) P := by
  conv_lhs => rw [← Nat.mod_add_div n edOrderL]
  rw [edNatSmul_add (n % edOrderL) (edOrderL * (n / edOrderL)) hP,
    Nat.mul_comm edOrderL (n / edOrderL),
    edNatSmul_mul (n / edOrderL) edOrderL hP,
    hL, edNatSmul_edZero, edAdd_edZero (edOnCurve_edNatSmul _ hP)]

theorem edNatSmul_sub_edOrderL {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) {c : Nat} (hc : c ≤ edOrderL) :
    edNatSmul (edOrderL - c) P = edNeg (edNatSmul c P) := by
  have hA : edOnCurve (edNatSmul (edOrderL - c) P) = true := edOnCurve_edNatSmul _ hP
  have hB : edOnCurve (edNatSmul c P) = true := edOnCurve_edNatSmul _ hP
  have hsum : edAdd (edNatSmul (edOrderL - c) P) (edNatSmul c P) = edZero := by
    rw [← edNatSmul_add (edOrderL - c) c hP, Nat.sub_add_cancel hc, hL]
  have h1 := congrArg (fun X => edAdd X (edNeg (edNatSmul c P))) hsum
  rw [edAdd_assoc hA hB (edOnCurve_edNeg hB), edAdd_edNeg_self hB,
    edAdd_edZero hA, edZero_edAdd (edOnCurve_edNeg hB)] at h1
  exact h1

theorem edNatSmul_ne_edZero_of_zmod_ne_zero {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {z : ZMod l25519} (hz : z ≠ 0) :
    edNatSmul z.val P ≠ edZero := by
  intro h0
  have hinv_mul : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have hval : (z⁻¹.val * z.val) % edOrderL = 1 := by
    rw [edOrderL_eq_l25519, ← ZMod.val_mul, hinv_mul]
    decide
  have h1 : P = edZero := by
    calc P = edNatSmul 1 P := (edNatSmul_one hP).symm
      _ = edNatSmul ((z⁻¹.val * z.val) % edOrderL) P := by rw [hval]
      _ = edNatSmul (z⁻¹.val * z.val) P := (edNatSmul_mod_edOrderL hP hL _).symm
      _ = edNatSmul z⁻¹.val (edNatSmul z.val P) := edNatSmul_mul z⁻¹.val z.val hP
      _ = edZero := by rw [h0, edNatSmul_edZero]
  exact hne h1

theorem edNatSmul_zmod_mul {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a b : ZMod l25519) :
    edNatSmul (a * b).val P = edNatSmul a.val (edNatSmul b.val P) := by
  have hmod : (a * b).val = (a.val * b.val) % edOrderL :=
    (ZMod.val_mul a b).trans (by rw [edOrderL_eq_l25519])
  rw [hmod, ← edNatSmul_mod_edOrderL hP hL, edNatSmul_mul a.val b.val hP]

theorem edNatSmul_zmod_neg {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a : ZMod l25519) :
    edNatSmul (-a).val P = edNeg (edNatSmul a.val P) := by
  by_cases ha : a = 0
  · subst ha
    change edNatSmul 0 P = edNeg (edNatSmul 0 P)
    exact edNeg_edZero.symm
  · have hneg : (-a).val = edOrderL - a.val := by
      rw [ZMod.neg_val, if_false_eq ha, edOrderL_eq_l25519]
    rw [hneg]
    exact edNatSmul_sub_edOrderL hP hL (by rw [edOrderL_eq_l25519]; exact le_of_lt a.val_lt)

theorem edNatSmul_zmod_inj {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a b : ZMod l25519} (heq : edNatSmul a.val P = edNatSmul b.val P) :
    a = b := by
  have hsub : edNatSmul (a + -b).val P = edZero := by
    have hmod : (a + -b).val = (a.val + (-b).val) % edOrderL := by
      rw [ZMod.val_add, edOrderL_eq_l25519]
    rw [hmod, ← edNatSmul_mod_edOrderL hP hL, edNatSmul_add _ _ hP, heq,
      edNatSmul_zmod_neg hP hL b, edAdd_edNeg_self (edOnCurve_edNatSmul _ hP)]
  by_contra hab
  have hne0 : a + -b ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr hab
  exact edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL hne0 hsub

theorem edToMontU_edNatSmul_eq_iff {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a b : ZMod l25519} (ha : a ≠ 0) (hb : b ≠ 0) :
    edToMontU (edNatSmul a.val P) = edToMontU (edNatSmul b.val P) ↔ a = b ∨ a = -b := by
  constructor
  · intro hu
    have hA_on := edOnCurve_edNatSmul a.val hP
    have hB_on := edOnCurve_edNatSmul b.val hP
    have hA_ne := edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL ha
    have hB_ne := edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL hb
    rcases edPoint_eq_or_edNeg_of_edToMontU_eq hA_on hB_on hA_ne hB_ne hu with h1 | h2
    · exact Or.inl (edNatSmul_zmod_inj hP hne hL h1)
    · rw [← edNatSmul_zmod_neg hP hL b] at h2
      exact Or.inr (edNatSmul_zmod_inj hP hne hL h2)
  · rintro (rfl | rfl)
    · rfl
    · rw [edNatSmul_zmod_neg hP hL b, edToMontU_edNeg (edOnCurve_edNatSmul _ hP)]

private theorem zmod_val_lt_two_pow_256 (z : ZMod l25519) : z.val < 2 ^ 256 :=
  lt_trans z.val_lt (by rw [← edOrderL_eq_l25519]; exact edOrderL_lt_two_pow_256)

theorem liftCanon255_some_props {Q : BitVec 255} {P : EdPoint}
    (h : liftCanon255 Q = some P) :
    Q.toNat < p25519 ∧ edOnCurve P = true ∧ P ≠ edZero ∧
      edNatSmul edOrderL P = edZero ∧ edToMontU P = Q.toNat := by
  unfold liftCanon255 at h
  by_cases hsc : scalarIsInRange (toU8 (encPt255 Q)) = true
  · rw [if_true_eq hsc] at h
    have hlt_p : Q.toNat < p25519 := (scalarIsInRange_encPt255_iff Q).mp hsc
    cases hlift : montLiftEd ⟨encPt255 Q, encPt255_length Q⟩ 0#8 with
    | none => rw [hlift] at h; cases h
    | some P' =>
      rw [hlift] at h
      dsimp only at h
      by_cases htf : (edSmul edOrderL P' == edZero) = true
      · rw [if_true_eq htf] at h
        cases h
        rcases montLiftEd_some_props hlift with ⟨hon, hne, hu⟩
        have hdec : decodeU255 (encPt255 Q) % p25519 = Q.toNat := by
          rw [encPt255_eq_natToLeBytes, decodeU255_natToLeBytes_of_lt Q.isLt,
            Nat.mod_eq_of_lt hlt_p]
        have hL : edNatSmul edOrderL P = edZero := by
          rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hon]
          exact beq_iff_eq.mp htf
        exact ⟨hlt_p, hon, hne, hL, hu.trans hdec⟩
      · rw [if_false_eq htf] at h; cases h
  · rw [if_false_eq hsc] at h; cases h

private theorem edNeg_x_even_of_odd {R : EdPoint} (hR : edOnCurve R = true) (hodd : R.x % 2 = 1) :
    (edNeg R).x % 2 = 0 := by
  have hx_lt := edOnCurve_x_lt hR
  dsimp only [edNeg]
  unfold fpNeg
  rw [Nat.mod_eq_of_lt hx_lt]
  have hp_odd : p25519 % 2 = 1 := by unfold p25519; decide
  rw [Nat.mod_eq_of_lt (by omega : p25519 - R.x < p25519)]
  omega

/-- Every non-identity `[edOrderL]`-torsion curve point `R` produces a canonical `BitVec 255`
encoding `BitVec.ofNat 255 (edToMontU R)` whose lift is `R` or `edNeg R`. -/
theorem liftCanon255_ofNat_edToMontU {R : EdPoint}
    (hR : edOnCurve R = true) (hne : R ≠ edZero) (hL : edNatSmul edOrderL R = edZero) :
    ∃ P : EdPoint,
      liftCanon255 (BitVec.ofNat 255 (edToMontU R)) = some P ∧ (P = R ∨ P = edNeg R) := by
  obtain ⟨R0, hR0_def⟩ : ∃ x, (if R.x % 2 == 1 then edNeg R else R) = x := ⟨_, rfl⟩
  have hR0_pm : R0 = R ∨ R0 = edNeg R := by
    rw [← hR0_def]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hR0_on : edOnCurve R0 = true := by
    rcases hR0_pm with rfl | rfl
    · exact hR
    · exact edOnCurve_edNeg hR
  have hR0_ne : R0 ≠ edZero := by
    rcases hR0_pm with rfl | rfl
    · exact hne
    · intro h0
      have h1 := congrArg edNeg h0
      rw [edNeg_edNeg hR, edNeg_edZero] at h1
      exact hne h1
  have hR0_even : R0.x % 2 = 0 := by
    rw [← hR0_def]
    rcases Nat.mod_two_eq_zero_or_one R.x with h0 | h1
    · have hb : (R.x % 2 == 1) = false := by rw [h0]; decide
      rw [hb]; exact h0
    · have hb : (R.x % 2 == 1) = true := by rw [h1]; decide
      rw [hb]; exact edNeg_x_even_of_odd hR h1
  have hR0_u : edToMontU R0 = edToMontU R := by
    rcases hR0_pm with rfl | rfl
    · rfl
    · exact edToMontU_edNeg hR
  have hR0_tf : (edSmul edOrderL R0 == edZero) = true := by
    have htfR : (edSmul edOrderL R == edZero) = true := by
      rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hR]
      exact beq_iff_eq.mpr hL
    rcases hR0_pm with rfl | rfl
    · exact htfR
    · rw [edSmul_edOrderL_edNeg_eq_edZero_iff hR]; exact htfR
  have hu_lt_p : edToMontU R < p25519 := edToMontU_lt R
  have hu_lt_255 : edToMontU R < 2 ^ 255 := lt_trans hu_lt_p p25519_lt_two_pow_255
  let Q := BitVec.ofNat 255 (edToMontU R)
  have hQ_toNat : Q.toNat = edToMontU R := by
    dsimp only [Q]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu_lt_255]
  have hsc : scalarIsInRange (toU8 (encPt255 Q)) = true := by
    rw [scalarIsInRange_encPt255_iff, hQ_toNat]; exact hu_lt_p
  have hlift : montLiftEd (⟨encPt255 Q, encPt255_length Q⟩ : List.Vector (BitVec 8) 32) 0#8 =
      some R0 := by
    refine (montLiftEd_eq_montToEdwards ⟨encPt255 Q, encPt255_length Q⟩ 0#8).trans ?_
    change montToEdwards (encPt255 Q) 0 = some R0
    rw [encPt255_eq_natToLeBytes, hQ_toNat, ← hR0_u, ← hR0_even]
    exact montToEdwards_edToMontU hR0_on hR0_ne
  refine ⟨R0, ?_, hR0_pm⟩
  unfold liftCanon255
  rw [if_true_eq hsc, hlift]
  dsimp only
  rw [if_true_eq hR0_tf]

private theorem five_mul_edOrderL_eq_eight_mul_add_one :
    5 * edOrderL = 8 * ((5 * edOrderL) / 8) + 1 := by
  unfold edOrderL; decide

theorem liftCanon255_zero : liftCanon255 0 = none := by
  cases h : liftCanon255 0 with
  | none => rfl
  | some P =>
    exfalso
    rcases liftCanon255_some_props h with ⟨_, hon, hne, hL, hu⟩
    have hu0 : edToMontU P = 0 := hu
    have h8s : edSmul 8 P = edZero :=
      (edSmul_eight_eq_edZero_iff hon).mpr (by rw [hu0]; simp)
    have h8 : edNatSmul 8 P = edZero := by
      rw [← edSmul_eq_edNatSmul (by decide) hon]; exact h8s
    have h5L : edNatSmul (5 * edOrderL) P = edZero := by
      rw [edNatSmul_mul 5 edOrderL hon, hL, edNatSmul_edZero]
    have h8k : edNatSmul (8 * ((5 * edOrderL) / 8)) P = edZero := by
      rw [Nat.mul_comm, edNatSmul_mul _ 8 hon, h8, edNatSmul_edZero]
    rw [five_mul_edOrderL_eq_eight_mul_add_one,
      edNatSmul_add _ 1 hon, h8k, edNatSmul_one hon, edZero_edAdd hon] at h5L
    exact hne h5L

theorem liftCanon255_base : liftCanon255 dh255.base = some edBasepoint := by
  have hsc : scalarIsInRange (toU8 (encPt255 dh255.base)) = true := by
    rw [scalarIsInRange_encPt255_iff]
    change 9 < p25519
    unfold p25519; decide
  have hu9 : decodeU255 (encPt255 dh255.base) % p25519 = 9 := by
    rw [encPt255_eq_natToLeBytes, decodeU255_natToLeBytes_of_lt (dh255.base).isLt]
    change 9 % p25519 = 9
    unfold p25519; decide
  have hlift : montLiftEd ⟨encPt255 dh255.base, encPt255_length _⟩ 0#8 = some edBasepoint :=
    montLiftEd_u9_even hu9 (by decide)
  have htf : (edSmul edOrderL edBasepoint == edZero) = true :=
    beq_iff_eq.mpr edSmul_edOrderL_edBasepoint
  unfold liftCanon255
  rw [if_true_eq hsc, hlift]
  dsimp only
  rw [if_true_eq htf]

/-! ## 3. `dh255` Group Laws, Injectivity, & Uniform Kernel -/

theorem dh255_of_liftCanon {k : BitVec 256} {Q : BitVec 255} {P : EdPoint}
    (h : liftCanon255 Q = some P) :
    dh255.dh k Q =
      BitVec.ofNat 255 (edToMontU (edNatSmul (clampedScalarZMod (word256ToBytes k)).val P)) := by
  rcases liftCanon255_some_props h with ⟨_, hon, _, _, _⟩
  unfold dh255
  dsimp only []
  rw [h]
  dsimp only []
  rw [edSmul_eq_edNatSmul (zmod_val_lt_two_pow_256 _) hon]

theorem liftCanon255_dh255_isSome (k : BitVec 256) (Q : BitVec 255) :
    (liftCanon255 (dh255.dh k Q)).isSome = (liftCanon255 Q).isSome := by
  cases h : liftCanon255 Q with
  | none =>
    have hdh : dh255.dh k Q = Q := by unfold dh255; dsimp only []; rw [h]
    rw [hdh, h]
  | some P =>
    rcases liftCanon255_some_props h with ⟨_, hon, hne, hL, _⟩
    set c := clampedScalarZMod (word256ToBytes k)
    have hc : c ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes k)
    have hR_on := edOnCurve_edNatSmul c.val hon
    have hR_ne := edNatSmul_ne_edZero_of_zmod_ne_zero hon hne hL hc
    have hR_L : edNatSmul edOrderL (edNatSmul c.val P) = edZero := by
      rw [← edNatSmul_mul edOrderL c.val hon, Nat.mul_comm,
        edNatSmul_mul c.val edOrderL hon, hL, edNatSmul_edZero]
    rcases liftCanon255_ofNat_edToMontU hR_on hR_ne hR_L with ⟨P', hP', _⟩
    rw [dh255_of_liftCanon h, hP']
    rfl

theorem dh255_zero (x : BitVec 256) : dh255.dh x 0 = 0 := by
  unfold dh255; dsimp only []; rw [liftCanon255_zero]

theorem dh255_ne_zero (k : BitVec 256) (Q : BitVec 255) (hQ : Q ≠ 0) :
    dh255.dh k Q ≠ 0 := by
  intro h0
  cases h : liftCanon255 Q with
  | none =>
    have hdh : dh255.dh k Q = Q := by unfold dh255; dsimp only []; rw [h]
    exact hQ (hdh.symm.trans h0)
  | some P =>
    have his := liftCanon255_dh255_isSome k Q
    rw [h0, liftCanon255_zero, h] at his
    exact Bool.noConfusion his

theorem dh255_of_liftCanon_none {k : BitVec 256} {Q : BitVec 255}
    (h : liftCanon255 Q = none) : dh255.dh k Q = Q := by
  unfold dh255; dsimp only []; rw [h]

private theorem edNatSmul_edNeg_of_lt {n : Nat} (hn : n < 2 ^ 256) {R : EdPoint}
    (hR : edOnCurve R = true) :
    edNatSmul n (edNeg R) = edNeg (edNatSmul n R) := by
  rw [← edSmul_eq_edNatSmul hn (edOnCurve_edNeg hR),
    edSmul_edNeg hn hR,
    edSmul_eq_edNatSmul hn hR]

section Dh255GroupLaws

attribute [local irreducible] dh255 liftCanon255 edToMontU edNatSmul clampedScalarZMod
  word256ToBytes edNeg

theorem dh255_dh_dh_of_liftCanon (a b : BitVec 256) {Q : BitVec 255} {P : EdPoint}
    (h : liftCanon255 Q = some P) :
    dh255.dh a (dh255.dh b Q) =
      BitVec.ofNat 255 (edToMontU (edNatSmul
        (clampedScalarZMod (word256ToBytes a) * clampedScalarZMod (word256ToBytes b)).val P)) := by
  rcases liftCanon255_some_props h with ⟨_, hon, hne, hL, _⟩
  have hcb : clampedScalarZMod (word256ToBytes b) ≠ 0 :=
    clampedScalarZMod_ne_zero (word256ToBytes b)
  have hR_on : edOnCurve (edNatSmul (clampedScalarZMod (word256ToBytes b)).val P) = true :=
    edOnCurve_edNatSmul _ hon
  have hR_ne : edNatSmul (clampedScalarZMod (word256ToBytes b)).val P ≠ edZero :=
    edNatSmul_ne_edZero_of_zmod_ne_zero hon hne hL hcb
  have hR_L : edNatSmul edOrderL (edNatSmul (clampedScalarZMod (word256ToBytes b)).val P) =
      edZero := by
    rw [← edNatSmul_mul edOrderL _ hon, Nat.mul_comm,
      edNatSmul_mul _ edOrderL hon, hL, edNatSmul_edZero]
  rcases liftCanon255_ofNat_edToMontU hR_on hR_ne hR_L with ⟨P', hP', hpm⟩
  rw [dh255_of_liftCanon (k := b) h, dh255_of_liftCanon (k := a) hP']
  apply congrArg (BitVec.ofNat 255)
  rcases hpm with h1 | h2
  · rw [h1, ← edNatSmul_zmod_mul hon hL]
  · rw [h2, edNatSmul_edNeg_of_lt (zmod_val_lt_two_pow_256 _) hR_on,
      edToMontU_edNeg (edOnCurve_edNatSmul _ hR_on), ← edNatSmul_zmod_mul hon hL]

theorem dh255_commutes : dh255.Commutes := by
  intro a b
  rw [dh255_dh_dh_of_liftCanon a b liftCanon255_base,
    dh255_dh_dh_of_liftCanon b a liftCanon255_base,
    mul_comm (clampedScalarZMod (word256ToBytes a)) (clampedScalarZMod (word256ToBytes b))]

theorem dh255_dh_inj (k : BitVec 256) : Function.Injective (dh255.dh k) := by
  intro Q1 Q2 heq
  have his : (liftCanon255 Q1).isSome = (liftCanon255 Q2).isSome := by
    rw [← liftCanon255_dh255_isSome k Q1, heq, liftCanon255_dh255_isSome k Q2]
  cases h1 : liftCanon255 Q1 with
  | none =>
    rw [h1] at his
    cases h2 : liftCanon255 Q2 with
    | none =>
      exact (dh255_of_liftCanon_none (k := k) h1).symm.trans
        (heq.trans (dh255_of_liftCanon_none (k := k) h2))
    | some _ => rw [h2] at his; cases his
  | some P1 =>
    rw [h1] at his
    cases h2 : liftCanon255 Q2 with
    | none => rw [h2] at his; cases his
    | some P2 =>
      rcases liftCanon255_some_props h1 with ⟨_, hon1, hne1, hL1, hu1⟩
      rcases liftCanon255_some_props h2 with ⟨_, hon2, hne2, hL2, hu2⟩
      set c := clampedScalarZMod (word256ToBytes k)
      have hc : c ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes k)
      rw [dh255_of_liftCanon h1, dh255_of_liftCanon h2] at heq
      have hu_eq : edToMontU (edNatSmul c.val P1) = edToMontU (edNatSmul c.val P2) :=
        bitVec255_ofNat_inj
          (lt_trans (edToMontU_lt (edNatSmul c.val P1)) p25519_lt_two_pow_255)
          (lt_trans (edToMontU_lt (edNatSmul c.val P2)) p25519_lt_two_pow_255)
          heq
      have hA_on := edOnCurve_edNatSmul c.val hon1
      have hB_on := edOnCurve_edNatSmul c.val hon2
      have hA_ne := edNatSmul_ne_edZero_of_zmod_ne_zero hon1 hne1 hL1 hc
      have hB_ne := edNatSmul_ne_edZero_of_zmod_ne_zero hon2 hne2 hL2 hc
      have hinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
      have hP1 : edNatSmul c⁻¹.val (edNatSmul c.val P1) = P1 := by
        rw [← edNatSmul_zmod_mul hon1 hL1 c⁻¹ c, hinv, ZMod.val_one, edNatSmul_one hon1]
      have hP2 : edNatSmul c⁻¹.val (edNatSmul c.val P2) = P2 := by
        rw [← edNatSmul_zmod_mul hon2 hL2 c⁻¹ c, hinv, ZMod.val_one, edNatSmul_one hon2]
      apply BitVec.eq_of_toNat_eq
      rw [← hu1, ← hu2]
      rcases edPoint_eq_or_edNeg_of_edToMontU_eq hA_on hB_on hA_ne hB_ne hu_eq with hp | hm
      · have hP_eq : P1 = P2 := by rw [← hP1, hp, hP2]
        rw [hP_eq]
      · have hneg : edNatSmul c⁻¹.val (edNeg (edNatSmul c.val P2)) = edNeg P2 := by
          rw [edNatSmul_edNeg_of_lt (zmod_val_lt_two_pow_256 c⁻¹) hB_on, hP2]
        have hP_eq : P1 = edNeg P2 := by rw [← hP1, hm, hneg]
        rw [hP_eq, edToMontU_edNeg hon2]

theorem dh255_kerUniform : DhKerUniform dh255 := by
  intro s x Q Q'
  rw [(dh255_dh_inj x).eq_iff, (dh255_dh_inj s).eq_iff]

end Dh255GroupLaws

/-! ## 4. `X25519RealizesDh` and `modelPrims` Field Characterizations -/

private theorem vecU8_vec32_of_length (bs : List (BitVec 8)) (h : bs.length = 32) :
    vecU8 (vec32 bs) = toU8 bs := by
  simp [vecU8, vec32, h]

private theorem word256ToBytes_clamp256 (k : BitVec 256) :
    word256ToBytes (clamp256 k) = clampScalar25519 (word256ToBytes k) := by
  have h1 : u8Vec 32 (word256ToBytes (clamp256 k)) =
      u8Vec 32 (clampScalar25519 (word256ToBytes k)) := by
    rw [u8Vec_word256ToBytes, ← clampScalar_keyVec,
        ← u8Vec_word256ToBytes, u8Vec_clampScalar25519]
  have h2 := congrArg vecU8 h1
  rwa [vecU8_u8Vec_of_length _ (length_word256ToBytes _),
       vecU8_u8Vec_of_length _ (clampScalar25519_length _)] at h2

theorem dh255_clamp (k : BitVec 256) (Q : BitVec 255) :
    dh255.dh (clamp256 k) Q = dh255.dh k Q := by
  unfold dh255
  dsimp only []
  rw [word256ToBytes_clamp256, clampedScalarZMod_clamp]

theorem libX25519Rel_c255 : X25519RealizesDh c255 dh255 encPt255 encT255 := by
  refine ⟨?_, fun _ => rfl⟩
  refine
    { enc_injective := encPt255_inj
      enc_length := encPt255_length
      enc_zero := encPt255_zero
      enc_base := encPt255_base
      base_ne_zero := by decide
      hook := fun k Q => ?_
      pubKey_hook := fun k => ?_
      dh_clamp := dh255_clamp
      dh_ne_zero := dh255_ne_zero }
  · dsimp only [c255]
    have hg : good255 (vecU8 (vec32 (encPt255 Q))) = true := by
      rw [vecU8_vec32_of_length _ (encPt255_length Q)]
      exact good255_toU8_encPt255 Q
    rw [if_true_eq hg, vec32_toList_of_length (encPt255_length _),
      vec32_toList_of_length (length_keyToBytes32 k),
      vec32_toList_of_length (encPt255_length Q), bytesToKey32_keyToBytes32]
    have hQ : (HKDF.bytesToKey32 (encPt255 Q)).truncate 255 = Q := by
      unfold encPt255
      rw [bytesToKey32_keyToBytes32, zeroExtend_truncate_255]
    rw [hQ]
  · dsimp only [c255]
    rw [vec32_toList_of_length (encPt255_length _),
      vec32_toList_of_length (length_keyToBytes32 k), bytesToKey32_keyToBytes32]

private def kOfBytes (a : List UInt8) : BitVec 256 :=
  HKDF.bytesToKey32 (ofU8 (clampScalar25519 a))

private theorem clampedScalarZMod_kOfBytes (a : List UInt8) :
    clampedScalarZMod (word256ToBytes (kOfBytes a)) = clampedScalarZMod a := by
  unfold kOfBytes
  rw [word256ToBytes_bytesToKey32_ofU8 _ (clampScalar25519_length a), clampedScalarZMod_clamp]

private theorem clampScalar_u8Vec_toList (a : List UInt8) :
    (Ratchet.clampScalar (u8Vec 32 a)).toList = ofU8 (clampScalar25519 a) := by
  rw [← u8Vec_clampScalar25519, u8Vec_toList_of_length (clampScalar25519_length a)]

private theorem modelPrims_X255_x25519Base (a : List UInt8) :
    (modelPrims X255 W255).x25519Base a = toU8 (encPt255 (dh255.dh (kOfBytes a) dh255.base)) := by
  dsimp only [modelPrims, blockLevelPrims, W255, c255]
  rw [clampScalar_u8Vec_toList, vecU8_vec32_of_length _ (encPt255_length _)]
  rfl

private theorem modelPrims_X255_x25519 (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X255 W255).x25519 a pk =
      if good255 pk then
        toU8 (encPt255 (dh255.dh (kOfBytes a) ((HKDF.bytesToKey32 (ofU8 pk)).truncate 255)))
      else
        List.replicate 32 0 := by
  dsimp only [modelPrims, blockLevelPrims, W255, c255]
  rw [clampScalar_u8Vec_toList, vecU8_u8Vec_of_length pk hpk, u8Vec_toList_of_length hpk]
  by_cases hg : good255 pk = true
  · rw [if_true_eq hg, if_true_eq hg, vecU8_vec32_of_length _ (encPt255_length _)]
    rfl
  · rw [if_false_eq hg, if_false_eq hg]
    exact vecU8_replicate_zero 32

private theorem w255_upd9_isCanonical (B1 : SignalPqxdh.Primitives)
    (sv h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    ({ B1 with
        sigVerify := sv
        isCanonical := SignalPqxdh.isCanonicalRef B1
        hkdfDerive96 := h96
        rootCreateChain := rcc
        chainKdfSeed := cks
        chainKdfNext := ckn
        deriveMsgKeys := dmk
        aeadEnc := ae
        aeadDec := ad } : SignalPqxdh.Primitives).isCanonical pk =
      SignalPqxdh.isCanonicalRef B1 pk := rfl

private theorem w255_upd1_isCanonicalRef (B : SignalPqxdh.Primitives) (s512) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s512 } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl

private theorem modelPrims_X255_isCanonical_eq (pk : List UInt8) :
    (modelPrims X255 W255).isCanonical pk =
      isCanonicalRef (blockLevelPrims X255 W255) pk :=
  (w255_upd9_isCanonical _ _ _ _ _ _ _ _ _ pk).trans (w255_upd1_isCanonicalRef _ _ pk)

private theorem w255_block_eq_upd :
    blockLevelPrims X255 W255 =
      { blockLevelPrims X255 W255 with isTorsionFree := fun P => edSmul edOrderL P == edZero } := rfl

private theorem w255_upd_isTorsionFree (B : SignalPqxdh.Primitives) (f : EdPoint → Bool) (P : EdPoint) :
    ({ B with isTorsionFree := f } : SignalPqxdh.Primitives).isTorsionFree P = f P := rfl

private theorem w255_block_isTorsionFree (P : EdPoint) :
    (blockLevelPrims X255 W255).isTorsionFree P = (edSmul edOrderL P == edZero) :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.isTorsionFree P) w255_block_eq_upd).trans
    (w255_upd_isTorsionFree _ _ P)

private theorem w255_block_montToEd_zero (pk : List UInt8) :
    (blockLevelPrims X255 W255).montToEd pk 0 = montLiftEd (u8Vec 32 pk) 0#8 := by
  change SignalPqxdh.montLiftEd (u8Vec 32 pk).toList (0 : UInt8).toBitVec = _
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl,
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge.signalMontLiftEd_eq]

private theorem w255_isCanonicalRef_of_some (B : SignalPqxdh.Primitives) (pk : List UInt8) (P : EdPoint)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = some P) :
    SignalPqxdh.isCanonicalRef B pk = B.isTorsionFree P := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, if_true_eq hg]
  split
  · rename_i Q hQ; exact congrArg B.isTorsionFree (Option.some.inj (hQ.symm.trans hm))
  · rename_i hQ; exact absurd (hQ.symm.trans hm) nofun

private theorem w255_isCanonicalRef_of_none (B : SignalPqxdh.Primitives) (pk : List UInt8)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = none) :
    SignalPqxdh.isCanonicalRef B pk = false := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, if_true_eq hg]
  split
  · rename_i Q hQ; exact absurd (hQ.symm.trans hm) nofun
  · rfl

private theorem modelPrims_X255_isCanonical_encPt255 (Q : BitVec 255) :
    (modelPrims X255 W255).isCanonical (toU8 (encPt255 Q)) = (liftCanon255 Q).isSome := by
  rw [modelPrims_X255_isCanonical_eq]
  have hg := good255_spec.mp (good255_toU8_encPt255 Q)
  have hu8 : u8Vec 32 (toU8 (encPt255 Q)) = ⟨encPt255 Q, encPt255_length Q⟩ := by
    apply List.Vector.eq
    change (u8Vec 32 (toU8 (encPt255 Q))).toList = encPt255 Q
    rw [u8Vec_toList_of_length hg.1, ofU8_toU8]
  unfold liftCanon255
  by_cases hsc : scalarIsInRange (toU8 (encPt255 Q)) = true
  · have hcond : ((toU8 (encPt255 Q)).length == 32 &&
        (((toU8 (encPt255 Q)).getD 31 0 &&& 0x80) == 0) &&
        scalarIsInRange (toU8 (encPt255 Q))) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨beq_iff_eq.mpr hg.1, beq_iff_eq.mpr hg.2⟩, hsc⟩
    rw [if_true_eq hsc]
    cases hml : montLiftEd ⟨encPt255 Q, encPt255_length Q⟩ 0#8 with
    | none =>
      have hm0 : (blockLevelPrims X255 W255).montToEd (toU8 (encPt255 Q)) 0 = none := by
        rw [w255_block_montToEd_zero, hu8]; exact hml
      rw [w255_isCanonicalRef_of_none _ _ hcond hm0]
      rfl
    | some P =>
      have hm0 : (blockLevelPrims X255 W255).montToEd (toU8 (encPt255 Q)) 0 = some P := by
        rw [w255_block_montToEd_zero, hu8]; exact hml
      rw [w255_isCanonicalRef_of_some _ _ P hcond hm0, w255_block_isTorsionFree]
      dsimp only
      cases (edSmul edOrderL P == edZero) <;> rfl
  · have hcond : ((toU8 (encPt255 Q)).length == 32 &&
        (((toU8 (encPt255 Q)).getD 31 0 &&& 0x80) == 0) &&
        scalarIsInRange (toU8 (encPt255 Q))) = false := by
      simp [Bool.eq_false_iff.mpr hsc]
    rw [SignalPqxdh.isCanonicalRef.eq_def, if_false_eq (by rw [hcond]; decide), if_false_eq hsc]
    rfl

private theorem modelPrims_X255_isCanonical_spec {pk : List UInt8}
    (hcan : (modelPrims X255 W255).isCanonical pk = true) :
    good255 pk = true ∧
      ∃ Q : BitVec 255, pk = toU8 (encPt255 Q) ∧ (liftCanon255 Q).isSome = true := by
  have hc0 : isCanonicalRef (blockLevelPrims X255 W255) pk = true := by
    rwa [← modelPrims_X255_isCanonical_eq]
  rw [isCanonicalRef_blockLevelPrims_eq] at hc0
  split at hc0
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    have hg : good255 pk = true := good255_spec.mpr ⟨hcond.1.1, hcond.1.2⟩
    let Q := (HKDF.bytesToKey32 (ofU8 pk)).truncate 255
    have hpk_eq : pk = toU8 (encPt255 Q) := (toU8_encPt255_truncate_of_good255 hg).symm
    refine ⟨hg, Q, hpk_eq, ?_⟩
    rw [← modelPrims_X255_isCanonical_encPt255, ← hpk_eq]
    exact hcan
  · cases hc0

/-! ## 5. Constant-Zero `sha512` & `sig_corr` -/

private theorem sha512Pad_length_ge_128 (msg : List UInt8) : 128 ≤ (sha512Pad msg).length := by
  unfold sha512Pad encodeBitLen128BE encodeBitLen64BE
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  set rem := (msg.length + 17) % 128
  have hrem_lt : rem < 128 := Nat.mod_lt _ (by decide)
  by_cases h0 : rem == 0
  · have hr0 : (msg.length + 17) % 128 = 0 := beq_iff_eq.mp h0
    simp only [h0, ↓reduceIte]
    omega
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    omega

private theorem foldl_const_aux {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β), l.foldl f z = z
  | [] => rfl
  | b :: rest => by simp only [List.foldl_cons, hf]; exact foldl_const_aux f z hf rest

private theorem foldl_const {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β) (init : α), l ≠ [] → l.foldl f init = z
  | [], _, hne => absurd rfl hne
  | b :: rest, init, _ => by
    simp only [List.foldl_cons, hf]
    exact foldl_const_aux f z hf rest

private theorem modelPrims_X255_sha512_zero (msg : List UInt8) :
    (modelPrims X255 W255).sha512 msg = List.replicate 64 0 := by
  rw [modelPrims_sha512_eq_ref]
  unfold sha512Ref chunkBlocks
  dsimp only []
  have hdiv : 1 ≤ (sha512Pad msg).length / 128 :=
    Nat.div_pos (sha512Pad_length_ge_128 msg) (by decide)
  have hne : ((List.range ((sha512Pad msg).length / 128)).map
      (fun i => ((sha512Pad msg).drop (i * 128)).take 128)) ≠ [] := by
    intro heq
    have hl := congrArg List.length heq
    simp at hl
    omega
  have hstep : ∀ s b, sha512Step (modelPrims X255 W255) s b = List.replicate 64 0 := by
    intro s b
    unfold sha512Step
    dsimp only [modelPrims, blockLevelPrims, W255, Q255]
    decide
  rw [foldl_const _ (List.replicate 64 0) hstep _ _ hne]
  decide

theorem modelPrims_X255_sig_corr (sk msg r : List UInt8) :
    (modelPrims X255 W255).sigVerify (X255.sigPkGen sk) msg (X255.sigSign sk msg r) = true := by
  let Q := dh255.dh (kOfBytes sk) dh255.base
  have hpk : X255.sigPkGen sk = toU8 (encPt255 Q) := modelPrims_X255_x25519Base sk
  have his : (liftCanon255 Q).isSome = true := by
    rw [liftCanon255_dh255_isSome, liftCanon255_base]; rfl
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp his
  have hmont : montLiftEd ⟨encPt255 Q, encPt255_length Q⟩ 0#8 = some P := by
    unfold liftCanon255 at hP
    by_cases hsc : scalarIsInRange (toU8 (encPt255 Q)) = true
    · rw [if_true_eq hsc] at hP
      cases hm : montLiftEd ⟨encPt255 Q, encPt255_length Q⟩ 0#8 with
      | none => rw [hm] at hP; cases hP
      | some P' =>
        rw [hm] at hP
        dsimp only at hP
        by_cases htf : (edSmul edOrderL P' == edZero) = true
        · rw [if_true_eq htf] at hP; cases hP; rfl
        · rw [if_false_eq htf] at hP; cases hP
    · rw [if_false_eq hsc] at hP; cases hP
  have hApt_on : edOnCurve P = true := montLiftEd_some_onCurve hmont
  have hlen_pk : (X255.sigPkGen sk).length = 32 := by rw [hpk, toU8_length, encPt255_length]
  have hu8 : u8Vec 32 (X255.sigPkGen sk) = ⟨encPt255 Q, encPt255_length Q⟩ := by
    apply List.Vector.eq
    change (u8Vec 32 (X255.sigPkGen sk)).toList = encPt255 Q
    rw [hpk, u8Vec_toList_of_length (by rw [toU8_length, encPt255_length]), ofU8_toU8]
  have hsig : X255.sigSign sk msg r = sigZeroEd64 := rfl
  rw [modelPrims_sigVerify_eq_ref, hsig]
  have hxeq := xeddsaVerifyRef_blockLevelPrims_eq X255 W255
    (modelPrims X255 W255).sha512 (X255.sigPkGen sk) msg sigZeroEd64
  change xeddsaVerifyRef ({ blockLevelPrims X255 W255 with sha512 := (modelPrims X255 W255).sha512 })
    (X255.sigPkGen sk) msg sigZeroEd64 = true
  rw [hxeq]
  have hcond : ((X255.sigPkGen sk).length == 32 &&
      sigZeroEd64.length == 64 &&
      ((sigZeroEd64.getD 63 0 &&& 0x60) == 0)) = true := by
    rw [hlen_pk]; decide
  rw [if_true_eq hcond]
  dsimp only
  have hs0 : ((sigZeroEd64.getD 63 0 &&& 0x80) >>> 7).toBitVec = 0#8 := by decide
  rw [hs0, hu8, hmont]
  dsimp only
  rw [modelPrims_X255_sha512_zero]
  have hh0 : leBytesToNat (u8Vec 64 (List.replicate 64 (0 : UInt8))).toList % edOrderL = 0 := by
    decide
  have hsNat0 : leBytesToNat (u8Vec 32
      ((sigZeroEd64.drop 32).take 31 ++ [(sigZeroEd64.drop 32).getD 31 0 &&& 0x7F])).toList %
      edOrderL = 0 := by decide
  rw [hh0, hsNat0,
    edSmul_eq_edNatSmul (by decide) edOnCurve_edBasepoint,
    edSmul_eq_edNatSmul (by decide) hApt_on]
  change (toU8 (encodeEd (edSub edZero edZero)) == sigZeroEd64.take 32) = true
  have hsub0 : edSub edZero edZero = edZero := by
    change edAdd edZero (edNeg edZero) = edZero
    rw [edNeg_edZero, edAdd_edZero edOnCurve_edZero]
  rw [hsub0]
  decide

/-! ## 6. Point-Fiber Cardinality (`≤ 64`) & `ModelPrimsCryptoAssumptions` -/

theorem dh255_base_fiber_card (Qt : BitVec 255) :
    (Finset.univ.filter (fun w : BitVec 256 => dh255.dh w dh255.base = Qt)).card ≤ 64 := by
  set S := Finset.univ.filter (fun w : BitVec 256 => dh255.dh w dh255.base = Qt)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : dh255.dh w0 dh255.base = Qt := (Finset.mem_filter.mp hw0).2
    set c0 := clampedScalarZMod (word256ToBytes w0)
    have hc0_ne : c0 ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes w0)
    have hc0_ne_neg : c0 ≠ -c0 := by
      intro h2c0
      have hs := edSignZMod_neg c0 hc0_ne
      rw [← h2c0] at hs
      rcases edSignZMod_bool c0 with hb | hb <;> rw [hb] at hs <;>
        exact (by revert hs; decide)
    have hb_L : edNatSmul edOrderL edBasepoint = edZero := by
      rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint]
      exact edSmul_edOrderL_edBasepoint
    let tag : BitVec 256 → Bool × Fin 8 × Fin 4 := fun w =>
      (@decide (clampedScalarZMod (word256ToBytes w) = c0) (Classical.propDecidable _),
       ⟨w.toNat % 8, Nat.mod_lt _ (by decide)⟩,
       ⟨w.toNat / 2 ^ 254, Nat.div_lt_of_lt_mul (by have := w.isLt; omega)⟩)
    have hinj : Set.InjOn tag (S : Set (BitVec 256)) := by
      intro w1 hw1 w2 hw2 htag
      have hw1_eq : dh255.dh w1 dh255.base = Qt :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
      have hw2_eq : dh255.dh w2 dh255.base = Qt :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
      have hu_pm : ∀ w, dh255.dh w dh255.base = Qt →
          clampedScalarZMod (word256ToBytes w) = c0 ∨
          clampedScalarZMod (word256ToBytes w) = -c0 := by
        intro w hw
        have hdh_eq := hw.trans hw0_eq.symm
        rw [dh255_of_liftCanon liftCanon255_base, dh255_of_liftCanon liftCanon255_base] at hdh_eq
        have hu_eq : edToMontU (edNatSmul (clampedScalarZMod (word256ToBytes w)).val edBasepoint) =
            edToMontU (edNatSmul c0.val edBasepoint) :=
          bitVec255_ofNat_inj
            (lt_trans
              (edToMontU_lt (edNatSmul (clampedScalarZMod (word256ToBytes w)).val edBasepoint))
              p25519_lt_two_pow_255)
            (lt_trans (edToMontU_lt (edNatSmul c0.val edBasepoint)) p25519_lt_two_pow_255)
            hdh_eq
        exact (edToMontU_edNatSmul_eq_iff edOnCurve_edBasepoint edBasepoint_ne_edZero hb_L
          (clampedScalarZMod_ne_zero (word256ToBytes w)) hc0_ne).mp hu_eq
      have hpm1 := hu_pm w1 hw1_eq
      have hpm2 := hu_pm w2 hw2_eq
      have htag_iff : (clampedScalarZMod (word256ToBytes w1) = c0) ↔
          (clampedScalarZMod (word256ToBytes w2) = c0) :=
        @decide_eq_decide _ _ (Classical.propDecidable _) (Classical.propDecidable _) |>.mp
          (congrArg Prod.fst htag)
      have hlo : w1.toNat % 8 = w2.toNat % 8 := congrArg (fun p => p.2.1.val) htag
      have hhi : w1.toNat / 2 ^ 254 = w2.toNat / 2 ^ 254 := congrArg (fun p => p.2.2.val) htag
      have hc_eq :
          clampedScalarZMod (word256ToBytes w1) = clampedScalarZMod (word256ToBytes w2) := by
        rcases hpm1 with hc1 | hc1 <;> rcases hpm2 with hc2 | hc2
        · exact hc1.trans hc2.symm
        · exfalso; exact hc0_ne_neg (hc2.symm.trans (htag_iff.mp hc1)).symm
        · exfalso; exact hc0_ne_neg (hc1.symm.trans (htag_iff.mpr hc2)).symm
        · exact hc1.trans hc2.symm
      have hcl_eq := clampScalar25519_eq_of_clampedScalarZMod_eq hc_eq
      have hcwf : cwfC (word256ToBytes w1) = cwfC (word256ToBytes w2) := by
        rw [← cwfC_clamp (word256ToBytes w1), ← cwfC_clamp (word256ToBytes w2), hcl_eq]
      exact cwfC_word_eq w1 w2 hcwf hlo hhi
    have hcard_le : S.card ≤ Fintype.card (Bool × Fin 8 × Fin 4) :=
      Finset.card_le_card_of_injOn tag (fun _ _ => Finset.mem_univ _) hinj
    have hcard64 : Fintype.card (Bool × Fin 8 × Fin 4) = 64 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact hcard_le.trans_eq hcard64
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le 64

private theorem dh255_kOfBytes_word256ToBytes (w : BitVec 256) (Q : BitVec 255) :
    dh255.dh (kOfBytes (word256ToBytes w)) Q = dh255.dh w Q := by
  unfold dh255
  dsimp only []
  rw [clampedScalarZMod_kOfBytes]

private theorem modelPrims_X255_ec_coll_bound (targetPk : List UInt8) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (X255.pow8 ((modelPrims X255 W255).x25519Base sk) ==
          X255.pow8 targetPk)] {true}).toReal
        ≤ 1 / (2 : ℝ) ^ 250 := by
  have hp8_good : good255 (X255.pow8 targetPk) = true := by
    change good255 (if good255 targetPk then targetPk else List.replicate 32 0) = true
    by_cases hg : good255 targetPk = true
    · rw [if_true_eq hg]; exact hg
    · rw [if_false_eq hg]; exact good255_replicate_zero
  let Qt : BitVec 255 := (HKDF.bytesToKey32 (ofU8 (X255.pow8 targetPk))).truncate 255
  have hQt : X255.pow8 targetPk = toU8 (encPt255 Qt) :=
    (toU8_encPt255_truncate_of_good255 hp8_good).symm
  have hc : ∀ sk, X255.pow8 ((modelPrims X255 W255).x25519Base sk) =
      toU8 (encPt255 (dh255.dh (kOfBytes sk) dh255.base)) := fun sk => by
    rw [modelPrims_X255_x25519Base]
    change (if good255 (toU8 (encPt255 _)) then _ else _) = _
    rw [if_true_eq (good255_toU8_encPt255 _)]
  let f : BitVec 256 → Bool := fun w =>
    toU8 (encPt255 (dh255.dh (kOfBytes (word256ToBytes w)) dh255.base)) == X255.pow8 targetPk
  have hexpr :
      (do
        let sk ← sampleScalar32
        pure (X255.pow8 ((modelPrims X255 W255).x25519Base sk) ==
          X255.pow8 targetPk)) =
      (f <$> ($ᵗ BitVec 256)) := by
    simp only [hc, sampleScalar32, sampleBytes32, bind_pure_comp, Functor.map_map]
    rfl
  rw [hexpr]
  refine le_trans (uniform256_map_bool_le f 64 ?_) (by norm_num)
  refine le_trans (Finset.card_le_card ?_) (dh255_base_fiber_card Qt)
  intro w hw
  have hb : f w = true := (Finset.mem_filter.mp hw).2
  dsimp only [f] at hb
  rw [dh255_kOfBytes_word256ToBytes, hQt] at hb
  have henc : encPt255 (dh255.dh w dh255.base) = encPt255 Qt := by
    have h1 := congrArg ofU8 (beq_iff_eq.mp hb)
    rwa [ofU8_toU8, ofU8_toU8] at h1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, encPt255_inj henc⟩

private theorem toU8_encPt255_zero : toU8 (encPt255 0) = List.replicate 32 0 := by decide

private theorem toU8_encPt255_eq_zero_iff (Q : BitVec 255) :
    toU8 (encPt255 Q) = List.replicate 32 0 ↔ Q = 0 := by
  constructor
  · intro h
    apply encPt255_inj
    rw [← ofU8_toU8 (encPt255 Q), h, encPt255_zero]
    decide
  · rintro rfl
    exact toU8_encPt255_zero

private theorem truncate_zero :
    ((HKDF.bytesToKey32 (ofU8 (List.replicate 32 (0 : UInt8)))).truncate 255) = 0 := by
  decide

theorem modelPrims_X255_cryptoAssumptions : ModelPrimsCryptoAssumptions X255 W255 where
  x25519_zero_iff := fun a1 a2 pk _ _ hpk => by
    rw [modelPrims_X255_x25519 a1 pk hpk, modelPrims_X255_x25519 a2 pk hpk]
    by_cases hg : good255 pk = true
    · rw [if_true_eq hg, if_true_eq hg, toU8_encPt255_eq_zero_iff, toU8_encPt255_eq_zero_iff]
      set Q := (HKDF.bytesToKey32 (ofU8 pk)).truncate 255
      constructor <;> intro h0
      · by_cases hQ : Q = 0
        · rw [hQ]; exact dh255_zero _
        · exact absurd h0 (dh255_ne_zero _ Q hQ)
      · by_cases hQ : Q = 0
        · rw [hQ]; exact dh255_zero _
        · exact absurd h0 (dh255_ne_zero _ Q hQ)
    · simp [hg]
  canon_base := fun e _ => by
    rw [modelPrims_X255_x25519Base, modelPrims_X255_isCanonical_encPt255,
      liftCanon255_dh255_isSome, liftCanon255_base]
    rfl
  canon_x25519 := fun a pk _ hcan => by
    obtain ⟨hg, Q, hpk_eq, his⟩ := modelPrims_X255_isCanonical_spec hcan
    have hpk : pk.length = 32 := (good255_spec.mp hg).1
    rw [modelPrims_X255_x25519 a pk hpk, if_true_eq hg,
      modelPrims_X255_isCanonical_encPt255, liftCanon255_dh255_isSome]
    have hQ : (HKDF.bytesToKey32 (ofU8 pk)).truncate 255 = Q := by
      rw [hpk_eq, ofU8_toU8, encPt255, bytesToKey32_keyToBytes32, zeroExtend_truncate_255]
    rwa [hQ]
  pow8_idemp := fun p => by
    change X255_pre.pow8 (X255_pre.pow8 p) = X255_pre.pow8 p
    dsimp only [X255_pre]
    by_cases hg : good255 p = true
    · rw [if_true_eq hg, if_true_eq hg]
    · rw [if_false_eq hg, if_true_eq good255_replicate_zero]
  isValidDhTriple_eq_ref := fun A B Z => by
    dsimp only [X255]
    exact isValidDhTripleModelB_eq_ref X255_pre W255 A B Z
  x25519_pow8_congr := fun a pk1 pk2 _ h1 h2 hpow => by
    rw [modelPrims_X255_x25519 a pk1 h1, modelPrims_X255_x25519 a pk2 h2]
    change (if good255 pk1 then pk1 else List.replicate 32 0) =
      (if good255 pk2 then pk2 else List.replicate 32 0) at hpow
    by_cases hg1 : good255 pk1 = true <;> by_cases hg2 : good255 pk2 = true
    · simp only [hg1, hg2, ↓reduceIte] at hpow ⊢
      rw [hpow]
    · simp only [hg1, hg2, Bool.false_eq_true, ↓reduceIte] at hpow ⊢
      rw [hpow, truncate_zero, dh255_zero, toU8_encPt255_zero]
    · simp only [hg1, hg2, Bool.false_eq_true, ↓reduceIte] at hpow ⊢
      rw [← hpow, truncate_zero, dh255_zero, toU8_encPt255_zero]
    · simp [hg1, hg2]
  x25519_congr_of_base_eq := fun a1 a2 pk _ _ hcan hbase => by
    obtain ⟨hg, Q, hpk_eq, his⟩ := modelPrims_X255_isCanonical_spec hcan
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp his
    rcases liftCanon255_some_props hP with ⟨_, honP, hneP, hLP, _⟩
    have hpk : pk.length = 32 := (good255_spec.mp hg).1
    have hQ : (HKDF.bytesToKey32 (ofU8 pk)).truncate 255 = Q := by
      rw [hpk_eq, ofU8_toU8, encPt255, bytesToKey32_keyToBytes32, zeroExtend_truncate_255]
    rw [modelPrims_X255_x25519Base, modelPrims_X255_x25519Base] at hbase
    have hdh_base : dh255.dh (kOfBytes a1) dh255.base = dh255.dh (kOfBytes a2) dh255.base := by
      apply encPt255_inj
      have h1 := congrArg ofU8 hbase
      rwa [ofU8_toU8, ofU8_toU8] at h1
    rw [dh255_of_liftCanon liftCanon255_base, dh255_of_liftCanon liftCanon255_base,
      clampedScalarZMod_kOfBytes, clampedScalarZMod_kOfBytes] at hdh_base
    have hu_base : edToMontU (edNatSmul (clampedScalarZMod a1).val edBasepoint) =
        edToMontU (edNatSmul (clampedScalarZMod a2).val edBasepoint) :=
      bitVec255_ofNat_inj
        (lt_trans (edToMontU_lt (edNatSmul (clampedScalarZMod a1).val edBasepoint))
          p25519_lt_two_pow_255)
        (lt_trans (edToMontU_lt (edNatSmul (clampedScalarZMod a2).val edBasepoint))
          p25519_lt_two_pow_255)
        hdh_base
    have hb_L : edNatSmul edOrderL edBasepoint = edZero := by
      rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint]
      exact edSmul_edOrderL_edBasepoint
    have hpm := (edToMontU_edNatSmul_eq_iff edOnCurve_edBasepoint edBasepoint_ne_edZero hb_L
      (clampedScalarZMod_ne_zero a1) (clampedScalarZMod_ne_zero a2)).mp hu_base
    have hu_P : edToMontU (edNatSmul (clampedScalarZMod a1).val P) =
        edToMontU (edNatSmul (clampedScalarZMod a2).val P) :=
      (edToMontU_edNatSmul_eq_iff honP hneP hLP
        (clampedScalarZMod_ne_zero a1) (clampedScalarZMod_ne_zero a2)).mpr hpm
    rw [modelPrims_X255_x25519 a1 pk hpk, modelPrims_X255_x25519 a2 pk hpk,
      if_true_eq hg, if_true_eq hg, hQ,
      dh255_of_liftCanon hP, dh255_of_liftCanon hP,
      clampedScalarZMod_kOfBytes, clampedScalarZMod_kOfBytes, hu_P]
  canon_pow8_inj := fun pk1 pk2 h1 h2 hpow => by
    have hg1 := (modelPrims_X255_isCanonical_spec h1).1
    have hg2 := (modelPrims_X255_isCanonical_spec h2).1
    change (if good255 pk1 then pk1 else List.replicate 32 0) =
      (if good255 pk2 then pk2 else List.replicate 32 0) at hpow
    rwa [if_true_eq hg1, if_true_eq hg2] at hpow
  pow8_len := fun p => by
    change (if good255 p then p else List.replicate 32 0).length = 32
    by_cases hg : good255 p = true
    · rw [if_true_eq hg]; exact (good255_spec.mp hg).1
    · rw [if_false_eq hg]; simp
  ec_coll_bound := modelPrims_X255_ec_coll_bound
  x25519_inj_pow8 := fun a pk1 pk2 _ h1 h2 hx => by
    rw [modelPrims_X255_x25519 a pk1 h1, modelPrims_X255_x25519 a pk2 h2] at hx
    change (if good255 pk1 then pk1 else List.replicate 32 0) =
      (if good255 pk2 then pk2 else List.replicate 32 0)
    by_cases hg1 : good255 pk1 = true <;> by_cases hg2 : good255 pk2 = true
    · simp only [hg1, hg2, ↓reduceIte] at hx ⊢
      have henc : encPt255 (dh255.dh (kOfBytes a) ((HKDF.bytesToKey32 (ofU8 pk1)).truncate 255)) =
          encPt255 (dh255.dh (kOfBytes a) ((HKDF.bytesToKey32 (ofU8 pk2)).truncate 255)) := by
        have ht := congrArg ofU8 hx
        rwa [ofU8_toU8, ofU8_toU8] at ht
      have hQ := dh255_dh_inj (kOfBytes a) (encPt255_inj henc)
      rw [← toU8_encPt255_truncate_of_good255 hg1, hQ, toU8_encPt255_truncate_of_good255 hg2]
    · simp only [hg1, hg2, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      have hdh0 := (toU8_encPt255_eq_zero_iff _).mp hx
      have hQ0 : (HKDF.bytesToKey32 (ofU8 pk1)).truncate 255 = 0 := by
        by_contra hne
        exact dh255_ne_zero (kOfBytes a) _ hne hdh0
      rw [← toU8_encPt255_truncate_of_good255 hg1, hQ0, toU8_encPt255_zero]
    · simp only [hg1, hg2, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      have hdh0 := (toU8_encPt255_eq_zero_iff _).mp hx.symm
      have hQ0 : (HKDF.bytesToKey32 (ofU8 pk2)).truncate 255 = 0 := by
        by_contra hne
        exact dh255_ne_zero (kOfBytes a) _ hne hdh0
      rw [← toU8_encPt255_truncate_of_good255 hg2, hQ0, toU8_encPt255_zero]
    · simp [hg1, hg2]
  pow8_base_len := fun p e _ hpow => by
    rw [modelPrims_X255_x25519Base] at hpow
    change (if good255 p then p else List.replicate 32 0) =
      (if good255 (toU8 (encPt255 _)) then _ else _) at hpow
    rw [if_true_eq (good255_toU8_encPt255 _)] at hpow
    by_cases hg : good255 p = true
    · exact (good255_spec.mp hg).1
    · rw [if_false_eq hg] at hpow
      exfalso
      exact dh255_ne_zero (kOfBytes e) dh255.base (by decide)
        ((toU8_encPt255_eq_zero_iff _).mp hpow.symm)
  sigPkGen_eq_x25519Base := rfl
  scalarMul_len := fun _ _ => by simp [X255, X255_pre]
  scalarAdd_len := fun _ _ => by simp [X255, X255_pre]
  kemKeyGen_len := fun seed => ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  sig_corr := modelPrims_X255_sig_corr
  kem_coll_bound := cwfPrimitives_kem_coll_bound

/-- info: 'CryptoVerification.E2E.modelPrims_X255_cryptoAssumptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modelPrims_X255_cryptoAssumptions

end CryptoVerification.E2E
