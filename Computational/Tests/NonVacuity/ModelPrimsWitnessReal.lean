/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.Kyber1024Delta
public import Computational.Specifications.LibsignalCli.StatementPqElfAnyKem
public import Computational.Tests.NonVacuity.PrimeOrderX25519Satisfiable
public import Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
public import Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.SignalPqxdh.CwfPrimitives
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import Computational.Tests.NonVacuity.KeyInd1KeyRoNonVac
import Computational.Theorems.Lemmas
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
import LibsignalBinary.Proofs.SignalSession.PqModelRun
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Real-Primitive Non-Vacuity Witness (`ModelPrimsWitnessReal`)

**Checked by Lean.**

Constructs a standalone untrusted primitive witness `(Pt25519, dhReal, cReal, QReal, WReal, XReal)`
pinned to the concrete reference primitives:
- `WReal.C.X = x25519Ref` (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref`)
- `WReal.C.pubKey = x25519PubFromSecretRef`
- `WReal.Q.F512 = sha512CompressState` (`LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref`)
- `XReal.pow8 = pow8Real` (CryptoVerif `gexp_div_8`, `Model.lean:151`: cofactor-clearing prime-order
  projection `[3 * edOrderL + 1]` on $E(\mathbb{F}_p)$ and `[3 * twistOrderL + 1]` on
  $E_{\text{twist}}(\mathbb{F}_p)$, alongside `not_pow8_idemp_ladder8` showing why raw `[8]P`
  fails `pow8_idemp`)
- `XReal.sigSign = xeddsaSignRef (modelPrims XReal WReal)` (honest XEdDSA over real SHA-512 and
  Curve25519/Ed25519 arithmetic)

Proves `X25519RealizesDh cReal dhReal encPtReal encTReal`, `XeddsaCurveWitness (modelPrims XReal WReal)`,
`ModelPrimsCryptoAssumptions XReal WReal`, `CryptoWellFormedPrimitivesδ (modelPrims XReal WReal)`,
and joint hypothesis satisfiability and conclusion instantiation for `SessionSecure`,
`LibsignalCliPqSecure`, and `CliSpecPqxdhOrExcusedAbort`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA SM
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SignalSession CryptoGames.LibsignalSM.Proofs.Correctness
open _root_.SignalPqxdh (
  fitBytes fitBytesRef word256ToBytes clampScalar25519
  clampScalar25519_length sampleScalar32 sampleBytes32 scalarIsInRange isCanonicalRef
  xeddsaVerifyRef isValidDhTripleRef
)
open SpecTests.SignalPqxdh
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 two_pow_252_lt_l25519 natOfBytesLE bytesOfNatLE bytesOfNatLE_length
  natOfBytesLE_bytesOfNatLE bytesOfNatLE_natOfBytesLE getD_toNat_eq_div_mod
  encodeScalarBytes decodeScalarBytes encodeScalarBytes_length natOfBytesLE_encodeScalarBytes
  clearSignBit32 clampedScalarZMod clampedScalarZMod_clamp clampedScalarZMod_ne_zero
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  xeddsaSignRef XeddsaCurveWitness XeddsaCurveLaws
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip (xeddsaSignRef_correct)
open Computational.Tests.XeddsaRomNonVac (
  halfL25519 halfL25519_lt_two_pow_252 absZMod absZMod_le_half absZMod_eq_zero_iff
  absZMod_neg absZMod_eq_iff edSignZMod_bool edSignZMod_neg
  clampScalar25519_eq_of_clampedScalarZMod_eq list32_take31_append_getD31
)
open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpNeg fpMul fpInv recoverXEven leBytesToNat natToLeBytes
  EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul encodeEd decodeEdRfc
  clampScalarBytes clampScalar
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  x25519Ladder x25519 x25519Basepoint x25519Pubkey x25519Ref x25519PubFromSecretRef
  isCanonicalX25519 lowOrderUs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Ladder_mod x25519Ladder_zero x25519Ladder_edToMontU x25519Ladder_twToMontU
  clampScalar_eight_mul clampScalar_lt_two_pow_255 x25519Pubkey_eq_edNatSmul
  x25519_eq_zero_iff_lowOrder x25519Pubkey_not_lowOrder isCanonicalX25519_x25519
  edToMontU_edSmul_edBasepoint_eq_iff
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpMul_lt fpNeg_mod_two_of_ne_zero
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg
  edOnCurve_edAdd edAdd_edZero edZero_edAdd edAdd_edNeg_self edNeg_edZero edNeg_edNeg edAdd_assoc
  edNatSmul edOnCurve_edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_add edNatSmul_mul
  edSmul_eq_edNatSmul edOrderL_lt_two_pow_256
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_cons leBytesToNat_lt leBytesToNat_natToLeBytes_of_lt edOrderL_pos
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  twistOrderL edOrderL_odd twistOrderL_odd two_pow_252_lt_edOrderL two_pow_252_lt_twistOrderL
  edOrderL_prime twistOrderL_prime gcd_sixteen_mul_odd_prime
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  montRHS edToMontU edToMontU_lt edToMontU_edBasepoint
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero montToEdwards_some_edToMontU
  decodeU255_natToLeBytes_edToMontU montToEdwards_edToMontU
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  FpIsSquare twOnCurve twAdd twZero twNeg twNatSmul twOnCurve_x_lt twOnCurve_twZero
  twOnCurve_twNeg twOnCurve_twAdd twAdd_comm twAdd_twZero twZero_twAdd twAdd_twNeg_self
  twAdd_assoc twOnCurve_twNatSmul twNatSmul_twZero twNatSmul_add twNatSmul_mul
  twToMontU twToMontU_lt edToMontU_eq_zero_iff twToMontU_eq_zero_iff
  edOnCurve_montRHS_isSquare twOnCurve_montRHS_not_isSquare mont_lift_dichotomy
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  twToMontU_twNeg twOnCurve_eq_of_twToMontU_eq edNatSmul_gcd_eq_zero twNatSmul_gcd_eq_zero
  edNatSmul_eight_mul_edOrderL twNatSmul_four_mul_twistOrderL
  edNatSmul_two_eq_zero_iff twNatSmul_two_eq_zero_iff
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  montLiftEd signalMontLiftEd_eq natToLeBytes_len u8Vec_toList_of_length
  montLiftEd_eq_montToEdwards isCanonicalRef_blockLevelPrims_eq
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge (
  natToLeBytes_succ montLiftEd_congr_decodeU255_mod_p montLiftEd_odd_eq_edNeg_of_even
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (edBasepoint_ne_edZero)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  encodeEd_length decodeEdRfc_encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)

/-! ## 1. Witness Definitions (`cReal`, `QReal`, `WReal`, `pow8Real`, `XReal`) -/

/-- Session `Crypto` witness pinned to `X = x25519Ref` and `pubKey = x25519PubFromSecretRef`. -/
@[expose] def cReal : Crypto where
  F := fun st _ => st
  E := fun _ b => b
  D := fun _ b => b
  X := x25519Ref
  pubKey := x25519PubFromSecretRef

/-- `PqxdhPrims` witness pinned to `F512 = sha512CompressState` and total `K255`. -/
@[expose] def QReal : PqxdhPrims where
  F512 := sha512CompressState
  encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps := fun _ _ => List.Vector.replicate 32 0#8
  K := K255

/-- End-to-end parameter bundle `(cReal, QReal)`. -/
@[expose] def WReal : PEParams := ⟨cReal, QReal⟩

theorem wReal_X : WReal.C.X = x25519Ref := rfl
theorem wReal_pubKey : WReal.C.pubKey = x25519PubFromSecretRef := rfl
theorem wReal_F512 : WReal.Q.F512 = sha512CompressState := rfl

/-- Cofactor-clearing idempotent exponent on $E(\mathbb{F}_p)$ (`gexp_div_8 = 8 * (8⁻¹ mod ℓ)`):
`3 * edOrderL + 1 ≡ 0 (mod 8)` and `≡ 1 (mod edOrderL)`. -/
@[expose] def eEd : Nat := 3 * edOrderL + 1

/-- Cofactor-clearing idempotent exponent on $E_{\text{twist}}(\mathbb{F}_p)$:
`3 * twistOrderL + 1 ≡ 0 (mod 4)` and `≡ 1 (mod twistOrderL)`. -/
@[expose] def eTw : Nat := 3 * twistOrderL + 1

/-- Raw 3-doubling ladder `[8]P` (`x25519Ladder 8`), shown in `not_pow8_idemp_ladder8` not to be
idempotent (`[64]B ≠ [8]B`). -/
@[expose] def pow8Ladder8 (pk : List UInt8) : List UInt8 :=
  if pk.length == 32 then
    let bs := ofU8 pk
    toU8 (natToLeBytes 32 (x25519Ladder 8 (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs)))
  else
    List.replicate 32 0

/-- CryptoVerif cofactor-clearing subgroup projection `gexp_div_8` (`Model.lean:151`): evaluates
`x25519Ladder eEd` on $E(\mathbb{F}_p)$ coordinates and `x25519Ladder eTw` on
$E_{\text{twist}}(\mathbb{F}_p)$ coordinates, mapping non-32-byte inputs to `0^32`. -/
@[expose] def pow8Real (pk : List UInt8) : List UInt8 :=
  if pk.length == 32 then
    let bs := ofU8 pk
    let exp :=
      match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
      | some _ => eEd
      | none => eTw
    toU8 (natToLeBytes 32
      (x25519Ladder exp (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs)))
  else
    List.replicate 32 0

/-- Base `UnreachedPqxdhPrimitives` witness with real `ZMod l25519` scalar addition/multiplication
and `pow8 = pow8Real`. -/
@[expose] def XReal_pre : UnreachedPqxdhPrimitives where
  sigPkGen := fun a => vecU8 (cReal.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
  sigSign := fun _ _ _ => []
  scalarMul := fun a b =>
    encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 a) * decodeScalarBytes (fitBytesRef 32 b))
  scalarAdd := fun a b =>
    encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 a) + decodeScalarBytes (fitBytesRef 32 b))
  kemKeyGen := fun seed => (fitBytes 1568 (seed.take 32), fitBytes 3168 seed)
  pow8 := pow8Real
  isValidDhTriple := fun _ _ _ => false

/-- Full `UnreachedPqxdhPrimitives` witness equipping `XReal_pre` with honest `xeddsaSignRef`
signing and the constructive `256 ^ 32`-scalar decision procedure `isValidDhTripleModelB`
(computable, though infeasible to evaluate exhaustively in practice). -/
def XReal : UnreachedPqxdhPrimitives :=
  { XReal_pre with
    sigSign := xeddsaSignRef (modelPrims XReal_pre WReal)
    isValidDhTriple := isValidDhTripleModelB XReal_pre WReal }

private theorem wr_upd9_isCanonical (B1 : SignalPqxdh.Primitives)
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

private theorem wr_upd1_isCanonicalRef (B : SignalPqxdh.Primitives) (s512) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s512 } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl

private theorem wr_modelPrims_isCanonical_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk : List UInt8) :
    (modelPrims X W).isCanonical pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims X W) pk :=
  (wr_upd9_isCanonical _ _ _ _ _ _ _ _ _ pk).trans (wr_upd1_isCanonicalRef _ _ pk)

private theorem wr_block_eq_upd (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    blockLevelPrims X W =
      { blockLevelPrims X W with isTorsionFree := fun P => edSmul edOrderL P == edZero } := rfl

private theorem wr_upd_isTorsionFree (B : SignalPqxdh.Primitives) (f : EdPoint → Bool)
    (P : EdPoint) :
    ({ B with isTorsionFree := f } : SignalPqxdh.Primitives).isTorsionFree P = f P := rfl

private theorem wr_block_isTorsionFree (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (P : EdPoint) :
    (blockLevelPrims X W).isTorsionFree P = (edSmul edOrderL P == edZero) :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.isTorsionFree P) (wr_block_eq_upd X W)).trans
    (wr_upd_isTorsionFree _ _ P)

private theorem wr_block_montToEd_zero (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk : List UInt8) :
    (blockLevelPrims X W).montToEd pk 0 = montLiftEd (u8Vec 32 pk) 0#8 := by
  change SignalPqxdh.montLiftEd (u8Vec 32 pk).toList (0 : UInt8).toBitVec = _
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl, signalMontLiftEd_eq]

private theorem wr_if_pos {c : Prop} [Decidable c] (h : c) {α : Type _} {t e : α} :
    (if c then t else e) = t := by
  split
  · rfl
  · rename_i hn; exact absurd h hn

private theorem wr_if_neg {c : Prop} [Decidable c] (h : ¬ c) {α : Type _} {t e : α} :
    (if c then t else e) = e := by
  split
  · rename_i hp; exact absurd hp h
  · rfl

private theorem wr_isCanonicalRef_of_some (B : SignalPqxdh.Primitives) (pk : List UInt8)
    (P : EdPoint)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = some P) :
    SignalPqxdh.isCanonicalRef B pk = B.isTorsionFree P := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, wr_if_pos hg]
  split
  · rename_i Q hQ; exact congrArg B.isTorsionFree (Option.some.inj (hQ.symm.trans hm))
  · rename_i hQ; exact absurd (hQ.symm.trans hm) nofun

private theorem wr_isCanonicalRef_of_none (B : SignalPqxdh.Primitives) (pk : List UInt8)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = none) :
    SignalPqxdh.isCanonicalRef B pk = false := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, wr_if_pos hg]
  split
  · rename_i Q hQ; exact absurd (hQ.symm.trans hm) nofun
  · rfl

private theorem wr_isCanonicalRef_of_false (B : SignalPqxdh.Primitives) (pk : List UInt8)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = false) :
    SignalPqxdh.isCanonicalRef B pk = false := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, wr_if_neg (by rw [hg]; decide)]

set_option linter.auxLemma false in
private theorem wr_canon_match_some (m : Option EdPoint) (P : EdPoint) (f : EdPoint → Bool)
    (hm : m = some P) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.isCanonicalX25519.match_1
      (fun _ => Bool) m (fun _ => false) f = f P := by
  subst hm; rfl

set_option linter.auxLemma false in
private theorem wr_canon_match_none (m : Option EdPoint) (f : EdPoint → Bool)
    (hm : m = none) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.isCanonicalX25519.match_1
      (fun _ => Bool) m (fun _ => false) f = false := by
  subst hm; rfl

private theorem wr_isCanonicalX25519_of_some (bs : List (BitVec 8)) (P : EdPoint)
    (hg : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = true)
    (hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 = some P) :
    isCanonicalX25519 bs = (edSmul edOrderL P == edZero) := by
  unfold isCanonicalX25519
  rw [hg, Bool.true_and]
  exact wr_canon_match_some _ P (fun Q => edSmul edOrderL Q == edZero) hm

private theorem wr_isCanonicalX25519_of_none (bs : List (BitVec 8))
    (hg : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = true)
    (hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 = none) :
    isCanonicalX25519 bs = false := by
  unfold isCanonicalX25519
  rw [hg, Bool.true_and]
  exact wr_canon_match_none _ (fun Q => edSmul edOrderL Q == edZero) hm

private theorem wr_isCanonicalX25519_of_false (bs : List (BitVec 8))
    (hg : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = false) :
    isCanonicalX25519 bs = false := by
  unfold isCanonicalX25519
  rw [hg, Bool.false_and]

private theorem wr_match_edPoint_eq_true (m : Option EdPoint) (f : EdPoint → Bool)
    (h : (match m with | none => false | some Q => f Q) = true) :
    ∃ P, m = some P ∧ f P = true := by
  cases m with
  | none => cases h
  | some P => exact ⟨P, rfl, h⟩

private theorem wr_sha512Step_congr {B C : SignalPqxdh.Primitives}
    (h : B.sha512Compress = C.sha512Compress) :
    SignalPqxdh.sha512Step B = SignalPqxdh.sha512Step C := by
  funext s b
  unfold SignalPqxdh.sha512Step
  rw [h]

private theorem wr_sha512Ref_congr {B C : SignalPqxdh.Primitives}
    (h : B.sha512Compress = C.sha512Compress) :
    SignalPqxdh.sha512Ref B = SignalPqxdh.sha512Ref C := by
  funext msg
  unfold SignalPqxdh.sha512Ref
  rw [wr_sha512Step_congr h]

private theorem wr_upd9_proj (B1 : SignalPqxdh.Primitives)
    (sv ic h96 rcc cks ckn dmk ae ad) :
    let M : SignalPqxdh.Primitives := { B1 with
      sigVerify := sv, isCanonical := ic, hkdfDerive96 := h96, rootCreateChain := rcc,
      chainKdfSeed := cks, chainKdfNext := ckn, deriveMsgKeys := dmk, aeadEnc := ae, aeadDec := ad }
    M.scalarFromBytesModOrder = B1.scalarFromBytesModOrder ∧
    M.montToEd = B1.montToEd ∧
    M.x25519Base = B1.x25519Base ∧
    M.doubleScalarMulBasepoint = B1.doubleScalarMulBasepoint ∧
    M.compress = B1.compress ∧
    M.scalarFromWide = B1.scalarFromWide ∧
    M.sha512 = B1.sha512 ∧
    M.scalarAdd = B1.scalarAdd ∧
    M.scalarMul = B1.scalarMul :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wr_upd1_proj (B : SignalPqxdh.Primitives) (s512) :
    let B1 : SignalPqxdh.Primitives := { B with sha512 := s512 }
    B1.scalarFromBytesModOrder = B.scalarFromBytesModOrder ∧
    B1.montToEd = B.montToEd ∧
    B1.x25519Base = B.x25519Base ∧
    B1.doubleScalarMulBasepoint = B.doubleScalarMulBasepoint ∧
    B1.compress = B.compress ∧
    B1.scalarFromWide = B.scalarFromWide ∧
    B1.sha512 = s512 ∧
    B1.scalarAdd = B.scalarAdd ∧
    B1.scalarMul = B.scalarMul :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wr_xeddsaSignRef_congr {B C : SignalPqxdh.Primitives}
    (h1 : B.scalarFromBytesModOrder = C.scalarFromBytesModOrder)
    (h2 : B.montToEd = C.montToEd)
    (h3 : B.x25519Base = C.x25519Base)
    (h4 : B.doubleScalarMulBasepoint = C.doubleScalarMulBasepoint)
    (h5 : B.compress = C.compress)
    (h6 : B.scalarFromWide = C.scalarFromWide)
    (h7 : B.sha512 = C.sha512)
    (h8 : B.scalarAdd = C.scalarAdd)
    (h9 : B.scalarMul = C.scalarMul) :
    xeddsaSignRef B = xeddsaSignRef C := by
  funext sk m rand
  unfold xeddsaSignRef Computational.Proofs.SignalPqxdh.XeddsaRom.Statements.edBaseMul
    Computational.Proofs.SignalPqxdh.XeddsaRom.Statements.edDummy
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]

private theorem wr_xeddsaSignRef_modelPrims_congr
    (X1 X2 : UnreachedPqxdhPrimitives) (W1 W2 : PEParams)
    (hAdd : X1.scalarAdd = X2.scalarAdd)
    (hMul : X1.scalarMul = X2.scalarMul)
    (hPub : W1.C.pubKey = W2.C.pubKey)
    (hF512 : W1.Q.F512 = W2.Q.F512) :
    xeddsaSignRef (modelPrims X1 W1) = xeddsaSignRef (modelPrims X2 W2) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ :=
    wr_upd9_proj { blockLevelPrims X1 W1 with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X1 W1) }
      _ _ _ _ _ _ _ _ _
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ :=
    wr_upd1_proj (blockLevelPrims X1 W1) (SignalPqxdh.sha512Ref (blockLevelPrims X1 W1))
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    wr_upd9_proj { blockLevelPrims X2 W2 with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X2 W2) }
      _ _ _ _ _ _ _ _ _
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    wr_upd1_proj (blockLevelPrims X2 W2) (SignalPqxdh.sha512Ref (blockLevelPrims X2 W2))
  have h3_mid : (blockLevelPrims X1 W1).x25519Base = (blockLevelPrims X2 W2).x25519Base := by
    funext a
    change vecU8 (W1.C.pubKey (Ratchet.clampScalar (u8Vec 32 a))) =
      vecU8 (W2.C.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
    rw [hPub]
  have h7_mid : SignalPqxdh.sha512Ref (blockLevelPrims X1 W1) =
      SignalPqxdh.sha512Ref (blockLevelPrims X2 W2) := by
    refine wr_sha512Ref_congr ?_
    funext st blk
    change sha512StateBytesBE (W1.Q.F512 (sha512StateOf st) (ofU8 blk)) =
      sha512StateBytesBE (W2.Q.F512 (sha512StateOf st) (ofU8 blk))
    rw [hF512]
  exact wr_xeddsaSignRef_congr
    ((u1.trans v1).trans (p1.trans q1).symm)
    ((u2.trans v2).trans (p2.trans q2).symm)
    ((u3.trans v3).trans (h3_mid.trans (p3.trans q3).symm))
    ((u4.trans v4).trans (p4.trans q4).symm)
    ((u5.trans v5).trans (p5.trans q5).symm)
    ((u6.trans v6).trans (p6.trans q6).symm)
    ((u7.trans v7).trans (h7_mid.trans (p7.trans q7).symm))
    ((u8.trans v8).trans (hAdd.trans (p8.trans q8).symm))
    ((u9.trans v9).trans (hMul.trans (p9.trans q9).symm))

private theorem wr_upd_xreal_proj (X : UnreachedPqxdhPrimitives) (ss ivd) :
    let Y : UnreachedPqxdhPrimitives := { X with sigSign := ss, isValidDhTriple := ivd }
    Y.sigSign = ss ∧ Y.scalarAdd = X.scalarAdd ∧ Y.scalarMul = X.scalarMul :=
  ⟨rfl, rfl, rfl⟩

theorem xReal_sigSign : XReal.sigSign = xeddsaSignRef (modelPrims XReal WReal) := by
  obtain ⟨hss, hAdd, hMul⟩ := wr_upd_xreal_proj XReal_pre
    (xeddsaSignRef (modelPrims XReal_pre WReal))
    (fun A B Z => @decide (isValidDhTripleRef (modelPrims XReal_pre WReal) A B Z) (Classical.propDecidable _))
  exact hss.trans (wr_xeddsaSignRef_modelPrims_congr XReal_pre XReal WReal WReal hAdd.symm hMul.symm rfl rfl)

theorem xReal_pow8 : XReal.pow8 = pow8Real := by
  unfold XReal XReal_pre
  rfl

/-! ## 2. Disproof of `pow8_idemp` for Raw `[8]P` (`not_pow8_idemp_ladder8`) -/

private theorem p25519_lt_two_pow_255_real : p25519 < 2 ^ 255 := by
  unfold p25519; decide

private theorem p25519_lt_256_pow_32 : p25519 < 256 ^ 32 := by
  unfold p25519; decide

private theorem decodeU255_natToLeBytes_of_lt_p {u : Nat} (hu : u < p25519) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 (natToLeBytes 32 u) = u := by
  unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
  rw [List.take_of_length_le (Nat.le_of_eq (natToLeBytes_len 32 u)),
      leBytesToNat_natToLeBytes_of_lt (lt_trans hu p25519_lt_256_pow_32),
      Nat.mod_eq_of_lt (lt_trans hu p25519_lt_two_pow_255_real)]

/-- Raw 3-doubling `[8]P` (`pow8Ladder8`) is not idempotent on the Curve25519 basepoint:
`pow8Ladder8 (pow8Ladder8 B) = [64]B ≠ [8]B = pow8Ladder8 B`, so it violates
`WellFormedPrimitivesδ.pow8_idemp` (`ModelPrimsCryptoAssumptions.pow8_idemp`). -/
theorem not_pow8_idemp_ladder8 :
    pow8Ladder8 (pow8Ladder8 (toU8 x25519Basepoint)) ≠ pow8Ladder8 (toU8 x25519Basepoint) := by
  have hlenB : (toU8 x25519Basepoint).length = 32 := by
    rw [toU8_length]; exact natToLeBytes_len 32 9
  have h9_lt : 9 < p25519 := by unfold p25519; decide
  have hp1 : pow8Ladder8 (toU8 x25519Basepoint) =
      toU8 (natToLeBytes 32 (edToMontU (edNatSmul 8 edBasepoint))) := by
    unfold pow8Ladder8
    rw [beq_iff_eq.mpr hlenB]
    simp only [↓reduceIte, ofU8_toU8]
    unfold x25519Basepoint
    rw [decodeU255_natToLeBytes_of_lt_p h9_lt, ← edToMontU_edBasepoint,
        x25519Ladder_edToMontU (by decide : 8 < 2 ^ 255) edOnCurve_edBasepoint]
  have hp2 : pow8Ladder8 (pow8Ladder8 (toU8 x25519Basepoint)) =
      toU8 (natToLeBytes 32 (edToMontU (edNatSmul 64 edBasepoint))) := by
    rw [hp1]
    unfold pow8Ladder8
    have hlen8 : (toU8 (natToLeBytes 32 (edToMontU (edNatSmul 8 edBasepoint)))).length = 32 := by
      rw [toU8_length, natToLeBytes_len]
    rw [beq_iff_eq.mpr hlen8]
    simp only [↓reduceIte, ofU8_toU8,
      decodeU255_natToLeBytes_of_lt_p (edToMontU_lt _),
      x25519Ladder_edToMontU (by decide : 8 < 2 ^ 255) (edOnCurve_edNatSmul 8 edOnCurve_edBasepoint),
      ← edNatSmul_mul 8 8 edOnCurve_edBasepoint]
  rw [hp2, hp1]
  intro heq
  have hbytes : natToLeBytes 32 (edToMontU (edNatSmul 64 edBasepoint)) =
      natToLeBytes 32 (edToMontU (edNatSmul 8 edBasepoint)) := by
    have h := congrArg ofU8 heq
    rwa [ofU8_toU8, ofU8_toU8] at h
  have hu : edToMontU (edNatSmul 64 edBasepoint) = edToMontU (edNatSmul 8 edBasepoint) := by
    have h := congrArg leBytesToNat hbytes
    rwa [leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32),
         leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32)] at h
  rw [← edSmul_eq_edNatSmul (by decide : 64 < 2 ^ 256) edOnCurve_edBasepoint,
      ← edSmul_eq_edNatSmul (by decide : 8 < 2 ^ 256) edOnCurve_edBasepoint] at hu
  have h64_8 := (edToMontU_edSmul_edBasepoint_eq_iff
    (by unfold edOrderL; decide : 64 ≤ (edOrderL - 1) / 2)
    (by unfold edOrderL; decide : 8 ≤ (edOrderL - 1) / 2)).mp hu
  omega

/-! ## 3. Byte / Little-Endian / Clamped-Scalar Bridges -/

attribute [local irreducible] fpInv recoverXEven montLiftEd edSmul

private theorem shared_edNatSmul_eq (n : Nat) (P : EdPoint) :
    edNatSmul n P =
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards.edNatSmul n P := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [edNatSmul,
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards.edNatSmul, ih]

private theorem edNatSmul_mod_edOrderL_s {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (n : Nat) :
    edNatSmul n P = edNatSmul (n % edOrderL) P := by
  simp only [shared_edNatSmul_eq] at hL ⊢
  exact edNatSmul_mod_edOrderL hP hL n

private theorem edNatSmul_ne_edZero_of_zmod_ne_zero_s {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {z : ZMod l25519} (hz : z ≠ 0) :
    edNatSmul z.val P ≠ edZero := by
  simp only [shared_edNatSmul_eq] at hL ⊢
  exact edNatSmul_ne_edZero_of_zmod_ne_zero hP hne hL hz

private theorem edNatSmul_zmod_mul_s {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a b : ZMod l25519) :
    edNatSmul (a * b).val P = edNatSmul a.val (edNatSmul b.val P) := by
  simp only [shared_edNatSmul_eq] at hL ⊢
  exact edNatSmul_zmod_mul hP hL a b

private theorem edNatSmul_zmod_neg_s {P : EdPoint} (hP : edOnCurve P = true)
    (hL : edNatSmul edOrderL P = edZero) (a : ZMod l25519) :
    edNatSmul (-a).val P = edNeg (edNatSmul a.val P) := by
  simp only [shared_edNatSmul_eq] at hL ⊢
  exact edNatSmul_zmod_neg hP hL a

private theorem edToMontU_edNeg_s {P : EdPoint} (hP : edOnCurve P = true) :
    edToMontU (edNeg P) = edToMontU P := by
  unfold edToMontU
  dsimp only [edNeg]
  rw [Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

private theorem edNatSmul_zmod_inj_s {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a b : ZMod l25519} (heq : edNatSmul a.val P = edNatSmul b.val P) :
    a = b := by
  simp only [shared_edNatSmul_eq] at hL heq
  exact edNatSmul_zmod_inj hP hne hL heq

private theorem edToMontU_edNatSmul_eq_iff_s {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) (hL : edNatSmul edOrderL P = edZero)
    {a b : ZMod l25519} (ha : a ≠ 0) (hb : b ≠ 0) :
    edToMontU (edNatSmul a.val P) = edToMontU (edNatSmul b.val P) ↔ a = b ∨ a = -b := by
  simp only [shared_edNatSmul_eq] at hL ⊢
  exact edToMontU_edNatSmul_eq_iff hP hne hL ha hb

private theorem if_true_eq_r {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

private theorem if_false_eq_r {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

private theorem edOrderL_eq_l25519_r : edOrderL = l25519 := by
  unfold edOrderL l25519; decide

private theorem edNatSmul_edOrderL_edBasepoint_r : edNatSmul edOrderL edBasepoint = edZero :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards.edNatSmul_edOrderL_edBasepoint

private theorem leBytesToNat_ofU8 (bs : List UInt8) :
    leBytesToNat (ofU8 bs) = natOfBytesLE bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hcons : ofU8 (b :: rest) = b.toBitVec :: ofU8 rest := rfl
    have hb : b.toBitVec.toNat = b.toNat := rfl
    rw [hcons, leBytesToNat_cons, natOfBytesLE, ih, hb]
    omega

private theorem toU8_natToLeBytes (k n : Nat) :
    toU8 (natToLeBytes k n) = bytesOfNatLE k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [natToLeBytes_succ, bytesOfNatLE]
    have hcons : ∀ (x : BitVec 8) (xs : List (BitVec 8)),
        toU8 (x :: xs) = UInt8.ofBitVec x :: toU8 xs := fun _ _ => rfl
    rw [hcons, ih]
    congr 1
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.ofNat]

private theorem u8Vec_toList_eq_ofU8_fitBytesRef (n : Nat) (bs : List UInt8) :
    (u8Vec n bs).toList = ofU8 (fitBytesRef n bs) := by
  change List.take n (List.map UInt8.toBitVec bs ++ List.replicate n 0#8) =
    List.map UInt8.toBitVec (List.take n bs ++ List.replicate (n - bs.length) 0)
  rw [List.map_append, List.map_take, List.map_replicate,
      List.take_append, List.length_map, List.take_replicate,
      Nat.min_eq_left (Nat.sub_le n bs.length)]
  rfl

private theorem clampScalarBytes_id_of_already_clamped (a : List UInt8) :
    clampScalarBytes (ofU8 (clampScalar25519 a)) = ofU8 (clampScalar25519 a) := by
  have hlen : (ofU8 (clampScalar25519 a)).length = 32 := by
    rw [ofU8_length, clampScalar25519_length]
  have hvec : (⟨ofU8 (clampScalar25519 a), hlen⟩ : List.Vector (BitVec 8) 32) =
      Ratchet.clampScalar (u8Vec 32 a) := by
    apply List.Vector.eq
    change ofU8 (clampScalar25519 a) = (Ratchet.clampScalar (u8Vec 32 a)).toList
    rw [← u8Vec_clampScalar25519, u8Vec_toList_of_length (clampScalar25519_length a)]
  set l := ofU8 (clampScalar25519 a)
  have h2 : Ratchet.clampScalar (⟨l, hlen⟩ : List.Vector (BitVec 8) 32) = ⟨l, hlen⟩ := by
    rw [hvec]
    apply List.Vector.eq
    rcases u8Vec 32 a with ⟨bs, hbs⟩
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
      _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
      _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hbs; done)
    have hb0 : ∀ x : BitVec 8, (x &&& 0xf8#8) &&& 0xf8#8 = x &&& 0xf8#8 := by decide
    have hb31 : ∀ x : BitVec 8,
        (((x &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (x &&& 0x7f#8) ||| 0x40#8 := by
      decide
    change [(b0 &&& 0xf8#8) &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23,
        b24, b25, b26, b27, b28, b29, b30,
        (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8] =
      [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23,
        b24, b25, b26, b27, b28, b29, b30, (b31 &&& 0x7f#8) ||| 0x40#8]
    rw [hb0, hb31]
  have h3 : (Ratchet.clampScalar (⟨l, hlen⟩ : List.Vector (BitVec 8) 32)).toList =
      clampScalarBytes l := by
    rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
      _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
      _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hlen; done)
    rfl
  exact (congrArg List.Vector.toList h2).symm.trans h3 |>.symm

private theorem clampScalar_ratchet_u8Vec_eq (a : List UInt8) :
    VerifiedLibraries.Common.clampScalar (Ratchet.clampScalar (u8Vec 32 a)).toList =
      natOfBytesLE (clampScalar25519 a) := by
  have hlist : (Ratchet.clampScalar (u8Vec 32 a)).toList = ofU8 (clampScalar25519 a) := by
    rw [← u8Vec_clampScalar25519, u8Vec_toList_of_length (clampScalar25519_length a)]
  rw [hlist]
  unfold VerifiedLibraries.Common.clampScalar
  have hlen : (ofU8 (clampScalar25519 a)).length = 32 := by
    rw [ofU8_length, clampScalar25519_length]
  rw [List.take_of_length_le (Nat.le_of_eq hlen),
      clampScalarBytes_id_of_already_clamped a, leBytesToNat_ofU8]

private theorem clampScalar_ratchet_u8Vec_mod_edOrderL (a : List UInt8) :
    VerifiedLibraries.Common.clampScalar (Ratchet.clampScalar (u8Vec 32 a)).toList % edOrderL =
      (clampedScalarZMod a).val := by
  rw [clampScalar_ratchet_u8Vec_eq, edOrderL_eq_l25519_r]
  unfold clampedScalarZMod decodeScalarBytes
  exact (ZMod.val_natCast l25519 (natOfBytesLE (clampScalar25519 a))).symm

private theorem clampScalar_keyToBytes32_mod_edOrderL (k : BitVec 256) :
    VerifiedLibraries.Common.clampScalar (HMAC.keyToBytes32 k) % edOrderL =
      (clampedScalarZMod (word256ToBytes k)).val := by
  let kv : List.Vector (BitVec 8) 32 := ⟨HMAC.keyToBytes32 k, length_keyToBytes32 k⟩
  have hu : u8Vec 32 (word256ToBytes k) = kv := by
    apply List.Vector.eq
    change (u8Vec 32 (word256ToBytes k)).toList = HMAC.keyToBytes32 k
    rw [u8Vec_toList_of_length (length_word256ToBytes k), ofU8_word256ToBytes]
  have hcl :=
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.clampScalar_ratchet_clampScalar kv
  change VerifiedLibraries.Common.clampScalar kv.toList % edOrderL = _
  rw [← hcl, ← hu]
  exact clampScalar_ratchet_u8Vec_mod_edOrderL (word256ToBytes k)

/-! ## 4. `X25519RealizesDh cReal dhReal encPtReal encTReal` on `Pt25519` -/

/-- Generator `[1]B` (`u = 9`) in `Pt25519`. -/
def baseReal : Pt25519 :=
  ⟨1, by unfold halfL25519 l25519; decide⟩

/-- Embeds `Q : Pt25519` into `BitVec 255` via `0` at `0` and the Curve25519 Montgomery
`u`-coordinate `edToMontU ([Q.val] edBasepoint)` for `Q ≠ 0`. -/
def ptToBvReal (Q : Pt25519) : BitVec 255 :=
  if Q.val == 0 then 0#255
  else BitVec.ofNat 255 (edToMontU (edNatSmul Q.val edBasepoint))

/-- 32-byte little-endian Curve25519 Montgomery encoding of `Q : Pt25519`. -/
def encPtReal (Q : Pt25519) : List (BitVec 8) :=
  encPt255 (ptToBvReal Q)

def encTReal (Q : Pt25519) : PublicKey :=
  encT255 (ptToBvReal Q)

/-- Left inverse of `encTReal` on `PublicKey` via `findPt25519` (computable, though practical to
evaluate only on small `Pt25519` exponents since `halfL25519 + 1 ≈ 2 ^ 251`). -/
def decTReal (pk : PublicKey) : Option Pt25519 :=
  findPt25519 encTReal pk

/-- Clamped x-only prime-subgroup DH action on `Pt25519` over `ZMod l25519`. -/
def dhReal : DHFun (BitVec 256) Pt25519 where
  base := baseReal
  dh k Q :=
    ⟨absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)),
     Nat.lt_succ_of_le (absZMod_le_half _)⟩

private theorem dhReal_dh_val (k : BitVec 256) (Q : Pt25519) :
    (dhReal.dh k Q).val =
      absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) := by
  unfold dhReal
  rfl

private theorem vec32_toList_r {bs : List (BitVec 8)} (h : bs.length = 32) :
    (vec32 bs).toList = bs := by
  simp [vec32, h]

private theorem pt25519_val_lt_l (Q : Pt25519) : Q.val < l25519 :=
  lt_trans (lt_of_le_of_lt (Nat.lt_succ_iff.mp Q.isLt) halfL25519_lt_two_pow_252)
    two_pow_252_lt_l25519

private theorem absZMod_pt25519_cast_r (Q : Pt25519) :
    absZMod (Q.val : ZMod l25519) = Q.val := by
  unfold absZMod
  simp [ZMod.val_natCast_of_lt (pt25519_val_lt_l Q), Nat.lt_succ_iff.mp Q.isLt]

private theorem pt25519_cast_ne_0 {Q : Pt25519} (hQ : Q ≠ 0) :
    (Q.val : ZMod l25519) ≠ 0 := by
  intro h0
  have hv := congrArg ZMod.val h0
  rw [ZMod.val_natCast_of_lt (pt25519_val_lt_l Q), ZMod.val_zero] at hv
  exact hQ (Fin.ext (by simpa using hv))

private theorem baseReal_ne_zero : dhReal.base ≠ 0 := by
  intro h
  unfold dhReal baseReal at h
  have hv := congrArg Fin.val h
  rw [Fin.val_zero] at hv
  exact absurd hv (by decide : (1 : ℕ) ≠ 0)

private theorem encPtReal_eq_natToLeBytes_of_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) :
    encPtReal Q = natToLeBytes 32 (edToMontU (edNatSmul Q.val edBasepoint)) := by
  have hne : (Q.val == 0) = false := beq_eq_false_iff_ne.mpr fun h0 => hQ (Fin.ext h0)
  unfold encPtReal ptToBvReal
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact encPt255_ofNat_of_lt (lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_real)

private theorem ptToBvReal_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) : ptToBvReal Q ≠ 0 := by
  intro h0
  have hne : (Q.val == 0) = false := beq_eq_false_iff_ne.mpr fun hz => hQ (Fin.ext hz)
  unfold ptToBvReal at h0
  rw [hne] at h0
  simp only [Bool.false_eq_true, ↓reduceIte] at h0
  have hu0 : edToMontU (edNatSmul Q.val edBasepoint) = 0 := by
    have ht := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_real)] at ht
  have hx0 : (edNatSmul Q.val edBasepoint).x = 0 :=
    (edToMontU_eq_zero_iff (edOnCurve_edNatSmul Q.val edOnCurve_edBasepoint)).mp hu0
  have h2z : edNatSmul 2 (edNatSmul Q.val edBasepoint) = edZero :=
    (edNatSmul_two_eq_zero_iff (edOnCurve_edNatSmul Q.val edOnCurve_edBasepoint)).mpr hx0
  have h2_ne : (2 : ZMod l25519) ≠ 0 := by
    intro h2
    have hv := congrArg ZMod.val h2
    change ((2 : ℕ) : ZMod l25519).val = (0 : ZMod l25519).val at hv
    rw [ZMod.val_natCast_of_lt (by unfold l25519; decide), ZMod.val_zero] at hv
    omega
  have h2Q : edNatSmul ((2 : ZMod l25519) * (Q.val : ZMod l25519)).val edBasepoint = edZero := by
    have h2v : (2 : ZMod l25519).val = 2 := ZMod.val_natCast_of_lt (by unfold l25519; decide)
    have hQv : (Q.val : ZMod l25519).val = Q.val := ZMod.val_natCast_of_lt (pt25519_val_lt_l Q)
    rw [edNatSmul_zmod_mul_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r, h2v, hQv]
    exact h2z
  exact edNatSmul_ne_edZero_of_zmod_ne_zero_s edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint_r (mul_ne_zero h2_ne (pt25519_cast_ne_0 hQ)) h2Q

private theorem ptToBvReal_inj : Function.Injective ptToBvReal := by
  intro Q1 Q2 h
  by_cases h1 : Q1 = 0
  · subst h1
    by_cases h2 : Q2 = 0
    · exact h2.symm
    · exact absurd h.symm (ptToBvReal_ne_zero h2)
  · by_cases h2 : Q2 = 0
    · subst h2
      exact absurd h (ptToBvReal_ne_zero h1)
    · have hne1 : (Q1.val == 0) = false := beq_eq_false_iff_ne.mpr fun hz => h1 (Fin.ext hz)
      have hne2 : (Q2.val == 0) = false := beq_eq_false_iff_ne.mpr fun hz => h2 (Fin.ext hz)
      unfold ptToBvReal at h
      rw [hne1, hne2] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hu_eq : edToMontU (edNatSmul Q1.val edBasepoint) =
          edToMontU (edNatSmul Q2.val edBasepoint) := by
        have ht := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_real),
          Nat.mod_eq_of_lt (lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_real)] at ht
      have hv1 : Q1.val = (Q1.val : ZMod l25519).val :=
        (ZMod.val_natCast_of_lt (pt25519_val_lt_l Q1)).symm
      have hv2 : Q2.val = (Q2.val : ZMod l25519).val :=
        (ZMod.val_natCast_of_lt (pt25519_val_lt_l Q2)).symm
      rw [hv1, hv2] at hu_eq
      have hpm := (edToMontU_edNatSmul_eq_iff_s edOnCurve_edBasepoint edBasepoint_ne_edZero
        edNatSmul_edOrderL_edBasepoint_r (pt25519_cast_ne_0 h1) (pt25519_cast_ne_0 h2)).mp hu_eq
      have habs := (absZMod_eq_iff _ _).mpr hpm
      rw [absZMod_pt25519_cast_r, absZMod_pt25519_cast_r] at habs
      exact Fin.ext habs

theorem encPtReal_inj : Function.Injective encPtReal :=
  encPt255_inj.comp ptToBvReal_inj

theorem encTReal_inj : Function.Injective encTReal :=
  encT255_inj.comp ptToBvReal_inj

theorem decTReal_encTReal (Q : Pt25519) : decTReal (encTReal Q) = some Q :=
  findPt25519_apply encTReal_inj Q

open Classical in
/-- `decTReal` agrees pointwise with the `Exists.choose` definition. -/
theorem decTReal_eq_classical :
    decTReal = fun pk : PublicKey =>
      if h : ∃ Q : Pt25519, encTReal Q = pk then some h.choose else none := by
  funext pk
  split_ifs with h
  · exact (findPt25519_eq_some_iff encTReal_inj pk h.choose).mpr h.choose_spec
  · cases hd : decTReal pk with
    | none => rfl
    | some Q =>
      exact absurd ⟨Q, (findPt25519_eq_some_iff encTReal_inj pk Q).mp hd⟩ h

theorem encTReal_ne_dummyKey (Q : Pt25519) : encTReal Q ≠ dummyKey := by
  unfold encTReal
  exact encT255_ne_dummyKey (ptToBvReal Q)

theorem dhReal_zero (x : BitVec 256) : dhReal.dh x 0 = 0 := by
  apply Fin.ext
  rw [dhReal_dh_val, Fin.val_zero]
  simp [absZMod]

theorem dhReal_ne_zero (k : BitVec 256) (Q : Pt25519) (hQ : Q ≠ 0) :
    dhReal.dh k Q ≠ 0 := by
  intro h0
  have hval : absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) = 0 := by
    have h := congrArg Fin.val h0
    rwa [dhReal_dh_val, Fin.val_zero] at h
  have hmul := (absZMod_eq_zero_iff _).mp hval
  exact mul_ne_zero (clampedScalarZMod_ne_zero (word256ToBytes k)) (pt25519_cast_ne_0 hQ) hmul

private theorem absZMod_mul_cast_absZMod (x y : ZMod l25519) :
    absZMod (x * ((absZMod y : ℕ) : ZMod l25519)) = absZMod (x * y) := by
  have habs : absZMod ((absZMod y : ℕ) : ZMod l25519) = absZMod y := by
    set n := absZMod y
    have hle : n ≤ halfL25519 := absZMod_le_half y
    have hlt : n < l25519 :=
      lt_trans (lt_of_le_of_lt hle halfL25519_lt_two_pow_252) two_pow_252_lt_l25519
    unfold absZMod
    rw [ZMod.val_natCast_of_lt hlt, if_true_eq_r hle]
  rcases (absZMod_eq_iff _ y).mp habs with hy | hy
  · rw [hy]
  · rw [hy, mul_neg, absZMod_neg]

theorem dhReal_commutes : dhReal.Commutes := by
  intro a b
  apply Fin.ext
  rw [dhReal_dh_val, dhReal_dh_val, dhReal_dh_val, dhReal_dh_val,
      absZMod_mul_cast_absZMod, absZMod_mul_cast_absZMod,
      ← mul_assoc, ← mul_assoc,
      mul_comm (clampedScalarZMod (word256ToBytes a)) (clampedScalarZMod (word256ToBytes b))]

theorem dhReal_dh_inj (a : BitVec 256) : Function.Injective (dhReal.dh a) := by
  intro Q Q' h
  have habs : absZMod (clampedScalarZMod (word256ToBytes a) * (Q.val : ZMod l25519)) =
      absZMod (clampedScalarZMod (word256ToBytes a) * (Q'.val : ZMod l25519)) := by
    have hv := congrArg Fin.val h
    rwa [dhReal_dh_val, dhReal_dh_val] at hv
  have hpm : (Q.val : ZMod l25519) = (Q'.val : ZMod l25519) ∨
      (Q.val : ZMod l25519) = -(Q'.val : ZMod l25519) := by
    rcases (absZMod_eq_iff _ _).mp habs with hm | hm
    · exact Or.inl (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
    · rw [← mul_neg] at hm
      exact Or.inr (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
  have hval : absZMod (Q.val : ZMod l25519) = absZMod (Q'.val : ZMod l25519) :=
    (absZMod_eq_iff _ _).mpr hpm
  rw [absZMod_pt25519_cast_r, absZMod_pt25519_cast_r] at hval
  exact Fin.ext hval

theorem dhReal_kerUniform : DhKerUniform dhReal := by
  intro s x Q Q'
  rw [(dhReal_dh_inj x).eq_iff, (dhReal_dh_inj s).eq_iff]

theorem dhReal_base_fiber_card (Q : Pt25519) :
    (Finset.univ.filter (fun w : BitVec 256 => dhReal.dh w dhReal.base = Q)).card ≤ 64 := by
  set S := Finset.univ.filter (fun w : BitVec 256 => dhReal.dh w dhReal.base = Q)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : dhReal.dh w0 dhReal.base = Q := (Finset.mem_filter.mp hw0).2
    set c0 := clampedScalarZMod (word256ToBytes w0)
    let b0 : ZMod l25519 := (dhReal.base.val : ZMod l25519)
    have hb0_ne : b0 ≠ 0 := pt25519_cast_ne_0 baseReal_ne_zero
    have hc0_ne_neg : c0 ≠ -c0 := by
      intro h2c0
      have hc0_ne : c0 ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes w0)
      have hs := edSignZMod_neg c0 hc0_ne
      rw [← h2c0] at hs
      rcases edSignZMod_bool c0 with hb | hb <;> rw [hb] at hs <;>
        exact (by revert hs; decide)
    let tag : BitVec 256 → Bool × Fin 8 × Fin 4 := fun w =>
      (@decide (clampedScalarZMod (word256ToBytes w) = c0) (Classical.propDecidable _),
       ⟨w.toNat % 8, Nat.mod_lt _ (by decide)⟩,
       ⟨w.toNat / 2 ^ 254, Nat.div_lt_of_lt_mul (by have := w.isLt; omega)⟩)
    have hinj : Set.InjOn tag (S : Set (BitVec 256)) := by
      intro w1 hw1 w2 hw2 htag
      have hw1_eq : dhReal.dh w1 dhReal.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
      have hw2_eq : dhReal.dh w2 dhReal.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
      have hw1_abs : absZMod (clampedScalarZMod (word256ToBytes w1) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw1_eq.trans hw0_eq.symm)
        rwa [dhReal_dh_val, dhReal_dh_val] at h
      have hw2_abs : absZMod (clampedScalarZMod (word256ToBytes w2) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw2_eq.trans hw0_eq.symm)
        rwa [dhReal_dh_val, dhReal_dh_val] at h
      have hpm1 : clampedScalarZMod (word256ToBytes w1) = c0 ∨
          clampedScalarZMod (word256ToBytes w1) = -c0 := by
        rcases (absZMod_eq_iff _ _).mp hw1_abs with hm | hm
        · exact Or.inl (mul_right_cancel₀ hb0_ne hm)
        · rw [← neg_mul] at hm
          exact Or.inr (mul_right_cancel₀ hb0_ne hm)
      have hpm2 : clampedScalarZMod (word256ToBytes w2) = c0 ∨
          clampedScalarZMod (word256ToBytes w2) = -c0 := by
        rcases (absZMod_eq_iff _ _).mp hw2_abs with hm | hm
        · exact Or.inl (mul_right_cancel₀ hb0_ne hm)
        · rw [← neg_mul] at hm
          exact Or.inr (mul_right_cancel₀ hb0_ne hm)
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

theorem dhReal_base_fiber_prob_le (Q : Pt25519) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | dhReal.dh x dhReal.base = Q} ≤
      (1 : ℝ≥0∞) / 2 ^ 250 := by
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample,
      Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_of_le_mul
  calc ((Finset.univ.filter (fun x : BitVec 256 => dhReal.dh x dhReal.base = Q)).card : ℝ≥0∞)
      ≤ ((64 : ℕ) : ℝ≥0∞) := by exact_mod_cast dhReal_base_fiber_card Q
    _ = (2 : ℝ≥0∞) ^ 6 := by norm_num
    _ = ((1 : ℝ≥0∞) / 2 ^ 250) * (2 : ℝ≥0∞) ^ 256 := by
      rw [one_div, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 250 * 2 ^ 6 by rw [← pow_add],
          ENNReal.inv_mul_cancel_left (by simp) (by simp)]

private theorem x25519_keyToBytes32_encPtReal (k : BitVec 256) (Q : Pt25519) :
    x25519 (HMAC.keyToBytes32 k) (encPtReal Q) = encPtReal (dhReal.dh k Q) := by
  by_cases hQ : Q = 0
  · subst hQ
    have hz0 : encPtReal 0 = natToLeBytes 32 0 := by
      unfold encPtReal ptToBvReal
      change encPt255 0#255 = natToLeBytes 32 0
      exact encPt255_ofNat_of_lt (by decide : 0 < 2 ^ 255)
    rw [dhReal_zero, hz0]
    unfold x25519
    rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, x25519Ladder_zero]
  · have hQd_ne : dhReal.dh k Q ≠ 0 := dhReal_ne_zero k Q hQ
    rw [encPtReal_eq_natToLeBytes_of_ne_zero hQ, encPtReal_eq_natToLeBytes_of_ne_zero hQd_ne]
    unfold x25519
    rw [← x25519Ladder_mod,
        decodeU255_natToLeBytes_edToMontU (edNatSmul Q.val edBasepoint),
        x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 _)
          (edOnCurve_edNatSmul Q.val edOnCurve_edBasepoint),
        ← edNatSmul_mul (VerifiedLibraries.Common.clampScalar (HMAC.keyToBytes32 k))
            Q.val edOnCurve_edBasepoint]
    apply congrArg (natToLeBytes 32)
    let c := clampedScalarZMod (word256ToBytes k)
    let z : ZMod l25519 := c * (Q.val : ZMod l25519)
    have hz_ne : z ≠ 0 := mul_ne_zero (clampedScalarZMod_ne_zero _) (pt25519_cast_ne_0 hQ)
    have hmod_prod :
        (VerifiedLibraries.Common.clampScalar (HMAC.keyToBytes32 k) * Q.val) % edOrderL = z.val := by
      have hQ_mod : Q.val % edOrderL = Q.val :=
        Nat.mod_eq_of_lt (by rw [edOrderL_eq_l25519_r]; exact pt25519_val_lt_l Q)
      rw [Nat.mul_mod, clampScalar_keyToBytes32_mod_edOrderL k, hQ_mod, edOrderL_eq_l25519_r]
      have hQv : Q.val = (Q.val : ZMod l25519).val :=
        (ZMod.val_natCast_of_lt (pt25519_val_lt_l Q)).symm
      rw [hQv, ← ZMod.val_mul]
    rw [edNatSmul_mod_edOrderL_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r,
        hmod_prod]
    let Qd := dhReal.dh k Q
    have habs_Qd : absZMod (Qd.val : ZMod l25519) = absZMod z :=
      (absZMod_pt25519_cast_r Qd).trans (dhReal_dh_val k Q)
    have hpm : z = (Qd.val : ZMod l25519) ∨ z = -(Qd.val : ZMod l25519) :=
      (absZMod_eq_iff z (Qd.val : ZMod l25519)).mp habs_Qd.symm
    have hQd_v : (Qd.val : ZMod l25519).val = Qd.val :=
      ZMod.val_natCast_of_lt (pt25519_val_lt_l Qd)
    rw [← hQd_v]
    exact (edToMontU_edNatSmul_eq_iff_s edOnCurve_edBasepoint edBasepoint_ne_edZero
      edNatSmul_edOrderL_edBasepoint_r hz_ne (pt25519_cast_ne_0 hQd_ne)).mpr hpm

private theorem word256ToBytes_clamp256_real (k : BitVec 256) :
    word256ToBytes (clamp256 k) = clampScalar25519 (word256ToBytes k) := by
  have h1 : u8Vec 32 (word256ToBytes (clamp256 k)) =
      u8Vec 32 (clampScalar25519 (word256ToBytes k)) := by
    rw [u8Vec_word256ToBytes, ← clampScalar_keyVec,
        ← u8Vec_word256ToBytes, u8Vec_clampScalar25519]
  have h2 := congrArg vecU8 h1
  rwa [vecU8_u8Vec_of_length _ (length_word256ToBytes _),
       vecU8_u8Vec_of_length _ (clampScalar25519_length _)] at h2

/-- `cReal` (`X = x25519Ref`, `pubKey = x25519PubFromSecretRef`) realizes `dhReal` on `Pt25519`. -/
theorem libX25519Rel_cReal : X25519RealizesDh cReal dhReal encPtReal encTReal := by
  have henc_len : ∀ Q : Pt25519, (encPtReal Q).length = 32 :=
    fun Q => by unfold encPtReal; exact encPt255_length (ptToBvReal Q)
  have henc_zero : encPtReal 0 = List.replicate 32 0#8 := by
    unfold encPtReal ptToBvReal; exact encPt255_zero
  have henc_base : encPtReal dhReal.base = x25519Base := by
    rw [encPtReal_eq_natToLeBytes_of_ne_zero baseReal_ne_zero]
    unfold dhReal baseReal
    dsimp only []
    rw [edNatSmul_one edOnCurve_edBasepoint, edToMontU_edBasepoint]
    decide
  have hbase_eq_pt : x25519Basepoint = encPtReal dhReal.base := by
    rw [henc_base]; decide
  refine ⟨?_, fun Q => by unfold encTReal encPtReal; rfl⟩
  refine
    { enc_injective := encPtReal_inj
      enc_length := henc_len
      enc_zero := henc_zero
      enc_base := henc_base
      base_ne_zero := baseReal_ne_zero
      hook := fun k Q => ?_
      pubKey_hook := fun k => ?_
      dh_clamp := fun k Q => ?_
      dh_ne_zero := dhReal_ne_zero }
  · dsimp only [cReal]
    rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519Ref_toList,
        vec32_toList_r (length_keyToBytes32 k), vec32_toList_r (henc_len Q)]
    exact x25519_keyToBytes32_encPtReal k Q
  · dsimp only [cReal]
    rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList,
        vec32_toList_r (length_keyToBytes32 k)]
    unfold x25519Pubkey
    rw [hbase_eq_pt]
    exact x25519_keyToBytes32_encPtReal k dhReal.base
  · apply Fin.ext
    rw [dhReal_dh_val, dhReal_dh_val, word256ToBytes_clamp256_real, clampedScalarZMod_clamp]

/-! ## 5. `XeddsaCurveWitness` & `XeddsaCurveLaws` for `modelPrims XReal WReal` -/

private def representsEdReal (x : ZMod l25519) (pt : EdPoint) : Prop :=
  pt = edNatSmul x.val edBasepoint

private def compressEdReal (x : ZMod l25519) : List UInt8 :=
  toU8 (encodeEd (edNatSmul x.val edBasepoint))

private def edSignReal (x : ZMod l25519) : UInt8 :=
  UInt8.ofNat ((edNatSmul x.val edBasepoint).x % 2)

private theorem modelPrims_cReal_x25519Base_eq (X : UnreachedPqxdhPrimitives) (sk : List UInt8) :
    (modelPrims X WReal).x25519Base sk =
      toU8 (natToLeBytes 32 (edToMontU (edNatSmul (clampedScalarZMod sk).val edBasepoint))) := by
  dsimp only [modelPrims, blockLevelPrims, WReal, cReal]
  unfold vecU8
  rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList,
      x25519Pubkey_eq_edNatSmul,
      edNatSmul_mod_edOrderL_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r,
      clampScalar_ratchet_u8Vec_mod_edOrderL sk]

private theorem edSignReal_bool (x : ZMod l25519) : edSignReal x = 0 ∨ edSignReal x = 1 := by
  unfold edSignReal
  rcases Nat.mod_two_eq_zero_or_one (edNatSmul x.val edBasepoint).x with h0 | h1
  · rw [h0]; exact Or.inl rfl
  · rw [h1]; exact Or.inr rfl

private theorem two_ne_zero_zmod_l25519 : (2 : ZMod l25519) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  have hlt : 2 < l25519 := by unfold l25519; decide
  rw [show (2 : ZMod l25519) = ((2 : ℕ) : ZMod l25519) from rfl,
      ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
  omega

private theorem edNatSmul_zmod_x_ne_zero {x : ZMod l25519} (hx : x ≠ 0) :
    (edNatSmul x.val edBasepoint).x ≠ 0 := by
  intro hx0
  have h_on := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have h20 : edNatSmul 2 (edNatSmul x.val edBasepoint) = edZero :=
    (edNatSmul_two_eq_zero_iff h_on).mpr hx0
  have h2z : edNatSmul ((2 : ZMod l25519) * x).val edBasepoint = edZero := by
    have h2v : (2 : ZMod l25519).val = 2 := by
      have hlt : 2 < l25519 := by unfold l25519; decide
      exact ZMod.val_natCast_of_lt hlt
    rw [edNatSmul_zmod_mul_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r, h2v]
    exact h20
  exact edNatSmul_ne_edZero_of_zmod_ne_zero_s edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint_r (mul_ne_zero two_ne_zero_zmod_l25519 hx) h2z

private theorem edSignReal_neg (x : ZMod l25519) (hx : x ≠ 0) :
    edSignReal (-x) = 1 - edSignReal x := by
  unfold edSignReal
  rw [edNatSmul_zmod_neg_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r x]
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have hQx_lt : Q.x < p25519 := edOnCurve_x_lt hQ_on
  have hQx_ne : Q.x ≠ 0 := edNatSmul_zmod_x_ne_zero hx
  have hQx_mod : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQx_lt]; exact hQx_ne
  dsimp only [edNeg]
  rw [fpNeg_mod_two_of_ne_zero hQx_mod, Nat.mod_eq_of_lt hQx_lt]
  rcases Nat.mod_two_eq_zero_or_one Q.x with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

private theorem compressEdReal_eq_bytesOfNatLE (x : ZMod l25519) :
    let Q := edNatSmul x.val edBasepoint
    compressEdReal x = bytesOfNatLE 32 (Q.y + (Q.x % 2) * 2 ^ 255) := by
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  unfold compressEdReal encodeEd
  dsimp only []
  rw [Nat.mod_eq_of_lt (edOnCurve_x_lt hQ_on), Nat.mod_eq_of_lt (edOnCurve_y_lt hQ_on),
      toU8_natToLeBytes]

private theorem compressEdReal_signBit_and_clear (x : ZMod l25519) :
    ((compressEdReal x).getD 31 0 &&& 0x80) >>> 7 = edSignReal x ∧
      clearSignBit32 (compressEdReal x) = toU8 (natToLeBytes 32 (edNatSmul x.val edBasepoint).y) := by
  set Q := edNatSmul x.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul x.val edOnCurve_edBasepoint
  have hy_lt : Q.y < p25519 := edOnCurve_y_lt hQ_on
  have hy_255 : Q.y < 2 ^ 255 := lt_trans hy_lt p25519_lt_two_pow_255_real
  have h255 : 2 ^ 255 = 128 * 256 ^ 31 := by decide
  have hy_div_lt : Q.y / 256 ^ 31 < 128 := by omega
  set s := Q.x % 2
  have hs_lt : s < 2 := Nat.mod_lt Q.x (by decide)
  let n := Q.y + s * 2 ^ 255
  have hn_lt : n < 256 ^ 32 := by
    have h256 : 256 ^ 32 = 256 * 256 ^ 31 := by decide
    omega
  have hc_eq : compressEdReal x = bytesOfNatLE 32 n := compressEdReal_eq_bytesOfNatLE x
  have htake31 : (bytesOfNatLE 32 n).take 31 = (bytesOfNatLE 32 Q.y).take 31 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    have hi31 : i < 31 := by simp at hi1; exact hi1
    have h1 := getD_toNat_eq_div_mod (bytesOfNatLE 32 n) i
    have h2 := getD_toNat_eq_div_mod (bytesOfNatLE 32 Q.y) i
    rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt hn_lt] at h1
    rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega : Q.y < 256 ^ 32)] at h2
    have hpow_dvd : 256 ^ i * 256 ∣ 2 ^ 255 := by
      rw [h255]
      have heq : 31 = (i + 1) + (30 - i) := by omega
      rw [heq, Nat.pow_add, Nat.pow_succ]
      exact Nat.dvd_trans (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ 128)
    rcases hpow_dvd with ⟨m, hm⟩
    have hdiv_mod : (n / 256 ^ i) % 256 = (Q.y / 256 ^ i) % 256 := by
      dsimp only [n]
      have hrw : Q.y + s * 2 ^ 255 = Q.y + 256 ^ i * (256 * (s * m)) := by rw [hm]; ring
      rw [hrw, Nat.add_mul_div_left _ _ (by positivity : 0 < 256 ^ i), Nat.add_mul_mod_self_left]
    rw [List.getElem_take, List.getElem_take]
    apply UInt8.toNat_inj.mp
    have hg1 : ((bytesOfNatLE 32 n)[i]'(by simp; omega)).toNat = (n / 256 ^ i) % 256 := by
      rw [← h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
    have hg2 : ((bytesOfNatLE 32 Q.y)[i]'(by simp; omega)).toNat = (Q.y / 256 ^ i) % 256 := by
      rw [← h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
    exact hg1.trans (hdiv_mod.trans hg2.symm)
  have hb31_n : ((bytesOfNatLE 32 n).getD 31 0).toNat = Q.y / 256 ^ 31 + s * 128 := by
    rw [getD_toNat_eq_div_mod, natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt hn_lt]
    dsimp only [n]
    have hrw : Q.y + s * 2 ^ 255 = Q.y + 256 ^ 31 * (s * 128) := by rw [h255]; ring
    rw [hrw, Nat.add_mul_div_left _ _ (by decide : 0 < 256 ^ 31),
        Nat.mod_eq_of_lt (by omega : Q.y / 256 ^ 31 + s * 128 < 256)]
  have hb31_y : ((bytesOfNatLE 32 Q.y).getD 31 0).toNat = Q.y / 256 ^ 31 := by
    rw [getD_toNat_eq_div_mod, natOfBytesLE_bytesOfNatLE,
        Nat.mod_eq_of_lt (by omega : Q.y < 256 ^ 32),
        Nat.mod_eq_of_lt (by omega : Q.y / 256 ^ 31 < 256)]
  have hbit_and_clear :
      ∀ (lo : Fin 128) (sg : Fin 2),
        ((UInt8.ofNat (lo.val + sg.val * 128) &&& 0x80) >>> 7) = UInt8.ofNat sg.val ∧
        (UInt8.ofNat (lo.val + sg.val * 128) &&& 0x7F) = UInt8.ofNat lo.val := by
    decide
  have hui8 : UInt8.size = 256 := rfl
  have hb31_eq_ofNat : (bytesOfNatLE 32 n).getD 31 0 = UInt8.ofNat (Q.y / 256 ^ 31 + s * 128) := by
    apply UInt8.toNat_inj.mp
    rw [hb31_n, UInt8.toNat_ofNat_of_lt' (by omega : Q.y / 256 ^ 31 + s * 128 < UInt8.size)]
  have hy31_eq_ofNat : (bytesOfNatLE 32 Q.y).getD 31 0 = UInt8.ofNat (Q.y / 256 ^ 31) := by
    apply UInt8.toNat_inj.mp
    rw [hb31_y, UInt8.toNat_ofNat_of_lt' (by omega : Q.y / 256 ^ 31 < UInt8.size)]
  obtain ⟨hbit, hclr⟩ := hbit_and_clear ⟨Q.y / 256 ^ 31, hy_div_lt⟩ ⟨s, hs_lt⟩
  constructor
  · rw [hc_eq, hb31_eq_ofNat]
    exact hbit
  · unfold clearSignBit32
    rw [hc_eq, htake31, hb31_eq_ofNat, hclr, ← hy31_eq_ofNat,
        list32_take31_append_getD31 (bytesOfNatLE_length 32 Q.y), toU8_natToLeBytes]

section MontToEdwardsEq
attribute [local irreducible] fpAdd fpSub fpMul fpNeg

private theorem x25519Ref_decodeU255_eq_curveSpecs (bs : List (BitVec 8)) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs =
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.decodeU255 bs := by
  unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.decodeU255
  rfl

private theorem x25519Ref_montToEdwards_eq_curveSpecs (bs : List (BitVec 8)) (sign : Nat) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs sign =
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.montToEdwards bs sign := by
  unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.montToEdwards
  rw [x25519Ref_decodeU255_eq_curveSpecs]
  rfl

private theorem montToEdwards_congr_mod_p {bs1 bs2 : List (BitVec 8)}
    (hu : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs1 % p25519 =
          LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs2 % p25519) :
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs1 0 =
      LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs2 0 := by
  unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
  rw [hu]

end MontToEdwardsEq

private theorem montToEdwards_edToMontU_even_r {A : EdPoint}
    (hA : edOnCurve A = true) (hne : A ≠ edZero) :
    let vA : List.Vector (BitVec 8) 32 := ⟨natToLeBytes 32 (edToMontU A), natToLeBytes_len 32 _⟩
    montLiftEd vA 0#8 =
      some (if A.x % 2 == 1 then edNeg A else A) := by
  dsimp only []
  let vA : List.Vector (BitVec 8) 32 := ⟨natToLeBytes 32 (edToMontU A), natToLeBytes_len 32 _⟩
  rw [montLiftEd_eq_montToEdwards vA 0#8]
  change LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.montToEdwards
    (natToLeBytes 32 (edToMontU A)) 0 = _
  rw [← x25519Ref_montToEdwards_eq_curveSpecs]
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
    rwa [edToMontU_edNeg_s hA, hneg_even] at hm

private theorem decodeScalarBytes_fitBytesRef_encodeScalarBytes (x : ZMod l25519) :
    decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes x)) = x := by
  unfold fitBytesRef decodeScalarBytes
  rw [encodeScalarBytes_length]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil,
    List.take_of_length_le (Nat.le_of_eq (encodeScalarBytes_length x)),
    natOfBytesLE_encodeScalarBytes]
  exact ZMod.natCast_zmod_val x

private theorem xeddsaReal_dsmb_represents (X : UnreachedPqxdhPrimitives)
    (h : ZMod l25519) {y : ZMod l25519} {pt : EdPoint} (s : ZMod l25519)
    (hpt : representsEdReal y pt) :
    representsEdReal (h * y + s)
      ((modelPrims X WReal).doubleScalarMulBasepoint (encodeScalarBytes h) pt (encodeScalarBytes s)) := by
  unfold representsEdReal at hpt ⊢
  dsimp only [modelPrims, blockLevelPrims]
  have hh_nat : leBytesToNat (u8Vec 32 (encodeScalarBytes h)).toList = h.val := by
    rw [u8Vec_toList_of_length (encodeScalarBytes_length h), leBytesToNat_ofU8,
        natOfBytesLE_encodeScalarBytes]
  have hs_nat : leBytesToNat (u8Vec 32 (encodeScalarBytes s)).toList = s.val := by
    rw [u8Vec_toList_of_length (encodeScalarBytes_length s), leBytesToNat_ofU8,
        natOfBytesLE_encodeScalarBytes]
  have hh_lt : h.val < 2 ^ 256 :=
    lt_trans h.val_lt (by rw [← edOrderL_eq_l25519_r]; exact edOrderL_lt_two_pow_256)
  have hs_lt : s.val < 2 ^ 256 :=
    lt_trans s.val_lt (by rw [← edOrderL_eq_l25519_r]; exact edOrderL_lt_two_pow_256)
  rw [hh_nat, hs_nat, hpt,
      edSmul_eq_edNatSmul hh_lt (edOnCurve_edNatSmul y.val edOnCurve_edBasepoint),
      edSmul_eq_edNatSmul hs_lt edOnCurve_edBasepoint,
      ← edNatSmul_zmod_mul_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r h y,
      ← edNatSmul_add (h * y).val s.val edOnCurve_edBasepoint,
      edNatSmul_mod_edOrderL_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r,
      edOrderL_eq_l25519_r, ← ZMod.val_add]

private theorem compressEdReal_inj : Function.Injective compressEdReal := by
  intro x1 x2 h
  have hbv : encodeEd (edNatSmul x1.val edBasepoint) =
      encodeEd (edNatSmul x2.val edBasepoint) := by
    unfold compressEdReal at h
    have h1 := congrArg ofU8 h
    rwa [ofU8_toU8, ofU8_toU8] at h1
  have hdec := congrArg decodeEdRfc hbv
  rw [decodeEdRfc_encodeEd (edOnCurve_edNatSmul x1.val edOnCurve_edBasepoint),
      decodeEdRfc_encodeEd (edOnCurve_edNatSmul x2.val edOnCurve_edBasepoint)] at hdec
  exact edNatSmul_zmod_inj_s edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint_r (Option.some.inj hdec)

private theorem compressEdReal_inRange (x : ZMod l25519) :
    scalarIsInRange (clearSignBit32 (compressEdReal x)) = true := by
  rw [(compressEdReal_signBit_and_clear x).2]
  have hy_lt : (edNatSmul x.val edBasepoint).y < p25519 :=
    edOnCurve_y_lt (edOnCurve_edNatSmul x.val edOnCurve_edBasepoint)
  have hy_255 : (edNatSmul x.val edBasepoint).y < 2 ^ 255 :=
    lt_trans hy_lt p25519_lt_two_pow_255_real
  rw [← encPt255_ofNat_of_lt hy_255, scalarIsInRange_encPt255_iff,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy_255]
  exact hy_lt

private theorem xeddsaReal_montToEd_base (X : UnreachedPqxdhPrimitives)
    (sk : List UInt8) (b : UInt8) (hb : b = 0 ∨ b = 1) :
    ∃ pt, (modelPrims X WReal).montToEd ((modelPrims X WReal).x25519Base sk) b = some pt ∧
      representsEdReal
        (if b == edSignReal (clampedScalarZMod sk) then clampedScalarZMod sk
         else -clampedScalarZMod sk) pt := by
  set a := clampedScalarZMod sk
  have ha_ne : a ≠ 0 := clampedScalarZMod_ne_zero sk
  set Q := edNatSmul a.val edBasepoint
  have hQ_on : edOnCurve Q = true := edOnCurve_edNatSmul a.val edOnCurve_edBasepoint
  have hQ_ne : Q ≠ edZero := edNatSmul_ne_edZero_of_zmod_ne_zero_s edOnCurve_edBasepoint
    edBasepoint_ne_edZero edNatSmul_edOrderL_edBasepoint_r ha_ne
  have hbase := modelPrims_cReal_x25519Base_eq X sk
  let vBase : List.Vector (BitVec 8) 32 := ⟨natToLeBytes 32 (edToMontU Q), natToLeBytes_len 32 _⟩
  have hu8_eq : u8Vec 32 ((modelPrims X WReal).x25519Base sk) = vBase := by
    apply List.Vector.eq
    change (u8Vec 32 ((modelPrims X WReal).x25519Base sk)).toList = natToLeBytes 32 (edToMontU Q)
    rw [hbase, u8Vec_toList_of_length (by rw [toU8_length, natToLeBytes_len]), ofU8_toU8]
  have hlift0 : montLiftEd vBase 0#8 = some (if Q.x % 2 == 1 then edNeg Q else Q) :=
    montToEdwards_edToMontU_even_r hQ_on hQ_ne
  change ∃ pt : EdPoint,
    SignalPqxdh.montLiftEd (u8Vec 32 ((modelPrims X WReal).x25519Base sk)).toList b.toBitVec =
      some pt ∧ _
  rw [signalMontLiftEd_eq, hu8_eq]
  have hneg_rep : representsEdReal (-a) (edNeg Q) := by
    unfold representsEdReal
    exact (edNatSmul_zmod_neg_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r a).symm
  have hsign0 : Q.x % 2 = 0 → edSignReal a = 0 := fun hx0 => by
    unfold edSignReal; change UInt8.ofNat (Q.x % 2) = 0; rw [hx0]; rfl
  have hsign1 : Q.x % 2 = 1 → edSignReal a = 1 := fun hx1 => by
    unfold edSignReal; change UInt8.ofNat (Q.x % 2) = 1; rw [hx1]; rfl
  rcases hb with rfl | rfl
  · have hb0 : (0 : UInt8).toBitVec = 0#8 := rfl
    rw [hb0, hlift0]
    refine ⟨if Q.x % 2 == 1 then edNeg Q else Q, rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one Q.x with hx0 | hx1
    · rw [hsign0 hx0, hx0]
      rfl
    · rw [hsign1 hx1, hx1]
      exact hneg_rep
  · have hb1 : (1 : UInt8).toBitVec = 1#8 := rfl
    have hlift1 : montLiftEd vBase 1#8 =
        some (edNeg (if Q.x % 2 == 1 then edNeg Q else Q)) :=
      montLiftEd_odd_eq_edNeg_of_even rfl rfl rfl hlift0
    rw [hb1, hlift1]
    refine ⟨edNeg (if Q.x % 2 == 1 then edNeg Q else Q), rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one Q.x with hx0 | hx1
    · rw [hsign0 hx0, hx0]
      exact hneg_rep
    · rw [hsign1 hx1, hx1]
      simp only [beq_self_eq_true, ↓reduceIte, edNeg_edNeg hQ_on]
      rfl

/-- Concrete `XeddsaCurveWitness` on `modelPrims X WReal` for any `X` sharing `XReal_pre`'s
`scalarAdd` and `scalarMul` over `ZMod l25519`. -/
def xeddsaCurveWitness_modelPrimsReal_of (X : UnreachedPqxdhPrimitives)
    (hAdd : X.scalarAdd = XReal_pre.scalarAdd)
    (hMul : X.scalarMul = XReal_pre.scalarMul) :
    XeddsaCurveWitness (modelPrims X WReal) where
  x25519Base_len := fun sk => by
    rw [modelPrims_cReal_x25519Base_eq, toU8_length, natToLeBytes_len]
  scalarMod_eq := fun bs => by
    dsimp only [modelPrims, blockLevelPrims]
    rw [u8Vec_toList_eq_ofU8_fitBytesRef, leBytesToNat_ofU8, edOrderL_eq_l25519_r,
        toU8_natToLeBytes]
    unfold encodeScalarBytes decodeScalarBytes
    rw [ZMod.val_natCast]
  scalarWide_eq := fun w => by
    dsimp only [modelPrims, blockLevelPrims]
    rw [u8Vec_toList_eq_ofU8_fitBytesRef, leBytesToNat_ofU8, edOrderL_eq_l25519_r,
        toU8_natToLeBytes]
    unfold encodeScalarBytes decodeScalarBytes
    rw [ZMod.val_natCast]
  scalarAdd_eq := fun x y => by
    change X.scalarAdd (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x + y)
    rw [hAdd]
    dsimp only [XReal_pre]
    rw [decodeScalarBytes_fitBytesRef_encodeScalarBytes,
        decodeScalarBytes_fitBytesRef_encodeScalarBytes]
  scalarMul_eq := fun x y => by
    change X.scalarMul (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x * y)
    rw [hMul]
    dsimp only [XReal_pre]
    rw [decodeScalarBytes_fitBytesRef_encodeScalarBytes,
        decodeScalarBytes_fitBytesRef_encodeScalarBytes]
  RepresentsEd := representsEdReal
  compressEd := compressEdReal
  edSign := edSignReal
  edNeg_represents := fun {x pt} hpt => by
    unfold representsEdReal at hpt ⊢
    dsimp only [modelPrims, blockLevelPrims]
    rw [hpt, ← edNatSmul_zmod_neg_s edOnCurve_edBasepoint edNatSmul_edOrderL_edBasepoint_r x]
  dsmb_represents := xeddsaReal_dsmb_represents X
  compress_of_represents := fun {_ _} hpt => by
    unfold representsEdReal at hpt
    subst hpt
    rfl
  compressEd_inj := compressEdReal_inj
  compressEd_len := fun x => by
    unfold compressEdReal
    rw [toU8_length, encodeEd_length]
  compressEd_inRange := compressEdReal_inRange
  edSign_bool := edSignReal_bool
  edSign_neg := edSignReal_neg
  compressEd_signBit := fun x => (compressEdReal_signBit_and_clear x).1
  montToEd_base := xeddsaReal_montToEd_base X
  x25519Base_eq_of_clamped_pm := fun u1 u2 hpm => by
    rw [modelPrims_cReal_x25519Base_eq, modelPrims_cReal_x25519Base_eq]
    have hu := (edToMontU_edNatSmul_eq_iff_s edOnCurve_edBasepoint edBasepoint_ne_edZero
      edNatSmul_edOrderL_edBasepoint_r (clampedScalarZMod_ne_zero u1)
      (clampedScalarZMod_ne_zero u2)).mpr hpm
    rw [hu]

/-- Concrete `XeddsaCurveWitness` for `modelPrims XReal WReal`. -/
def xeddsaCurveWitness_modelPrimsReal :
    XeddsaCurveWitness (modelPrims XReal WReal) :=
  xeddsaCurveWitness_modelPrimsReal_of XReal rfl rfl

/-- `XeddsaCurveLaws` holds on `modelPrims XReal WReal`. -/
theorem xeddsaCurveLaws_modelPrimsReal : XeddsaCurveLaws (modelPrims XReal WReal) :=
  ⟨xeddsaCurveWitness_modelPrimsReal⟩

/-! ## 6. `pow8Real` Subgroup Projection Laws & `ModelPrimsCryptoAssumptions XReal WReal` -/

private theorem eEd_lt_two_pow_255 : eEd < 2 ^ 255 := by
  unfold eEd edOrderL; decide

private theorem eTw_lt_two_pow_255 : eTw < 2 ^ 255 := by
  unfold eTw twistOrderL; decide

private def qEd : Nat := ((3 * edOrderL + 1) / 8) * 3
private def qTw : Nat := ((3 * twistOrderL + 1) / 4) * 3

private theorem eEd_div_eight : eEd = 8 * ((3 * edOrderL + 1) / 8) := by
  unfold eEd edOrderL; decide

private theorem eTw_div_four : eTw = 4 * ((3 * twistOrderL + 1) / 4) := by
  unfold eTw twistOrderL; decide

private theorem eEd_sq_eq : eEd * eEd = qEd * (8 * edOrderL) + eEd := by
  unfold eEd qEd edOrderL; decide

private theorem eTw_sq_eq : eTw * eTw = qTw * (4 * twistOrderL) + eTw := by
  unfold eTw qTw twistOrderL; decide

attribute [local irreducible]
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
  LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.montToEdwards

private theorem montToEdwards_isSome_of_edOnCurve {P : EdPoint}
    (hP : edOnCurve P = true) (hne : P ≠ edZero) :
    (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 (edToMontU P)) 0).isSome = true := by
  let vP : List.Vector (BitVec 8) 32 := ⟨natToLeBytes 32 (edToMontU P), natToLeBytes_len 32 _⟩
  have hm : montLiftEd vP 0#8 = some (if P.x % 2 == 1 then edNeg P else P) :=
    montToEdwards_edToMontU_even_r hP hne
  rw [montLiftEd_eq_montToEdwards vP 0#8] at hm
  change (LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.montToEdwards
    (natToLeBytes 32 (edToMontU P)) 0) = _ at hm
  rw [x25519Ref_montToEdwards_eq_curveSpecs, hm]
  rfl

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

private theorem pow8Real_natToLeBytes_zero :
    pow8Real (toU8 (natToLeBytes 32 0)) = toU8 (natToLeBytes 32 0) := by
  unfold pow8Real
  have hlen : (toU8 (natToLeBytes 32 0)).length == 32 := by
    rw [toU8_length, natToLeBytes_len]; rfl
  rw [hlen]; simp only [↓reduceIte, ofU8_toU8]
  rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, x25519Ladder_zero]

private theorem pow8Real_len (pk : List UInt8) : (pow8Real pk).length = 32 := by
  unfold pow8Real
  split
  · rw [toU8_length, natToLeBytes_len]
  · simp

/-- Three-way structural characterization of `pow8Real pk` on 32-byte inputs:
simultaneously evaluates `pow8Real pk = toU8 (natToLeBytes 32 u)` with `u < p25519` into
(Z) `u = 0`, (E) a non-2-torsion `edOrderL`-torsion point on $E(\mathbb{F}_p)$, or
(T) a non-2-torsion `twistOrderL`-torsion point on $E_{\text{twist}}(\mathbb{F}_p)$, and proves
both `pow8Real (pow8Real pk) = pow8Real pk` and `x25519 s (ofU8 (pow8Real pk)) = x25519 s (ofU8 pk)`. -/
private theorem pow8Real_spec_32 {pk : List UInt8} (hpk : pk.length = 32) :
    ∃ u : Nat,
      u < p25519 ∧
      pow8Real pk = toU8 (natToLeBytes 32 u) ∧
      pow8Real (pow8Real pk) = pow8Real pk ∧
      (∀ s : List (BitVec 8), x25519 s (natToLeBytes 32 u) = x25519 s (ofU8 pk)) ∧
      (u = 0 ∨
       (∃ Q : EdPoint, edOnCurve Q = true ∧ Q.x ≠ 0 ∧ edNatSmul edOrderL Q = edZero ∧
         edToMontU Q = u) ∨
       (∃ Q : EdPoint, twOnCurve Q = true ∧ Q.x ≠ 0 ∧ twNatSmul twistOrderL Q = twZero ∧
         twToMontU Q = u)) := by
  let bs := ofU8 pk
  let u1 := LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 bs % p25519
  have hu1_lt : u1 < p25519 := Nat.mod_lt _ p25519_pos
  have hp8_eq : pow8Real pk = toU8 (natToLeBytes 32
      (x25519Ladder
        (match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards bs 0 with
         | some _ => eEd | none => eTw) u1)) := by
    unfold pow8Real
    rw [beq_iff_eq.mpr hpk]; simp only [↓reduceIte]
    rw [x25519Ladder_mod]
  by_cases hu0 : u1 = 0
  · refine ⟨0, p25519_pos, ?_, ?_, ?_, Or.inl rfl⟩
    · rw [hp8_eq, hu0, x25519Ladder_zero]
    · rw [hp8_eq, hu0, x25519Ladder_zero, pow8Real_natToLeBytes_zero]
    · intro s
      apply LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519_uCoord_congr
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
      have hp8_Q : pow8Real pk = toU8 (natToLeBytes 32 (edToMontU Q)) := by
        rw [hp8_eq, hPm, ← huP, x25519Ladder_edToMontU eEd_lt_two_pow_255 hP]
      have hx_Q : ∀ s : List (BitVec 8),
          x25519 s (natToLeBytes 32 (edToMontU Q)) = x25519 s bs := by
        intro s
        obtain ⟨m, hk, _, _⟩ := clampScalar_eight_mul s
        have hx_rhs : x25519 s bs = natToLeBytes 32 (edToMontU (edNatSmul (clampScalar s) P)) := by
          have hc := LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519_uCoord_congr
            s bs (natToLeBytes 32 (edToMontU P))
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
        · rw [hp8_Q, huQ0, pow8Real_natToLeBytes_zero]
        · intro s; rw [← huQ0]; exact hx_Q s
      · have hQ_ne0 : Q ≠ edZero := fun h0 => hQx (congrArg EdPoint.x h0)
        refine ⟨edToMontU Q, edToMontU_lt Q, hp8_Q, ?_, hx_Q,
          Or.inr (Or.inl ⟨Q, hQ_on, hQx, hQ_ord, rfl⟩)⟩
        rw [hp8_Q]
        unfold pow8Real
        have hlenQ : (toU8 (natToLeBytes 32 (edToMontU Q))).length == 32 := by
          rw [toU8_length, natToLeBytes_len]; rfl
        rw [hlenQ]; simp only [↓reduceIte, ofU8_toU8]
        obtain ⟨Qm, hQm⟩ := Option.isSome_iff_exists.mp (montToEdwards_isSome_of_edOnCurve hQ_on hQ_ne0)
        rw [hQm, decodeU255_natToLeBytes_of_lt_p (edToMontU_lt Q),
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
      have hp8_Q : pow8Real pk = toU8 (natToLeBytes 32 (twToMontU Q)) := by
        rw [hp8_eq, hmont_none, ← huP, x25519Ladder_twToMontU eTw_lt_two_pow_255 hP]
      have hx_Q : ∀ s : List (BitVec 8),
          x25519 s (natToLeBytes 32 (twToMontU Q)) = x25519 s bs := by
        intro s
        obtain ⟨m, hk, _, _⟩ := clampScalar_eight_mul s
        have hx_rhs : x25519 s bs = natToLeBytes 32 (twToMontU (twNatSmul (clampScalar s) P)) := by
          have hc := LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519_uCoord_congr
            s bs (natToLeBytes 32 (twToMontU P))
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
        · rw [hp8_Q, huQ0, pow8Real_natToLeBytes_zero]
        · intro s; rw [← huQ0]; exact hx_Q s
      · refine ⟨twToMontU Q, twToMontU_lt Q, hp8_Q, ?_, hx_Q,
          Or.inr (Or.inr ⟨Q, hQ_on, hQx, hQ_ord, rfl⟩)⟩
        rw [hp8_Q]
        unfold pow8Real
        have hlenQ : (toU8 (natToLeBytes 32 (twToMontU Q))).length == 32 := by
          rw [toU8_length, natToLeBytes_len]; rfl
        rw [hlenQ]; simp only [↓reduceIte, ofU8_toU8]
        rw [montToEdwards_none_of_twOnCurve hQ_on hQx,
            decodeU255_natToLeBytes_of_lt_p (twToMontU_lt Q),
            x25519Ladder_twToMontU eTw_lt_two_pow_255 hQ_on,
            ← twNatSmul_mul eTw eTw hP, eTw_sq_eq,
            twNatSmul_add _ _ hP, twNatSmul_mul qTw (4 * twistOrderL) hP,
            twNatSmul_four_mul_twistOrderL hP, twNatSmul_twZero, twZero_twAdd hQ_on]

private theorem pow8Real_idemp (pk : List UInt8) : pow8Real (pow8Real pk) = pow8Real pk := by
  by_cases hpk : pk.length = 32
  · exact (pow8Real_spec_32 hpk).choose_spec.2.2.1
  · have hp1 : pow8Real pk = toU8 (natToLeBytes 32 0) := by
      unfold pow8Real
      rw [beq_eq_false_iff_ne.mpr hpk]
      simp only [Bool.false_eq_true, ↓reduceIte]
      decide
    rw [hp1, pow8Real_natToLeBytes_zero]

private theorem modelPrims_cReal_x25519_of_len32 (X : UnreachedPqxdhPrimitives)
    (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X WReal).x25519 a pk =
      toU8 (x25519 (Ratchet.clampScalar (u8Vec 32 a)).toList (ofU8 pk)) := by
  dsimp only [modelPrims, blockLevelPrims, WReal, cReal]
  unfold vecU8
  rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519Ref_toList,
      u8Vec_toList_of_length hpk]

private theorem modelPrims_cReal_x25519_pow8Real (X : UnreachedPqxdhPrimitives)
    (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X WReal).x25519 a (pow8Real pk) = (modelPrims X WReal).x25519 a pk := by
  obtain ⟨u, _, hp8, _, hx, _⟩ := pow8Real_spec_32 hpk
  rw [modelPrims_cReal_x25519_of_len32 X a (pow8Real pk) (pow8Real_len pk),
      modelPrims_cReal_x25519_of_len32 X a pk hpk,
      hp8, ofU8_toU8, hx]

private theorem modelPrims_isCanonical_eq_isCanonicalX25519
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    (modelPrims X W).isCanonical pk = isCanonicalX25519 (ofU8 pk) := by
  rw [wr_modelPrims_isCanonical_eq]
  by_cases hlen : pk.length = 32
  · have hlen_bv : ((ofU8 pk).length == 32) = true := by rw [ofU8_length, hlen]; rfl
    have hmont_eq : montLiftEd (u8Vec 32 pk) 0#8 =
        LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0 := by
      rw [montLiftEd_eq_montToEdwards, u8Vec_toList_of_length hlen]
      exact (x25519Ref_montToEdwards_eq_curveSpecs (ofU8 pk) 0).symm
    by_cases h80 : (pk.getD 31 0 &&& 0x80) = 0
    · let w := HKDF.bytesToKey32 (ofU8 pk)
      let Q := w.truncate 255
      have hk := keyToBytes32_bytesToKey32 (ofU8 pk)
        (by rw [ofU8_length, hlen])
      have hpk_w : word256ToBytes w = pk := by
        rw [word256ToBytes_eq_toU8_keyToBytes32, hk, toU8_ofU8]
      have ht7 := word_byte_testBit w.toNat 31 7 (by decide)
      rw [← word256ToBytes_getD w 31 (by decide), hpk_w] at ht7
      have hf7 : (pk.getD 31 0).toNat.testBit 7 = false := by
        have hc : ∀ b : UInt8, (b &&& 0x80) = 0 → b.toNat.testBit 7 = false := by decide
        exact hc _ h80
      have hw255 : w.toNat.testBit 255 = false := ht7.symm.trans hf7
      have h0ext : Q.zeroExtend 256 = w := by
        apply BitVec.eq_of_toNat_eq
        have hw256 := w.isLt
        have hwt : w.toNat < 2 ^ 255 := by
          by_contra hge
          have hdiv1 : w.toNat / 2 ^ 255 = 1 := by omega
          have htb : (w.toNat / 2 ^ 255).testBit 0 = false := by
            rw [Nat.testBit_div_two_pow]; exact hw255
          rw [hdiv1] at htb
          exact Bool.noConfusion htb
        change ((w.truncate 255).setWidth 256).toNat = w.toNat
        rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt hwt, Nat.mod_eq_of_lt hw256]
      have hpk_Q : pk = toU8 (encPt255 Q) := by
        unfold encPt255
        rw [h0ext, hk, toU8_ofU8]
      have hQ_nat : Q.toNat = leBytesToNat (ofU8 pk) := by
        have h1 := congrArg (fun l => leBytesToNat (ofU8 l)) hpk_Q
        rw [ofU8_toU8, encPt255_eq_natToLeBytes,
            leBytesToNat_natToLeBytes_of_lt (lt_trans Q.isLt (by decide : 2 ^ 255 < 256 ^ 32))] at h1
        exact h1.symm
      have hsc_iff : scalarIsInRange pk = decide (leBytesToNat (ofU8 pk) < p25519) := by
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, ← hQ_nat, ← scalarIsInRange_encPt255_iff, ← hpk_Q]
      by_cases hlt : leBytesToNat (ofU8 pk) < p25519
      · have hg1 : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = true := by
          rw [beq_iff_eq.mpr hlen, beq_iff_eq.mpr h80, hsc_iff, decide_eq_true hlt]; rfl
        have hg2 : ((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) = true := by
          rw [hlen_bv, decide_eq_true hlt]; rfl
        rcases hml : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0 with _ | P
        · have hm0 : (blockLevelPrims X W).montToEd pk 0 = none := by
            rw [wr_block_montToEd_zero, hmont_eq]; exact hml
          exact (wr_isCanonicalRef_of_none _ _ hg1 hm0).trans
            (wr_isCanonicalX25519_of_none (ofU8 pk) hg2 hml).symm
        · have hm0 : (blockLevelPrims X W).montToEd pk 0 = some P := by
            rw [wr_block_montToEd_zero, hmont_eq]; exact hml
          exact ((wr_isCanonicalRef_of_some _ _ P hg1 hm0).trans
            (wr_block_isTorsionFree X W P)).trans
            (wr_isCanonicalX25519_of_some (ofU8 pk) P hg2 hml).symm
      · have hg1 : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = false := by
          rw [hsc_iff, decide_eq_false hlt, Bool.and_false]
        have hg2 : ((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) = false := by
          rw [decide_eq_false hlt, Bool.and_false]
        exact (wr_isCanonicalRef_of_false _ _ hg1).trans
          (wr_isCanonicalX25519_of_false (ofU8 pk) hg2).symm
    · have hnlt : ¬ (leBytesToNat (ofU8 pk) < p25519) := by
        intro hlt
        rw [leBytesToNat_ofU8] at hlt
        have hn255 : natOfBytesLE pk < 2 ^ 255 := lt_trans hlt p25519_lt_two_pow_255_real
        have hb31 := getD_toNat_eq_div_mod pk 31
        have hlt32 : natOfBytesLE pk < 256 ^ 32 := lt_trans hn255 (by decide)
        rw [Nat.mod_eq_of_lt (by omega)] at hb31
        have h128 : (pk.getD 31 0).toNat < 128 := by
          have h255 : 2 ^ 255 = 128 * 256 ^ 31 := by decide
          omega
        have hc : ∀ b : UInt8, b.toNat < 128 → (b &&& 0x80) = 0 := by decide
        exact h80 (hc _ h128)
      have h80b : ((pk.getD 31 0 &&& 0x80) == 0) = false := beq_eq_false_iff_ne.mpr h80
      have hg1 : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = false := by
        rw [h80b, Bool.and_false, Bool.false_and]
      have hg2 : ((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) = false := by
        rw [decide_eq_false hnlt, Bool.and_false]
      exact (wr_isCanonicalRef_of_false _ _ hg1).trans
        (wr_isCanonicalX25519_of_false (ofU8 pk) hg2).symm
  · have hlen_pk : (pk.length == 32) = false := beq_eq_false_iff_ne.mpr hlen
    have hlen_bv : ((ofU8 pk).length == 32) = false :=
      beq_eq_false_iff_ne.mpr (by rw [ofU8_length]; exact hlen)
    have hg1 : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk) = false := by
      rw [hlen_pk, Bool.false_and, Bool.false_and]
    have hg2 : ((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) = false := by
      rw [hlen_bv, Bool.false_and]
    exact (wr_isCanonicalRef_of_false _ _ hg1).trans
      (wr_isCanonicalX25519_of_false (ofU8 pk) hg2).symm

private theorem isCanonicalX25519_basepoint : isCanonicalX25519 x25519Basepoint = true := by
  unfold isCanonicalX25519 x25519Basepoint
  have h9_lt : 9 < p25519 := by unfold p25519; decide
  have h9_256 : 9 < 256 ^ 32 := by decide
  rw [natToLeBytes_len, leBytesToNat_natToLeBytes_of_lt h9_256]
  have hm : LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards
      (natToLeBytes 32 9) 0 = some edBasepoint := by
    rw [← edToMontU_edBasepoint]
    have h := montToEdwards_edToMontU edOnCurve_edBasepoint edBasepoint_ne_edZero
    have heven : edBasepoint.x % 2 = 0 := by unfold edBasepoint; decide
    rwa [heven] at h
  rw [hm]
  have hord : (edSmul edOrderL edBasepoint == edZero) = true := by
    rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint,
        edNatSmul_edOrderL_edBasepoint_r]
    rfl
  simp [h9_lt, hord]

private theorem pow8Real_of_isCanonicalX25519 {pk : List UInt8}
    (h : isCanonicalX25519 (ofU8 pk) = true) :
    pow8Real pk = pk := by
  have h1 : (((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) &&
      match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0 with
      | none => false
      | some P => edSmul edOrderL P == edZero) = true := h
  have h1a := (Bool.and_eq_true _ _).mp h1
  have h1b := (Bool.and_eq_true _ _).mp h1a.1
  have hlen_of : (ofU8 pk).length = 32 := beq_iff_eq.mp h1b.1
  have hlt_p : leBytesToNat (ofU8 pk) < p25519 := decide_eq_true_eq.mp h1b.2
  have hlen : pk.length = 32 := by simpa using hlen_of
  obtain ⟨P, hmont, hmont_cond⟩ := wr_match_edPoint_eq_true
    (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0)
    (fun P => edSmul edOrderL P == edZero) h1a.2
  rw [beq_iff_eq] at hmont_cond
  have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
  have huP : edToMontU P = leBytesToNat (ofU8 pk) := by
    have h1 := montToEdwards_some_edToMontU hmont
    unfold LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 at h1
    rw [List.take_of_length_le (Nat.le_of_eq hlen_of),
        Nat.mod_eq_of_lt (lt_trans hlt_p p25519_lt_two_pow_255_real),
        Nat.mod_eq_of_lt hlt_p] at h1
    exact h1
  unfold pow8Real
  rw [beq_iff_eq.mpr hlen]; simp only [↓reduceIte]
  rw [hmont, ← x25519Ladder_mod, ← montToEdwards_some_edToMontU hmont,
      x25519Ladder_edToMontU eEd_lt_two_pow_255 hP_on]
  have heEd_P : edNatSmul eEd P = P := by
    unfold eEd
    rw [edNatSmul_add (3 * edOrderL) 1 hP_on, edNatSmul_mul 3 edOrderL hP_on,
        hP_ord, edNatSmul_edZero, edNatSmul_one hP_on, edZero_edAdd hP_on]
  rw [heEd_P, huP, leBytesToNat_ofU8, toU8_natToLeBytes, ← hlen, bytesOfNatLE_natOfBytesLE]

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

private theorem edOnCurve_eq_or_edNeg_of_edToMontU_eq_r {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : edToMontU P = edToMontU Q) :
    P = Q ∨ P = edNeg Q := by
  have hP_ne : P ≠ edZero := fun h0 => hPx (congrArg EdPoint.x h0)
  have hQ_ne : Q ≠ edZero := fun h0 => hQx (congrArg EdPoint.x h0)
  exact LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.edPoint_eq_or_edNeg_of_edToMontU_eq
    hP hQ hP_ne hQ_ne hu

private theorem modelPrims_XReal_x25519_inj_pow8 (a pk1 pk2 : List UInt8)
    (_ha : a.length = 32) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hx : (modelPrims XReal WReal).x25519 a pk1 = (modelPrims XReal WReal).x25519 a pk2) :
    pow8Real pk1 = pow8Real pk2 := by
  obtain ⟨u1, hu1_lt, hp8_1, _, hx1, hcls1⟩ := pow8Real_spec_32 h1
  obtain ⟨u2, hu2_lt, hp8_2, _, hx2, hcls2⟩ := pow8Real_spec_32 h2
  rw [hp8_1, hp8_2]
  set s := (Ratchet.clampScalar (u8Vec 32 a)).toList
  have hxs : x25519 s (natToLeBytes 32 u1) = x25519 s (natToLeBytes 32 u2) := by
    rw [hx1, hx2]
    have hbv := congrArg ofU8 hx
    rw [modelPrims_cReal_x25519_of_len32 XReal a pk1 h1,
        modelPrims_cReal_x25519_of_len32 XReal a pk2 h2,
        ofU8_toU8, ofU8_toU8] at hbv
    exact hbv
  obtain ⟨m, hk, hm0, hm_lt⟩ := clampScalar_eight_mul s
  have hk_lt255 : clampScalar s < 2 ^ 255 := clampScalar_lt_two_pow_255 s
  have hv_eq : x25519Ladder (clampScalar s) u1 = x25519Ladder (clampScalar s) u2 := by
    unfold x25519 at hxs
    rw [decodeU255_natToLeBytes_of_lt_p hu1_lt, decodeU255_natToLeBytes_of_lt_p hu2_lt] at hxs
    have hl := congrArg leBytesToNat hxs
    have hv1 : x25519Ladder (clampScalar s) u1 < 256 ^ 32 :=
      lt_trans (fpMul_lt _ _) p25519_lt_256_pow_32
    have hv2 : x25519Ladder (clampScalar s) u2 < 256 ^ 32 :=
      lt_trans (fpMul_lt _ _) p25519_lt_256_pow_32
    rwa [leBytesToNat_natToLeBytes_of_lt hv1, leBytesToNat_natToLeBytes_of_lt hv2] at hl
  -- Helper properties for Case E and Case T under `x25519Ladder (8 * m)`:
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
  · -- Case E vs E: invert `8 * m` mod `edOrderL`
    rw [x25519Ladder_edToMontU hk_lt255 hQ1, x25519Ladder_edToMontU hk_lt255 hQ2, hk] at hv_eq
    have : Fact (Nat.Prime edOrderL) := ⟨Nat.prime_def.mpr edOrderL_prime⟩
    let cEd : ZMod edOrderL := ((8 * m : Nat) : ZMod edOrderL)
    have hcEd_ne : cEd ≠ 0 := by
      dsimp only [cEd]; rw [Nat.cast_mul]
      refine mul_ne_zero ?_ ?_
      · intro h8
        have hv := congrArg ZMod.val h8
        change ((8 : ℕ) : ZMod edOrderL).val = (0 : ZMod edOrderL).val at hv
        rw [ZMod.val_natCast_of_lt (by unfold edOrderL; decide), ZMod.val_zero] at hv
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
      rw [← edNatSmul_mul d (8 * m) hQ, edNatSmul_mod_edOrderL_s hQ hQL, hd_mod, edNatSmul_one hQ]
    rcases edOnCurve_eq_or_edNeg_of_edToMontU_eq_r
        (edOnCurve_edNatSmul _ hQ1) (edOnCurve_edNatSmul _ hQ2)
        (hEd_smul_ne hQ1 hQ1x hQ1L) (hEd_smul_ne hQ2 hQ2x hQ2L) hv_eq with hR | hRneg
    · have hQ_eq : Q1 = Q2 := by rw [← hinv_ed hQ1 hQ1L, hR, hinv_ed hQ2 hQ2L]
      rw [hQ_eq]
    · have hQ_eq : Q1 = edNeg Q2 := by
        rw [← hinv_ed hQ1 hQ1L, hRneg, edNatSmul_edNeg_all, hinv_ed hQ2 hQ2L]
      rw [hQ_eq, edToMontU_edNeg_s hQ2]
  · -- Case E vs T: impossible by Legendre symbol
    exfalso
    rw [x25519Ladder_edToMontU hk_lt255 hQ1, x25519Ladder_twToMontU hk_lt255 hQ2, hk] at hv_eq
    have hsq := edOnCurve_montRHS_isSquare (edOnCurve_edNatSmul _ hQ1) (hEd_smul_ne hQ1 hQ1x hQ1L)
    rw [hv_eq] at hsq
    exact twOnCurve_montRHS_not_isSquare (twOnCurve_twNatSmul _ hQ2)
      (hTw_smul_ne hQ2 hQ2x hQ2L) hsq
  · exfalso
    rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_zero, hk] at hv_eq
    exact hTw_smul_ne hQ1 hQ1x hQ1L
      ((twToMontU_eq_zero_iff (twOnCurve_twNatSmul _ hQ1)).mp hv_eq)
  · -- Case T vs E: impossible by Legendre symbol
    exfalso
    rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_edToMontU hk_lt255 hQ2, hk] at hv_eq
    have hsq := edOnCurve_montRHS_isSquare (edOnCurve_edNatSmul _ hQ2) (hEd_smul_ne hQ2 hQ2x hQ2L)
    rw [← hv_eq] at hsq
    exact twOnCurve_montRHS_not_isSquare (twOnCurve_twNatSmul _ hQ1)
      (hTw_smul_ne hQ1 hQ1x hQ1L) hsq
  · -- Case T vs T: invert `8 * m` mod `twistOrderL`
    rw [x25519Ladder_twToMontU hk_lt255 hQ1, x25519Ladder_twToMontU hk_lt255 hQ2, hk] at hv_eq
    have : Fact (Nat.Prime twistOrderL) := ⟨Nat.prime_def.mpr twistOrderL_prime⟩
    let cTw : ZMod twistOrderL := ((8 * m : Nat) : ZMod twistOrderL)
    have hcTw_ne : cTw ≠ 0 := by
      dsimp only [cTw]; rw [Nat.cast_mul]
      refine mul_ne_zero ?_ ?_
      · intro h8
        have hv := congrArg ZMod.val h8
        change ((8 : ℕ) : ZMod twistOrderL).val = (0 : ZMod twistOrderL).val at hv
        rw [ZMod.val_natCast_of_lt (by unfold twistOrderL; decide), ZMod.val_zero] at hv
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

private theorem modelPrims_XReal_ec_coll_bound (targetPk : List UInt8) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (XReal.pow8 ((modelPrims XReal WReal).x25519Base sk) ==
          XReal.pow8 targetPk)] {true}).toReal
        ≤ 1 / (2 : ℝ) ^ 250 := by
  have hbase_eq_dh : ∀ w : BitVec 256,
      XReal.pow8 ((modelPrims XReal WReal).x25519Base (word256ToBytes w)) =
        toU8 (encPtReal (dhReal.dh w dhReal.base)) := by
    intro w
    have hcan : isCanonicalX25519 (ofU8 ((modelPrims XReal WReal).x25519Base (word256ToBytes w))) =
        true := by
      dsimp only [modelPrims, blockLevelPrims, WReal, cReal]
      unfold vecU8
      rw [ofU8_toU8,
          LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList]
      exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint
    rw [xReal_pow8]
    change pow8Real ((modelPrims XReal WReal).x25519Base (word256ToBytes w)) = _
    rw [pow8Real_of_isCanonicalX25519 hcan]
    dsimp only [modelPrims, blockLevelPrims, WReal]
    unfold vecU8
    let kw : List.Vector (BitVec 8) 32 := ⟨HMAC.keyToBytes32 w, length_keyToBytes32 w⟩
    have hu : u8Vec 32 (word256ToBytes w) = kw := by
      apply List.Vector.eq
      change (u8Vec 32 (word256ToBytes w)).toList = HMAC.keyToBytes32 w
      rw [u8Vec_toList_of_length (length_word256ToBytes w), ofU8_word256ToBytes]
    rw [hu, pubKey_clampScalar_toList_of_libX25519Rel libX25519Rel_cReal]
    change toU8 (encPtReal (dhReal.dh (HKDF.bytesToKey32 (HMAC.keyToBytes32 w)) dhReal.base)) = _
    rw [bytesToKey32_keyToBytes32]
  let f : BitVec 256 → Bool := fun w =>
    toU8 (encPtReal (dhReal.dh w dhReal.base)) == XReal.pow8 targetPk
  have hexpr :
      (do
        let sk ← sampleScalar32
        pure (XReal.pow8 ((modelPrims XReal WReal).x25519Base sk) ==
          XReal.pow8 targetPk)) =
      (f <$> ($ᵗ BitVec 256)) := by
    simp only [sampleScalar32, sampleBytes32, bind_pure_comp, Functor.map_map, hbase_eq_dh]
    rfl
  rw [hexpr]
  refine le_trans (uniform256_map_bool_le f 64 ?_) (by norm_num)
  by_cases hne : (Finset.univ.filter (fun w : BitVec 256 => f w = true)).Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hfw0 : f w0 = true := (Finset.mem_filter.mp hw0).2
    let Qt : Pt25519 := dhReal.dh w0 dhReal.base
    have htgt : XReal.pow8 targetPk = toU8 (encPtReal Qt) := (beq_iff_eq.mp hfw0).symm
    refine le_trans (Finset.card_le_card ?_) (dhReal_base_fiber_card Qt)
    intro w hw
    have hfw : f w = true := (Finset.mem_filter.mp hw).2
    dsimp only [f] at hfw
    rw [htgt] at hfw
    have henc : encPtReal (dhReal.dh w dhReal.base) = encPtReal Qt := by
      have h1 := congrArg ofU8 (beq_iff_eq.mp hfw)
      rwa [ofU8_toU8, ofU8_toU8] at h1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, encPtReal_inj henc⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le 64

private theorem wr_modelPrims_isCanonical_congr
    (X1 X2 : UnreachedPqxdhPrimitives) (W1 W2 : PEParams) :
    (modelPrims X1 W1).isCanonical = (modelPrims X2 W2).isCanonical := by
  funext pk
  rw [modelPrims_isCanonical_eq_isCanonicalX25519, modelPrims_isCanonical_eq_isCanonicalX25519]

private theorem wr_isValidDhTripleRef_congr {B C : SignalPqxdh.Primitives}
    (hc : B.isCanonical = C.isCanonical)
    (hb : B.x25519Base = C.x25519Base)
    (hx : B.x25519 = C.x25519)
    (hp : B.pow8 = C.pow8) :
    SignalPqxdh.isValidDhTripleRef B = SignalPqxdh.isValidDhTripleRef C := by
  funext X Y Z
  unfold SignalPqxdh.isValidDhTripleRef SignalPqxdh.onCurveKey
  rw [hc, hb, hx, hp]

private theorem wr_sampleKemKeyGen_congr {B C : SignalPqxdh.Primitives}
    (h : B.kemKeyGen = C.kemKeyGen) :
    SignalPqxdh.sampleKemKeyGen B = SignalPqxdh.sampleKemKeyGen C := by
  unfold SignalPqxdh.sampleKemKeyGen
  rw [h]

/-- All 18 external cryptographic assumptions of `ModelPrimsCryptoAssumptions` hold on
`(XReal, WReal)` with real `x25519Ref`, `x25519PubFromSecretRef`, `sha512CompressState`,
`pow8Real` (`gexp_div_8`), and `xeddsaSignRef`. -/
theorem modelPrims_XReal_cryptoAssumptions : ModelPrimsCryptoAssumptions XReal WReal where
  x25519_zero_iff := fun a1 a2 pk _ _ hpk => by
    rw [modelPrims_cReal_x25519_of_len32 XReal a1 pk hpk,
        modelPrims_cReal_x25519_of_len32 XReal a2 pk hpk]
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
  canon_base := fun e _ => by
    rw [modelPrims_isCanonical_eq_isCanonicalX25519]
    change isCanonicalX25519 (ofU8 (vecU8 (x25519PubFromSecretRef (Ratchet.clampScalar (u8Vec 32 e))))) = true
    unfold vecU8
    rw [ofU8_toU8,
        LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList]
    exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint
  canon_x25519 := fun a pk _ hcan => by
    rw [modelPrims_isCanonical_eq_isCanonicalX25519] at hcan ⊢
    have hlen : pk.length = 32 := by
      unfold isCanonicalX25519 at hcan
      simp only [Bool.and_eq_true, beq_iff_eq] at hcan
      simpa using hcan.1.1
    rw [modelPrims_cReal_x25519_of_len32 XReal a pk hlen, ofU8_toU8]
    exact isCanonicalX25519_x25519 hcan
  pow8_idemp := pow8Real_idemp
  isValidDhTriple_eq_ref := fun A B Z => by
    rw [wr_isValidDhTripleRef_congr (wr_modelPrims_isCanonical_congr XReal XReal_pre WReal WReal) rfl rfl rfl]
    dsimp only [XReal]
    exact isValidDhTripleModelB_eq_ref XReal_pre WReal A B Z
  x25519_pow8_congr := fun a pk1 pk2 _ h1 h2 hpow => by
    change pow8Real pk1 = pow8Real pk2 at hpow
    rw [← modelPrims_cReal_x25519_pow8Real XReal a pk1 h1, hpow,
        modelPrims_cReal_x25519_pow8Real XReal a pk2 h2]
  x25519_congr_of_base_eq := fun a1 a2 pk _ _ hcan hbase => by
    rw [modelPrims_isCanonical_eq_isCanonicalX25519] at hcan
    have hcan1 : (((ofU8 pk).length == 32 && decide (leBytesToNat (ofU8 pk) < p25519)) &&
        match LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0 with
        | none => false
        | some P => edSmul edOrderL P == edZero) = true := hcan
    have hcan1a := (Bool.and_eq_true _ _).mp hcan1
    have hcan1b := (Bool.and_eq_true _ _).mp hcan1a.1
    have hlen_of : (ofU8 pk).length = 32 := beq_iff_eq.mp hcan1b.1
    have hpk : pk.length = 32 := by simpa using hlen_of
    obtain ⟨P, hmont, hmont_cond⟩ := wr_match_edPoint_eq_true
      (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.montToEdwards (ofU8 pk) 0)
      (fun P => edSmul edOrderL P == edZero) hcan1a.2
    rw [beq_iff_eq] at hmont_cond
    have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
    have hP_ne : P ≠ edZero := montToEdwards_some_ne_edZero hmont
    have hP_ord : edNatSmul edOrderL P = edZero :=
      (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
    have huP : edToMontU P =
        LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 (ofU8 pk) % p25519 :=
      montToEdwards_some_edToMontU hmont
    rw [modelPrims_cReal_x25519Base_eq, modelPrims_cReal_x25519Base_eq] at hbase
    have hu_base : edToMontU (edNatSmul (clampedScalarZMod a1).val edBasepoint) =
        edToMontU (edNatSmul (clampedScalarZMod a2).val edBasepoint) := by
      have hbv := congrArg (fun l => leBytesToNat (ofU8 l)) hbase
      rwa [ofU8_toU8, ofU8_toU8,
           leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32),
           leBytesToNat_natToLeBytes_of_lt (lt_trans (edToMontU_lt _) p25519_lt_256_pow_32)] at hbv
    have hpm := (edToMontU_edNatSmul_eq_iff_s edOnCurve_edBasepoint edBasepoint_ne_edZero
      edNatSmul_edOrderL_edBasepoint_r (clampedScalarZMod_ne_zero a1)
      (clampedScalarZMod_ne_zero a2)).mp hu_base
    have hu_P : edToMontU (edNatSmul (clampedScalarZMod a1).val P) =
        edToMontU (edNatSmul (clampedScalarZMod a2).val P) :=
      (edToMontU_edNatSmul_eq_iff_s hP_on hP_ne hP_ord
        (clampedScalarZMod_ne_zero a1) (clampedScalarZMod_ne_zero a2)).mpr hpm
    have hx_eval : ∀ a : List UInt8,
        (modelPrims XReal WReal).x25519 a pk =
          toU8 (natToLeBytes 32 (edToMontU (edNatSmul (clampedScalarZMod a).val P))) := by
      intro a
      rw [modelPrims_cReal_x25519_of_len32 XReal a pk hpk]
      unfold x25519
      rw [← x25519Ladder_mod, ← huP,
          x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 _) hP_on,
          edNatSmul_mod_edOrderL_s hP_on hP_ord, clampScalar_ratchet_u8Vec_mod_edOrderL a]
    rw [hx_eval a1, hx_eval a2, hu_P]
  canon_pow8_inj := fun pk1 pk2 h1 h2 hpow => by
    rw [modelPrims_isCanonical_eq_isCanonicalX25519] at h1 h2
    change pow8Real pk1 = pow8Real pk2 at hpow
    rwa [pow8Real_of_isCanonicalX25519 h1, pow8Real_of_isCanonicalX25519 h2] at hpow
  pow8_len := pow8Real_len
  ec_coll_bound := modelPrims_XReal_ec_coll_bound
  x25519_inj_pow8 := modelPrims_XReal_x25519_inj_pow8
  pow8_base_len := fun p e _ hpow => by
    change pow8Real p = pow8Real ((modelPrims XReal WReal).x25519Base e) at hpow
    by_cases hp : p.length = 32
    · exact hp
    · exfalso
      have hp0 : pow8Real p = List.replicate 32 0 := by
        unfold pow8Real; rw [beq_eq_false_iff_ne.mpr hp]; rfl
      have hcan : isCanonicalX25519 (ofU8 ((modelPrims XReal WReal).x25519Base e)) = true := by
        change isCanonicalX25519 (ofU8 (vecU8 (x25519PubFromSecretRef (Ratchet.clampScalar (u8Vec 32 e))))) = true
        unfold vecU8
        rw [ofU8_toU8,
            LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList]
        exact isCanonicalX25519_x25519 isCanonicalX25519_basepoint
      rw [hp0, pow8Real_of_isCanonicalX25519 hcan] at hpow
      change List.replicate 32 0 = vecU8 (x25519PubFromSecretRef (Ratchet.clampScalar (u8Vec 32 e))) at hpow
      unfold vecU8 at hpow
      rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.x25519PubFromSecretRef_toList] at hpow
      have hbv := congrArg ofU8 hpow
      rw [ofU8_toU8] at hbv
      have hz : ofU8 (List.replicate 32 (0 : UInt8)) = natToLeBytes 32 0 := by decide
      rw [hz] at hbv
      have hdec := congrArg
        (fun l => LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref.decodeU255 l % p25519)
        hbv.symm
      rw [decodeU255_natToLeBytes_of_lt_p p25519_pos, Nat.zero_mod] at hdec
      exact x25519Pubkey_not_lowOrder _ (hdec ▸ (by simp [lowOrderUs] : 0 ∈ lowOrderUs))
  sigPkGen_eq_x25519Base := rfl
  scalarMul_len := fun _ _ => encodeScalarBytes_length _
  scalarAdd_len := fun _ _ => encodeScalarBytes_length _
  kemKeyGen_len := fun seed => ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  sig_corr := fun sk msg r => by
    rw [modelPrims_sigVerify_eq_ref, xReal_sigSign]
    exact xeddsaSignRef_correct xeddsaCurveLaws_modelPrimsReal sk msg r
  kem_coll_bound := fun targetPk => by
    rw [wr_sampleKemKeyGen_congr (rfl : (modelPrims XReal WReal).kemKeyGen = cwfPrimitives.kemKeyGen)]
    exact cwfPrimitives_kem_coll_bound targetPk

private theorem cReal_D_E (k : BitVec 256) (x : BitVec 128) : cReal.D k (cReal.E k x) = x := rfl

private theorem encaps1Total_K255_r : Encaps1Total K255 := fun _ _ _ => rfl

private theorem bhEncaps1Total_WReal : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds WReal.Q.K :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem modelPrims_XReal_kemCorrectWith_zero :
    SignalPqxdh.KemDeltaCorrect (modelPrims XReal WReal) 0 := by
  unfold SignalPqxdh.KemDeltaCorrect
  have hCorr : ∀ seed r ss ct,
      (modelPrims XReal WReal).kemEncaps ((modelPrims XReal WReal).kemKeyGen seed).1 r =
        some (ss, ct) →
      (modelPrims XReal WReal).kemDecaps ((modelPrims XReal WReal).kemKeyGen seed).2 ct =
        some ss :=
    modelPrims_kem_corr_of_decaps XReal WReal (fun _ _ => rfl)
  simp [SignalPqxdh.kemHonestFail_eq_false_of_kem_corr hCorr]

theorem modelPrims_XReal_cwfδ :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims XReal WReal) :=
  cryptoWellFormedPrimitivesδ_modelPrims XReal WReal modelPrims_XReal_cryptoAssumptions
    dhReal_commutes libX25519Rel_cReal cReal_D_E

/-! ## 7. Joint Hypothesis Satisfiability & Instantiation at Real `x25519Ref` + `sha512CompressState` -/

/-- Joint satisfiability of all hypotheses of `SessionSecure` on `Pt25519` (`> 2 ^ 251`) with
`C.X = x25519Ref`, `C.pubKey = x25519PubFromSecretRef`, and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem session_hypotheses_satisfiable_real (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep q : ℕ)
      (oa : ProbComp Unit) (_ida _idb : Unit → IdentityKey) (_s : Unit → BitVec 256)
      (A : Unit → SM.Adversary (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
        (BitVec 512) CryptoVerification.E2E.Bytes),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      C.X = x25519Ref ∧
      C.pubKey = x25519PubFromSecretRef ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < q ∧
      Encaps1Total K ∧
      (∀ k x, C.D k (C.E k x) = x) ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      DhKerUniform Dh ∧
      2 * (q + 1) + 25002 < 2 ^ 32 ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      (∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) := by
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    cReal, K255, dhReal, encPtReal, encTReal, decTReal, 1, 1,
    pure (), (fun _ => bhIdKeyOf []), (fun _ => bhIdKeyOf []), (fun _ => 0),
    (fun _ => sessionNoopAdv ℓ), ?_⟩
  exact ⟨rfl, rfl, two_pow_251_lt_card_pt25519, by decide, encaps1Total_K255_r, cReal_D_E, hℓ,
    dhReal_commutes, libX25519Rel_cReal, decTReal_encTReal, encTReal_inj,
    encTReal_ne_dummyKey, dhReal_zero, dhReal_kerUniform,
    show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dhReal_base_fiber_prob_le, fun _ _ => trivial⟩

/-- Instantiates `SessionSecure (Pt := Pt25519) ℓ` at `cReal` (`X = x25519Ref`,
`pubKey = x25519PubFromSecretRef`) and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem sessionSecure_real_instantiable (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : SessionSecure (Pt := Pt25519) ℓ) :
    ∃ D : SessionCostedReductionFamily Pt25519 ℓ,
      SessionCostedReductionFamilyBounded ℓ D ∧
      𝒟[(pure () : ProbComp Unit) >>= fun o =>
          SM.gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr cReal (LibsignalSpqrV1.spqrV1SessionUniformCoins cReal.F K255)
                (bhIdKeyOf []) (bhIdKeyOf []))
              ℓ (0 : BitVec 256))
            3 1 (configRefuseEarlyBobCorr decTReal encTReal)
            ((fun _ : Unit => sessionNoopAdv ℓ) o)].boolBias ≤
        sessionAdvantageBound ℓ D cReal K255 dhReal encPtReal encTReal decTReal 1 1
          ((1 : ℝ≥0∞) / 2 ^ 250) (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf [])
          (fun _ => 0) (fun _ => sessionNoopAdv ℓ)
          + 2 * sessionKemFailProb cReal K255 ℓ decTReal encTReal 1 (pure ())
            (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
            (fun _ => sessionNoopAdv ℓ) := by
  rcases hSec with ⟨D, hD, hMain⟩
  exact ⟨D, hD, hMain cReal K255 dhReal encPtReal encTReal decTReal
    encaps1Total_K255_r cReal_D_E hℓ dhReal_commutes libX25519Rel_cReal
    decTReal_encTReal encTReal_ne_dummyKey dhReal_zero dhReal_kerUniform
    1 1 (by decide) ((1 : ℝ≥0∞) / 2 ^ 250) dhReal_base_fiber_prob_le
    (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
    (fun _ => sessionNoopAdv ℓ) (fun _ _ => trivial)⟩

/-- Joint satisfiability of all hypotheses of `LibsignalCliPqSecure` and the real-primitive
equations `W.C.X = x25519Ref`, `W.C.pubKey = x25519PubFromSecretRef`,
`W.Q.F512 = sha512CompressState`, `XeddsaCurveLaws (modelPrims X W)`, and
`X.sigSign = xeddsaSignRef (modelPrims X W)` with `2 ^ 251 < Fintype.card Pt`, `δ_kem = 0`,
and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem cli_pq_headline_hypotheses_satisfiable_real
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      W.C.X = x25519Ref ∧
      W.C.pubKey = x25519PubFromSecretRef ∧
      W.Q.F512 = sha512CompressState ∧
      XeddsaCurveLaws (modelPrims X W) ∧
      X.sigSign = xeddsaSignRef (modelPrims X W) ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 0, 1, 0⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := cliRoCoinDrAdv S ℓ (BitVec 512)
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    pqModelRun XReal WReal, XReal, WReal, dhReal, encPtReal, encTReal, decTReal,
    1, b1, 1, fun _ => 1, A0, ?_⟩
  exact ⟨wReal_X, wReal_pubKey, wReal_F512, xeddsaCurveLaws_modelPrimsReal, xReal_sigSign,
    two_pow_251_lt_card_pt25519, by decide, by decide,
    cliSpecPq_pqModelRun XReal WReal, bhEncaps1Total_WReal,
    modelPrims_XReal_cwfδ, modelPrims_XReal_kemCorrectWith_zero, hℓ,
    dhReal_commutes, libX25519Rel_cReal, decTReal_encTReal, encTReal_inj,
    encTReal_ne_dummyKey, dhReal_zero, cReal_D_E, dhReal_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dhReal_base_fiber_prob_le,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Closed specialization of `cli_pq_headline_hypotheses_satisfiable_real` at `N_id = 2` and
`ℓ = 32`. -/
theorem cli_pq_headline_hypotheses_satisfiable_real_concrete :
    ∃ (S : SignalPqxdh.Setup) (ℓ : ℕ)
      (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      2 ≤ S.N_id ∧ 0 < S.N_send_tot ∧ 0 < S.N_recv_tot ∧ 0 < ℓ ∧
      W.C.X = x25519Ref ∧
      W.C.pubKey = x25519PubFromSecretRef ∧
      W.Q.F512 = sha512CompressState ∧
      XeddsaCurveLaws (modelPrims X W) ∧
      X.sigSign = xeddsaSignRef (modelPrims X W) ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let S0 : SignalPqxdh.Setup := ⟨2, 1, 1, 1, 1, 1⟩
  obtain ⟨Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
      b, qStart, qs, A, hRest⟩ :=
    cli_pq_headline_hypotheses_satisfiable_real S0 32 (by decide)
  exact ⟨S0, 32, Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
    b, qStart, qs, A, by decide, by decide, by decide, by decide, hRest⟩

/-- Instantiates both advantage bounds of `LibsignalCliPqSecure (Pt := Pt25519) S ℓ` at `(XReal, WReal)`
carrying `W.C.X = x25519Ref`, `W.C.pubKey = x25519PubFromSecretRef`,
`W.Q.F512 = sha512CompressState`, and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem libsignalCliPqSecure_real_instantiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : LibsignalCliPqSecure (Pt := Pt25519) S ℓ) :
    ∃ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      W.C.X = x25519Ref ∧
      W.C.pubKey = x25519PubFromSecretRef ∧
      W.Q.F512 = sha512CompressState ∧
      CliPqxdhAdvantage S run X W ℓ qep decTReal encTReal A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0 +
          2 * CliKemFailProb S run X W ℓ qep decTReal encTReal A ∧
      CliPqxdhAdvantage S run X W ℓ qep decTReal encTReal A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 0
               (SignalPqxdh.GapSigEufCma (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X W) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (modelPrims X W).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0
          + 2 * CliKemFailProb S run X W ℓ qep decTReal encTReal A := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  rcases hMain (pqModelRun XReal WReal) XReal WReal (cliSpecPq_pqModelRun XReal WReal)
      bhEncaps1Total_WReal cReal_D_E modelPrims_XReal_cwfδ 0 modelPrims_XReal_kemCorrectWith_zero
      dhReal encPtReal encTReal decTReal 1 hℓ
      dhReal_commutes libX25519Rel_cReal decTReal_encTReal encTReal_ne_dummyKey
      dhReal_zero dhReal_kerUniform
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide)
      ((1 : ℝ≥0∞) / 2 ^ 250) dhReal_base_fiber_prob_le A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨pqModelRun XReal WReal, XReal, WReal, 1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    wReal_X, wReal_pubKey, wReal_F512, hBound1,
    hBound2 1 (SignalPqxdh.keyIndRoGap_one S (modelPrims XReal WReal) _)⟩

/-- Joint satisfiability for `CliSpecPqxdhOrExcusedAbort` carrying `W.C.X = x25519Ref`,
`W.C.pubKey = x25519PubFromSecretRef`, `W.Q.F512 = sha512CompressState`,
`XeddsaCurveLaws (modelPrims X W)`, and `X.sigSign = xeddsaSignRef (modelPrims X W)`. -/
theorem pqOom_hypotheses_satisfiable_real
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      W.C.X = x25519Ref ∧
      W.C.pubKey = x25519PubFromSecretRef ∧
      W.Q.F512 = sha512CompressState ∧
      XeddsaCurveLaws (modelPrims X W) ∧
      X.sigSign = xeddsaSignRef (modelPrims X W) ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdhOrExcusedAbort exc run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  obtain ⟨Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
      b, qStart, qs, A, hX, hPub, hF512, hLaws, hSig, hCard, hqStart, hqs0, hCli, hRest⟩ :=
    cli_pq_headline_hypotheses_satisfiable_real S ℓ hℓ
  have someIte : ∀ {α : Type} (p : Prop) [Decidable p] (a b : α),
      (if p then some a else some b) = some (if p then a else b) := by
    intro α p _ a b; by_cases hp : p <;> simp [hp]
  have someIte2 : ∀ {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b c : α),
      (if p then some a else if q then some b else some c) =
        some (if p then a else if q then b else c) := by
    intro α p q _ _ a b c; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  have hCliOom : CliSpecPqxdhOrExcusedAbort (⊥ : Inputs → Prop) run X W := by
    intro st hst
    obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hCli st hst
    exact ⟨fun b t hnone => Or.inl ⟨_, hInit b t hnone, rfl⟩,
      fun m r hm => Or.inl ⟨_, (hSend m r hm).trans (someIte2 _ _ _ _ _), rfl⟩,
      fun c rc hc => Or.inl ⟨_, (hWhisper c rc hc).trans (someIte _ _ _), rfl⟩,
      fun m rc h1 h2 => Or.inl ⟨_, (hPrekey m rc h1 h2).trans (someIte _ _ _), rfl⟩,
      fun c rc h1 h2 h3 => Or.inl ⟨_, (hBad c rc h1 h2 h3).trans (someIte _ _ _), rfl⟩⟩
  exact ⟨Pt, dPt, zPt, fPt, sPt, ⊥, run, X, W, Dh, encPt, encT, decT, qep,
    b, qStart, qs, A, hX, hPub, hF512, hLaws, hSig, hCard, hqStart, hqs0, hCliOom, hRest⟩

/-! ## 8. Full 9-Equation Placed-Headline Witness (`cReal9`, `QReal9`, `WReal9`) -/

/-- Session `Crypto` witness pinned to all 5 real `W.C` primitives (`sha256Compress`, `aes256Enc`,
`aes256Dec`, `x25519Ref`, `x25519PubFromSecretRef`). -/
@[expose] def cReal9 : Crypto :=
  { cReal with
    F := CryptoVerification.LibsignalSpqrV1.sha256Compress
    E := CryptoGames.AES256.aes256Enc
    D := CryptoGames.AES256.aes256Dec }

/-- `PqxdhPrims` witness pinned to all 4 real `W.Q` primitives (`sha512CompressState`,
`kyber1024EncapsVec`, `kyber1024DecapsVec`, `mlkem768Incremental`). -/
@[expose] noncomputable def QReal9 : PqxdhPrims :=
  Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses.withRealMlKemPrims QReal

/-- End-to-end parameter bundle `(cReal9, QReal9)` satisfying all 9 placed-headline primitive
equations simultaneously. -/
@[expose] noncomputable def WReal9 : PEParams := ⟨cReal9, QReal9⟩

theorem wReal9_F : WReal9.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress := rfl
theorem wReal9_E : WReal9.C.E = CryptoGames.AES256.aes256Enc := rfl
theorem wReal9_D : WReal9.C.D = CryptoGames.AES256.aes256Dec := rfl
theorem wReal9_X : WReal9.C.X = CryptoGames.RFC7748.x25519Ref := rfl
theorem wReal9_pubKey : WReal9.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef := rfl
theorem wReal9_F512 : WReal9.Q.F512 = CryptoGames.SHA512.sha512CompressState := rfl
theorem wReal9_encaps : WReal9.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec := rfl
theorem wReal9_decaps : WReal9.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec := rfl
theorem wReal9_K : WReal9.Q.K = CryptoGames.MLKEM.mlkem768Incremental := rfl

theorem xReal_sigSign_WReal9 : XReal.sigSign = xeddsaSignRef (modelPrims XReal WReal9) :=
  xReal_sigSign.trans
    (wr_xeddsaSignRef_modelPrims_congr XReal XReal WReal WReal9
      rfl rfl (wReal_pubKey.trans wReal9_pubKey.symm) (wReal_F512.trans wReal9_F512.symm))

theorem libX25519Rel_cReal9 : X25519RealizesDh cReal9 dhReal encPtReal encTReal :=
  ⟨{ enc_injective := libX25519Rel_cReal.1.enc_injective
     enc_length := libX25519Rel_cReal.1.enc_length
     enc_zero := libX25519Rel_cReal.1.enc_zero
     enc_base := libX25519Rel_cReal.1.enc_base
     base_ne_zero := libX25519Rel_cReal.1.base_ne_zero
     hook := libX25519Rel_cReal.1.hook
     pubKey_hook := libX25519Rel_cReal.1.pubKey_hook
     dh_clamp := libX25519Rel_cReal.1.dh_clamp
     dh_ne_zero := libX25519Rel_cReal.1.dh_ne_zero },
   libX25519Rel_cReal.2⟩

noncomputable def xeddsaCurveWitness_modelPrimsReal9 :
    XeddsaCurveWitness (modelPrims XReal WReal9) where
  x25519Base_len := xeddsaCurveWitness_modelPrimsReal.x25519Base_len
  scalarMod_eq := xeddsaCurveWitness_modelPrimsReal.scalarMod_eq
  scalarWide_eq := xeddsaCurveWitness_modelPrimsReal.scalarWide_eq
  scalarAdd_eq := xeddsaCurveWitness_modelPrimsReal.scalarAdd_eq
  scalarMul_eq := xeddsaCurveWitness_modelPrimsReal.scalarMul_eq
  RepresentsEd := xeddsaCurveWitness_modelPrimsReal.RepresentsEd
  compressEd := xeddsaCurveWitness_modelPrimsReal.compressEd
  edSign := xeddsaCurveWitness_modelPrimsReal.edSign
  edNeg_represents := xeddsaCurveWitness_modelPrimsReal.edNeg_represents
  dsmb_represents := xeddsaCurveWitness_modelPrimsReal.dsmb_represents
  compress_of_represents := xeddsaCurveWitness_modelPrimsReal.compress_of_represents
  compressEd_inj := xeddsaCurveWitness_modelPrimsReal.compressEd_inj
  compressEd_len := xeddsaCurveWitness_modelPrimsReal.compressEd_len
  compressEd_inRange := xeddsaCurveWitness_modelPrimsReal.compressEd_inRange
  edSign_bool := xeddsaCurveWitness_modelPrimsReal.edSign_bool
  edSign_neg := xeddsaCurveWitness_modelPrimsReal.edSign_neg
  compressEd_signBit := xeddsaCurveWitness_modelPrimsReal.compressEd_signBit
  montToEd_base := xeddsaCurveWitness_modelPrimsReal.montToEd_base
  x25519Base_eq_of_clamped_pm := xeddsaCurveWitness_modelPrimsReal.x25519Base_eq_of_clamped_pm

theorem xeddsaCurveLaws_modelPrimsReal9 : XeddsaCurveLaws (modelPrims XReal WReal9) :=
  ⟨xeddsaCurveWitness_modelPrimsReal9⟩

private theorem wr_modelPrims_x25519_WReal9 :
    (modelPrims XReal WReal9).x25519 = (modelPrims XReal WReal).x25519 := rfl

private theorem wr_modelPrims_x25519Base_WReal9 :
    (modelPrims XReal WReal9).x25519Base = (modelPrims XReal WReal).x25519Base := rfl

private theorem wr_modelPrims_kemKeyGen_WReal9 :
    (modelPrims XReal WReal9).kemKeyGen = (modelPrims XReal WReal).kemKeyGen := rfl

theorem modelPrims_XReal_WReal9_cryptoAssumptions : ModelPrimsCryptoAssumptions XReal WReal9 where
  x25519_zero_iff := modelPrims_XReal_cryptoAssumptions.x25519_zero_iff
  canon_base := fun e he => by
    rw [wr_modelPrims_isCanonical_congr XReal XReal WReal9 WReal, wr_modelPrims_x25519Base_WReal9]
    exact modelPrims_XReal_cryptoAssumptions.canon_base e he
  canon_x25519 := fun a pk ha hc => by
    rw [wr_modelPrims_isCanonical_congr XReal XReal WReal9 WReal] at hc ⊢
    rw [wr_modelPrims_x25519_WReal9]
    exact modelPrims_XReal_cryptoAssumptions.canon_x25519 a pk ha hc
  pow8_idemp := modelPrims_XReal_cryptoAssumptions.pow8_idemp
  isValidDhTriple_eq_ref := fun A B Z => by
    rw [wr_isValidDhTripleRef_congr
      (wr_modelPrims_isCanonical_congr XReal XReal WReal9 WReal)
      wr_modelPrims_x25519Base_WReal9 wr_modelPrims_x25519_WReal9 rfl]
    exact modelPrims_XReal_cryptoAssumptions.isValidDhTriple_eq_ref A B Z
  x25519_pow8_congr := modelPrims_XReal_cryptoAssumptions.x25519_pow8_congr
  x25519_congr_of_base_eq := fun a1 a2 pk ha1 ha2 hc hb => by
    rw [wr_modelPrims_isCanonical_congr XReal XReal WReal9 WReal] at hc
    rw [wr_modelPrims_x25519Base_WReal9] at hb
    rw [wr_modelPrims_x25519_WReal9]
    exact modelPrims_XReal_cryptoAssumptions.x25519_congr_of_base_eq a1 a2 pk ha1 ha2 hc hb
  canon_pow8_inj := fun pk1 pk2 h1 h2 hp => by
    rw [wr_modelPrims_isCanonical_congr XReal XReal WReal9 WReal] at h1 h2
    exact modelPrims_XReal_cryptoAssumptions.canon_pow8_inj pk1 pk2 h1 h2 hp
  pow8_len := modelPrims_XReal_cryptoAssumptions.pow8_len
  ec_coll_bound := modelPrims_XReal_cryptoAssumptions.ec_coll_bound
  x25519_inj_pow8 := modelPrims_XReal_cryptoAssumptions.x25519_inj_pow8
  pow8_base_len := modelPrims_XReal_cryptoAssumptions.pow8_base_len
  sigPkGen_eq_x25519Base := modelPrims_XReal_cryptoAssumptions.sigPkGen_eq_x25519Base
  scalarMul_len := modelPrims_XReal_cryptoAssumptions.scalarMul_len
  scalarAdd_len := modelPrims_XReal_cryptoAssumptions.scalarAdd_len
  kemKeyGen_len := modelPrims_XReal_cryptoAssumptions.kemKeyGen_len
  sig_corr := fun sk msg r => by
    rw [modelPrims_sigVerify_eq_ref, xReal_sigSign_WReal9]
    exact xeddsaSignRef_correct xeddsaCurveLaws_modelPrimsReal9 sk msg r
  kem_coll_bound := fun targetPk => by
    rw [wr_sampleKemKeyGen_congr wr_modelPrims_kemKeyGen_WReal9]
    exact modelPrims_XReal_cryptoAssumptions.kem_coll_bound targetPk

theorem cReal9_D_E (k : BitVec 256) (x : BitVec 128) : cReal9.D k (cReal9.E k x) = x :=
  LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip.aes256Dec_aes256Enc k x

theorem bhEncaps1Total_WReal9 : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds WReal9.Q.K :=
  Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses.encaps1SucceedsOn64ByteHeaderAndSeeds_of_eq_mlkem768Incremental
    wReal9_K

theorem modelPrims_XReal_WReal9_kemCorrectWith_one :
    SignalPqxdh.KemDeltaCorrect (modelPrims XReal WReal9) 1 :=
  Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses.kemDeltaCorrect_one
    (modelPrims XReal WReal9)

theorem modelPrims_XReal_WReal9_cwfδ :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims XReal WReal9) :=
  cryptoWellFormedPrimitivesδ_modelPrims XReal WReal9 modelPrims_XReal_WReal9_cryptoAssumptions
    dhReal_commutes libX25519Rel_cReal9 cReal9_D_E

/-- Joint satisfiability of all hypotheses of `CliPqxdhElfSecurePlaced` and all 9
real-primitive equations (`W.C.{F, E, D, X, pubKey}` and `W.Q.{F512, encaps, decaps, K}`),
together with `XeddsaCurveLaws (modelPrims X W)` and `X.sigSign = xeddsaSignRef (modelPrims X W)`,
on `Pt25519` (`2 ^ 251 < Fintype.card Pt`), `δ_kem = 1`, and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem cli_pq_elf_placed_hypotheses_satisfiable_real_9eq
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress ∧
      W.C.E = CryptoGames.AES256.aes256Enc ∧
      W.C.D = CryptoGames.AES256.aes256Dec ∧
      W.C.X = CryptoGames.RFC7748.x25519Ref ∧
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef ∧
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState ∧
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec ∧
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec ∧
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental ∧
      XeddsaCurveLaws (modelPrims X W) ∧
      X.sigSign = xeddsaSignRef (modelPrims X W) ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 1 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 0, 1, 0⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := cliRoCoinDrAdv S ℓ (BitVec 512)
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    pqModelRun XReal WReal9, XReal, WReal9, dhReal, encPtReal, encTReal, decTReal,
    1, b1, 1, fun _ => 1, A0, ?_⟩
  exact ⟨wReal9_F, wReal9_E, wReal9_D, wReal9_X, wReal9_pubKey,
    wReal9_F512, wReal9_encaps, wReal9_decaps, wReal9_K,
    xeddsaCurveLaws_modelPrimsReal9, xReal_sigSign_WReal9,
    two_pow_251_lt_card_pt25519, by decide, by decide,
    cliSpecPq_pqModelRun XReal WReal9, bhEncaps1Total_WReal9,
    modelPrims_XReal_WReal9_cwfδ, modelPrims_XReal_WReal9_kemCorrectWith_one, hℓ,
    dhReal_commutes, libX25519Rel_cReal9, decTReal_encTReal, encTReal_inj,
    encTReal_ne_dummyKey, dhReal_zero, cReal9_D_E, dhReal_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dhReal_base_fiber_prob_le,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Instantiates both advantage bounds of the KEM-generic concrete X25519 statement
`CryptoVerification.LibsignalCli.CliPqxdhElfSecureAnyKem` at `kemKeyGen := XReal.kemKeyGen` and
`δ_kem = 1`. -/
theorem cliPqxdhElfSecure_real_9eq_instantiable
    (elf : Arm64.Process.ElfImage) (addrs : CliElfAddrs)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : CryptoVerification.LibsignalCli.CliPqxdhElfSecureAnyKem S ℓ elf addrs) :
    ∃ (kemKeyGen : List UInt8 → List UInt8 × List UInt8) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      let run := cliRunElf elf addrs
      let X := realUnreachedPrims kemKeyGen
      let Wp : PEParams := realPEParams
      CliPqxdhAdvantage S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
          CryptoGames.RFC7748.x25519EncT A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X Wp) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 1 +
          2 * CliKemFailProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
            CryptoGames.RFC7748.x25519EncT A +
          2 * CliPqxdhFlagProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
            CryptoGames.RFC7748.x25519EncT A
            (CliPqxdhExcusedAbort (CliReachesSampleNttStuckElf elf addrs) run Wp) ∧
      CliPqxdhAdvantage S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
          CryptoGames.RFC7748.x25519EncT A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 1
               (SignalPqxdh.GapSigEufCma (modelPrims X Wp) (modelPrims X Wp).isValidDhTriple
                 (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X Wp) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X Wp) (modelPrims X Wp).isValidDhTriple
                 (modelPrims X Wp).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 1
          + 2 * CliKemFailProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
              CryptoGames.RFC7748.x25519EncT A
          + 2 * CliPqxdhFlagProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
              CryptoGames.RFC7748.x25519EncT A
              (CliPqxdhExcusedAbort (CliReachesSampleNttStuckElf elf addrs) run Wp) := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  have hKemValid : ∀ seed, (XReal.kemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
      (XReal.kemKeyGen seed).2.length = 3168 :=
    modelPrims_XReal_cryptoAssumptions.kemKeyGen_len
  have hKemColl : ∀ targetPk,
      𝒟[do
          let (pk, _) ← SignalPqxdh.sampleKemKeyGen
            (modelPrims (realUnreachedPrims XReal.kemKeyGen) realPEParams)
          pure (pk == targetPk)] {true} ≤ 1 / (2 : ℝ≥0∞) ^ 255 :=
    fun targetPk => SignalPqxdh.prob_le_one_div_two_pow_of_toReal (cwfPrimitives_kem_coll_bound targetPk)
  have hKemBin : SignalPqxdh.KemDeltaCorrect
      (modelPrims (realUnreachedPrims XReal.kemKeyGen) realPEParams) 1 :=
    Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses.kemDeltaCorrect_one _
  rcases hMain XReal.kemKeyGen hKemValid hKemColl 1 hKemBin 1 hℓ
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide) A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨XReal.kemKeyGen, 1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    hBound1,
    hBound2 1 (SignalPqxdh.keyIndRoGap_one S
      (modelPrims (realUnreachedPrims XReal.kemKeyGen) realPEParams) _)⟩

attribute [local irreducible] CryptoGames.MLKEM.kyber1024KemKeyGen

/-- Non-vacuity witness instantiating both advantage bounds of the concrete Round-3
CRYSTALS-Kyber-1024 headline `CryptoVerification.LibsignalCli.CliPqxdhElfSecure` (proved at the
universal adversary level by `CryptoVerification.LibsignalCli.libsignal_cli_pq_secure_elf_binary` in
`Computational/Theorems/Main.lean`) at `δ_kem := ε + 1 / 2 ^ 112` under `KyberNoiseGap ε` and the
`2^-255` public-key collision premise on `kyber1024KemKeyGen`. -/
theorem cliPqxdhElfSecure_kyber1024_instantiable
    (elf : Arm64.Process.ElfImage) (addrs : CliElfAddrs)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (ε : ℝ≥0∞) (hGap : SignalPqxdh.KyberNoiseGap ε)
    (hKemColl : ∀ targetPk,
      𝒟[do
          let (pk, _) ← SignalPqxdh.sampleKemKeyGen
            (modelPrims (realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen) realPEParams)
          pure (pk == targetPk)] {true} ≤ 1 / (2 : ℝ≥0∞) ^ 255)
    (hSec : CryptoVerification.LibsignalCli.CliPqxdhElfSecure S ℓ elf addrs) :
    ∃ (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      let run := cliRunElf elf addrs
      let X := realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen
      let Wp : PEParams := realPEParams
      let δ_kem : ℝ≥0∞ := ε + 1 / (2 : ℝ≥0∞) ^ 112
      CliPqxdhAdvantage S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
          CryptoGames.RFC7748.x25519EncT A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X Wp) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
          2 * CliKemFailProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
            CryptoGames.RFC7748.x25519EncT A +
          2 * CliPqxdhFlagProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
            CryptoGames.RFC7748.x25519EncT A
            (CliPqxdhExcusedAbort (CliReachesSampleNttStuckElf elf addrs) run Wp) ∧
      CliPqxdhAdvantage S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
          CryptoGames.RFC7748.x25519EncT A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
               (SignalPqxdh.GapSigEufCma (modelPrims X Wp) (modelPrims X Wp).isValidDhTriple
                 (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X Wp) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X Wp) (modelPrims X Wp).isValidDhTriple
                 (modelPrims X Wp).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem
          + 2 * CliKemFailProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
              CryptoGames.RFC7748.x25519EncT A
          + 2 * CliPqxdhFlagProb S run X Wp ℓ qep CryptoGames.RFC7748.x25519DecT
              CryptoGames.RFC7748.x25519EncT A
              (CliPqxdhExcusedAbort (CliReachesSampleNttStuckElf elf addrs) run Wp) := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  rcases hMain hKemColl ε hGap 1 hℓ
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide) A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    hBound1,
    hBound2 1 (SignalPqxdh.keyIndRoGap_one S
      (modelPrims (realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen) realPEParams) _)⟩

/--
info: 'CryptoVerification.E2E.not_pow8_idemp_ladder8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_pow8_idemp_ladder8

/--
info: 'CryptoVerification.E2E.xeddsaCurveLaws_modelPrimsReal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms xeddsaCurveLaws_modelPrimsReal

/--
info: 'CryptoVerification.E2E.modelPrims_XReal_cryptoAssumptions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms modelPrims_XReal_cryptoAssumptions

/--
info: 'CryptoVerification.E2E.session_hypotheses_satisfiable_real' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms session_hypotheses_satisfiable_real

/--
info: 'CryptoVerification.E2E.sessionSecure_real_instantiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sessionSecure_real_instantiable

/--
info: 'CryptoVerification.E2E.cli_pq_headline_hypotheses_satisfiable_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cli_pq_headline_hypotheses_satisfiable_real

/--
info: 'CryptoVerification.E2E.cli_pq_headline_hypotheses_satisfiable_real_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cli_pq_headline_hypotheses_satisfiable_real_concrete

/--
info: 'CryptoVerification.E2E.libsignalCliPqSecure_real_instantiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms libsignalCliPqSecure_real_instantiable

/--
info: 'CryptoVerification.E2E.pqOom_hypotheses_satisfiable_real' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pqOom_hypotheses_satisfiable_real

/--
info: 'CryptoVerification.E2E.cli_pq_elf_placed_hypotheses_satisfiable_real_9eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cli_pq_elf_placed_hypotheses_satisfiable_real_9eq

/--
info: 'CryptoVerification.E2E.cliPqxdhElfSecure_real_9eq_instantiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliPqxdhElfSecure_real_9eq_instantiable

/--
info: 'CryptoVerification.E2E.cliPqxdhElfSecure_kyber1024_instantiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliPqxdhElfSecure_kyber1024_instantiable

end CryptoVerification.E2E
