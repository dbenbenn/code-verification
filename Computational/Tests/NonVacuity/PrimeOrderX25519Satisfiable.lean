/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.NonVacuity.PqHeadlineSatisfiable
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
public import Computational.Tests.XeddsaRomNonVac
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import Computational.Tests.NonVacuity.KeyInd1KeyRoNonVac
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.SignalSession.PqModelRun
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Algebra.Field.ZMod
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Prime-Order X25519 Joint Hypothesis Satisfiability

**Checked by Lean.**

Joint satisfiability witness for `SessionSecure`, `LibsignalCliPqSecure`, and the excused-abort
specialization of `CliPqxdhSecurityFor` over the Curve25519 subgroup of prime order
`l25519 = 2 ^ 252 + 27742317777372353535851937790883648493`. The carrier
`Pt25519 := Fin (halfL25519 + 1)` of size `(l25519 + 1) / 2 > 2 ^ 251` represents `0` together
with the `(l25519 - 1) / 2` x-only `{±[q]B}` pairs on Curve25519, with basepoint `base25519 = 1`
(Montgomery coordinate `u = 9`). RFC 7748 clamped scalars act injectively on `Pt25519` via
`absZMod (c * Q)`, which embeds equivariantly into `dh255` (`ModelPrimsWitness255`) and gives
`DhKerUniform dh25519` and the point-fiber bound `δ = (1 : ℝ≥0∞) / 2 ^ 250`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA SM
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SignalSession CryptoGames.LibsignalSM.Proofs.Correctness
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
open Computational.Tests.XeddsaRomNonVac
open SpecTests.SignalPqxdh (cwfC cwfC_clamp cwfC_word_eq)
open _root_.SignalPqxdh (word256ToBytes clampScalar25519)
open VerifiedLibraries.Common (
  edOrderL fpInv recoverXEven EdPoint edZero edBasepoint edOnCurve edNeg edSmul
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  montLiftEd edSmul_edNeg
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  edOnCurve_edBasepoint edOnCurve_edNeg edNatSmul edOnCurve_edNatSmul
  edNatSmul_edZero edNatSmul_one edNatSmul_mul edSmul_eq_edNatSmul
  edSmul_edOrderL_edBasepoint edOrderL_lt_two_pow_256
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (
  edToMontU edToMontU_lt edToMontU_edBasepoint edBasepoint_ne_edZero
)

attribute [local irreducible] fpInv recoverXEven montLiftEd montToEdwards edSmul

/-- Prime-order x-only subgroup carrier for Curve25519 (`0` for the identity and `1 .. halfL25519`
for the `(l25519 - 1) / 2` non-identity `{±[q]B}` pairs on Curve25519). -/
abbrev Pt25519 : Type := Fin (halfL25519 + 1)

theorem two_pow_251_lt_card_pt25519 : 2 ^ 251 < Fintype.card Pt25519 := by
  rw [Fintype.card_fin]
  unfold halfL25519 l25519
  decide

/-- Generator `[1]B` (Montgomery `u = 9`) in `Pt25519`. -/
def base25519 : Pt25519 :=
  ⟨1, by unfold halfL25519 l25519; decide⟩

private theorem pt25519_val_le_half (Q : Pt25519) : Q.val ≤ halfL25519 :=
  Nat.lt_succ_iff.mp Q.isLt

private theorem pt25519_val_lt_two_pow_252 (Q : Pt25519) : Q.val < 2 ^ 252 :=
  lt_of_le_of_lt (pt25519_val_le_half Q) halfL25519_lt_two_pow_252

private theorem pt25519_val_lt_l25519 (Q : Pt25519) : Q.val < l25519 :=
  lt_trans (pt25519_val_lt_two_pow_252 Q) two_pow_252_lt_l25519

private theorem absZMod_pt25519_cast (Q : Pt25519) :
    absZMod (Q.val : ZMod l25519) = Q.val := by
  unfold absZMod
  simp [ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q), pt25519_val_le_half Q]

private theorem pt25519_cast_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) :
    (Q.val : ZMod l25519) ≠ 0 := by
  intro h0
  have hval := congrArg ZMod.val h0
  rw [ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q), ZMod.val_zero] at hval
  exact hQ (Fin.ext (by simpa using hval))

/-- Embeds `Q : Pt25519` into `BitVec 255` via `0` at `0` and the Curve25519 Montgomery
`u`-coordinate `edToMontU ([Q.val] edBasepoint)` for `Q ≠ 0`. -/
def ptToBv255 (Q : Pt25519) : BitVec 255 :=
  if Q.val == 0 then 0#255
  else BitVec.ofNat 255 (edToMontU (edNatSmul Q.val edBasepoint))

/-- 32-byte little-endian Curve25519 Montgomery encoding of `Q : Pt25519`. -/
def encPt25519 (Q : Pt25519) : List (BitVec 8) :=
  encPt255 (ptToBv255 Q)

def encT25519 (Q : Pt25519) : PublicKey :=
  encT255 (ptToBv255 Q)

private def findPt25519From (f : Pt25519 → PublicKey) (pk : PublicKey) (cur fuel : ℕ) :
    Option Pt25519 :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if h : cur < halfL25519 + 1 then
      let Q : Pt25519 := ⟨cur, h⟩
      if f Q == pk then some Q else findPt25519From f pk (cur + 1) fuel'
    else none

/-- Constructive bounded search inverting an injective `Pt25519 → PublicKey` encoding.
Scans `Pt25519 = Fin (halfL25519 + 1)` (`≈ 2 ^ 251` values) upward from `0`; computable, though
practical to evaluate only on small exponents (infeasible to exhaust on arbitrary keys). -/
def findPt25519 (f : Pt25519 → PublicKey) (pk : PublicKey) : Option Pt25519 :=
  findPt25519From f pk 0 (halfL25519 + 1)

private theorem findPt25519From_sound {f : Pt25519 → PublicKey} {pk : PublicKey} :
    ∀ {cur fuel : ℕ} {Q : Pt25519}, findPt25519From f pk cur fuel = some Q → f Q = pk
  | _, 0, _, h => by cases h
  | cur, fuel' + 1, Q, h => by
    unfold findPt25519From at h
    split at h
    · next hcur =>
      dsimp only at h
      cases heq : f ⟨cur, hcur⟩ == pk
      · rw [heq] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact findPt25519From_sound h
      · rw [heq] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        exact h ▸ beq_iff_eq.mp heq
    · cases h

private theorem findPt25519From_apply {f : Pt25519 → PublicKey} (hf : Function.Injective f)
    (Q : Pt25519) :
    ∀ (cur fuel : ℕ), cur ≤ Q.val → Q.val < cur + fuel →
      findPt25519From f (f Q) cur fuel = some Q
  | _, 0, _, hlt => by omega
  | cur, fuel' + 1, hge, hlt => by
    have hcur : cur < halfL25519 + 1 := lt_of_le_of_lt hge Q.isLt
    simp only [findPt25519From, hcur, ↓reduceDIte]
    cases heq : f ⟨cur, hcur⟩ == f Q
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne : cur ≠ Q.val := fun hc => by
        have h : (f ⟨cur, hcur⟩ == f Q) = true := beq_iff_eq.mpr (by subst hc; rfl)
        rw [heq] at h; cases h
      exact findPt25519From_apply hf Q (cur + 1) fuel' (by omega) (by omega)
    · simp only [↓reduceIte]
      exact congrArg some (hf (beq_iff_eq.mp heq))

theorem findPt25519_apply {f : Pt25519 → PublicKey} (hf : Function.Injective f) (Q : Pt25519) :
    findPt25519 f (f Q) = some Q :=
  findPt25519From_apply hf Q 0 (halfL25519 + 1) (Nat.zero_le _) (by simpa using Q.isLt)

/-- Exact characterization of `findPt25519` for injective `f`. -/
theorem findPt25519_eq_some_iff {f : Pt25519 → PublicKey} (hf : Function.Injective f)
    (pk : PublicKey) (Q : Pt25519) :
    findPt25519 f pk = some Q ↔ f Q = pk :=
  ⟨findPt25519From_sound, fun h => h ▸ findPt25519_apply hf Q⟩

/-- Left inverse of `encT25519` on `PublicKey` via `findPt25519` (computable, though practical to
evaluate only on small `Pt25519` exponents since `halfL25519 + 1 ≈ 2 ^ 251`). -/
def decT25519 (pk : PublicKey) : Option Pt25519 :=
  findPt25519 encT25519 pk

/-- Clamped x-only prime-subgroup DH action on `Pt25519` over `ZMod l25519`. -/
def dh25519 : DHFun (BitVec 256) Pt25519 where
  base := base25519
  dh k Q :=
    ⟨absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)),
     Nat.lt_succ_of_le (absZMod_le_half _)⟩

private theorem if_false_eq_19 {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

private theorem p25519_lt_two_pow_255_19 : VerifiedLibraries.Common.p25519 < 2 ^ 255 := by
  unfold VerifiedLibraries.Common.p25519; decide

private theorem zmod_val_lt_two_pow_256_19 (z : ZMod l25519) : z.val < 2 ^ 256 := by
  have hl : l25519 < 2 ^ 256 := by unfold l25519; decide
  exact lt_trans z.val_lt hl

private theorem edNatSmul_edOrderL_edBasepoint : edNatSmul edOrderL edBasepoint = edZero := by
  rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint]
  exact edSmul_edOrderL_edBasepoint

private theorem edNatSmul_edOrderL_edNatSmul_edBasepoint (n : Nat) :
    edNatSmul edOrderL (edNatSmul n edBasepoint) = edZero := by
  rw [← edNatSmul_mul edOrderL n edOnCurve_edBasepoint, Nat.mul_comm,
    edNatSmul_mul n edOrderL edOnCurve_edBasepoint, edNatSmul_edOrderL_edBasepoint,
    edNatSmul_edZero]

private theorem edNatSmul_pt25519_ne_edZero {Q : Pt25519} (hQ : Q ≠ 0) :
    edNatSmul Q.val edBasepoint ≠ edZero := by
  have hval : Q.val = (Q.val : ZMod l25519).val :=
    (ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q)).symm
  rw [hval]
  exact edNatSmul_ne_edZero_of_zmod_ne_zero edOnCurve_edBasepoint edBasepoint_ne_edZero
    edNatSmul_edOrderL_edBasepoint (pt25519_cast_ne_zero hQ)

private theorem base25519_ne_zero : dh25519.base ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_zero] at hv
  exact absurd hv (by decide : (1 : ℕ) ≠ 0)

private theorem baseZMod_ne_zero : (dh25519.base.val : ZMod l25519) ≠ 0 :=
  pt25519_cast_ne_zero base25519_ne_zero

private theorem ptToBv255_zero : ptToBv255 0 = 0#255 := rfl

private theorem ptToBv255_of_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) :
    ptToBv255 Q = BitVec.ofNat 255 (edToMontU (edNatSmul Q.val edBasepoint)) := by
  have hne : (Q.val == 0) = false := beq_eq_false_iff_ne.mpr fun h0 => hQ (Fin.ext h0)
  unfold ptToBv255
  exact if_false_eq_19 (by rw [hne]; decide) _ _

private theorem ptToBv255_base : ptToBv255 dh25519.base = dh255.base := by
  rw [ptToBv255_of_ne_zero base25519_ne_zero, dh255_base_eq]
  change BitVec.ofNat 255 (edToMontU (edNatSmul 1 edBasepoint)) = 9#255
  rw [edNatSmul_one edOnCurve_edBasepoint, edToMontU_edBasepoint]

private theorem ptToBv255_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) : ptToBv255 Q ≠ 0 := by
  intro h0
  rw [ptToBv255_of_ne_zero hQ] at h0
  rcases liftCanon255_ofNat_edToMontU (edOnCurve_edNatSmul Q.val edOnCurve_edBasepoint)
    (edNatSmul_pt25519_ne_edZero hQ) (edNatSmul_edOrderL_edNatSmul_edBasepoint Q.val)
    with ⟨P, hP, _⟩
  rw [h0, liftCanon255_zero] at hP
  cases hP

private theorem ptToBv255_inj : Function.Injective ptToBv255 := by
  intro Q1 Q2 h
  by_cases h1 : Q1 = 0
  · subst h1
    by_cases h2 : Q2 = 0
    · exact h2.symm
    · exact absurd h.symm (ptToBv255_ne_zero h2)
  · by_cases h2 : Q2 = 0
    · subst h2
      exact absurd h (ptToBv255_ne_zero h1)
    · rw [ptToBv255_of_ne_zero h1, ptToBv255_of_ne_zero h2] at h
      have hu1 : edToMontU (edNatSmul Q1.val edBasepoint) < 2 ^ 255 :=
        lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_19
      have hu2 : edToMontU (edNatSmul Q2.val edBasepoint) < 2 ^ 255 :=
        lt_trans (edToMontU_lt _) p25519_lt_two_pow_255_19
      have hu_eq : edToMontU (edNatSmul Q1.val edBasepoint) =
          edToMontU (edNatSmul Q2.val edBasepoint) := by
        have ht := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hu2] at ht
      have hv1 : Q1.val = (Q1.val : ZMod l25519).val :=
        (ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q1)).symm
      have hv2 : Q2.val = (Q2.val : ZMod l25519).val :=
        (ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q2)).symm
      have hu_zmod : edToMontU (edNatSmul (Q1.val : ZMod l25519).val edBasepoint) =
          edToMontU (edNatSmul (Q2.val : ZMod l25519).val edBasepoint) :=
        (congrArg (fun n => edToMontU (edNatSmul n edBasepoint)) hv1.symm).trans
          (hu_eq.trans (congrArg (fun n => edToMontU (edNatSmul n edBasepoint)) hv2))
      have hpm := (edToMontU_edNatSmul_eq_iff edOnCurve_edBasepoint edBasepoint_ne_edZero
        edNatSmul_edOrderL_edBasepoint (pt25519_cast_ne_zero h1) (pt25519_cast_ne_zero h2)).mp
        hu_zmod
      have habs := (absZMod_eq_iff _ _).mpr hpm
      rw [absZMod_pt25519_cast, absZMod_pt25519_cast] at habs
      exact Fin.ext habs

theorem encPt25519_inj : Function.Injective encPt25519 :=
  encPt255_inj.comp ptToBv255_inj

theorem encT25519_inj : Function.Injective encT25519 :=
  encT255_inj.comp ptToBv255_inj

theorem decT25519_encT25519 (Q : Pt25519) : decT25519 (encT25519 Q) = some Q :=
  findPt25519_apply encT25519_inj Q

open Classical in
/-- `decT25519` agrees pointwise with the `Exists.choose` definition. -/
theorem decT25519_eq_classical :
    decT25519 = fun pk : PublicKey =>
      if h : ∃ Q : Pt25519, encT25519 Q = pk then some h.choose else none := by
  funext pk
  split_ifs with h
  · exact (findPt25519_eq_some_iff encT25519_inj pk h.choose).mpr h.choose_spec
  · cases hd : decT25519 pk with
    | none => rfl
    | some Q =>
      exact absurd ⟨Q, (findPt25519_eq_some_iff encT25519_inj pk Q).mp hd⟩ h

theorem encT25519_ne_dummyKey (Q : Pt25519) : encT25519 Q ≠ dummyKey :=
  encT255_ne_dummyKey (ptToBv255 Q)

private theorem encPt25519_length (Q : Pt25519) : (encPt25519 Q).length = 32 :=
  encPt255_length (ptToBv255 Q)

private theorem encPt25519_zero : encPt25519 0 = List.replicate 32 0#8 := by
  unfold encPt25519
  rw [ptToBv255_zero]
  exact encPt255_zero

private theorem encPt25519_base : encPt25519 dh25519.base = x25519Base := by
  unfold encPt25519
  rw [ptToBv255_base]
  exact encPt255_base

private theorem dh25519_dh_val (k : BitVec 256) (Q : Pt25519) :
    (dh25519.dh k Q).val =
      absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) := by
  unfold dh25519
  rfl

theorem dh25519_zero (x : BitVec 256) : dh25519.dh x 0 = 0 := by
  apply Fin.ext
  rw [Fin.val_zero]
  change absZMod (clampedScalarZMod (word256ToBytes x) * (((0 : Pt25519).val : ℕ) : ZMod l25519)) = 0
  rw [Fin.val_zero]
  simp [absZMod]

theorem dh25519_ne_zero (k : BitVec 256) (Q : Pt25519) (hQ : Q ≠ 0) :
    dh25519.dh k Q ≠ 0 := by
  intro h0
  have hval : absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) = 0 := by
    simpa [dh25519] using congrArg Fin.val h0
  have hmul := (absZMod_eq_zero_iff _).mp hval
  exact mul_ne_zero (clampedScalarZMod_ne_zero (word256ToBytes k)) (pt25519_cast_ne_zero hQ) hmul

private theorem ptToBv255_dh25519 (k : BitVec 256) (Q : Pt25519) :
    ptToBv255 (dh25519.dh k Q) = dh255.dh k (ptToBv255 Q) := by
  by_cases hQ : Q = 0
  · subst hQ
    rw [dh25519_zero, ptToBv255_zero]
    exact (dh255_zero k).symm
  · have hdh_ne : dh25519.dh k Q ≠ 0 := dh25519_ne_zero k Q hQ
    let c := clampedScalarZMod (word256ToBytes k)
    let z : ZMod l25519 := c * (Q.val : ZMod l25519)
    have hz_ne : z ≠ 0 := mul_ne_zero (clampedScalarZMod_ne_zero _) (pt25519_cast_ne_zero hQ)
    let Qd := dh25519.dh k Q
    have hQd_ne : Qd ≠ 0 := hdh_ne
    have habs_Qd : absZMod (Qd.val : ZMod l25519) = absZMod z :=
      (absZMod_pt25519_cast Qd).trans (dh25519_dh_val k Q)
    have hQd_pm : (Qd.val : ZMod l25519) = z ∨ (Qd.val : ZMod l25519) = -z :=
      (absZMod_eq_iff _ _).mp habs_Qd
    have hQd_val : Qd.val = (Qd.val : ZMod l25519).val :=
      (ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Qd)).symm
    have hlhs_u : edToMontU (edNatSmul Qd.val edBasepoint) =
        edToMontU (edNatSmul z.val edBasepoint) :=
      (congrArg (fun n => edToMontU (edNatSmul n edBasepoint)) hQd_val).trans
        ((edToMontU_edNatSmul_eq_iff edOnCurve_edBasepoint edBasepoint_ne_edZero
          edNatSmul_edOrderL_edBasepoint (pt25519_cast_ne_zero hQd_ne) hz_ne).mpr hQd_pm)
    have hlhs : ptToBv255 Qd = BitVec.ofNat 255 (edToMontU (edNatSmul z.val edBasepoint)) :=
      (ptToBv255_of_ne_zero hQd_ne).trans (congrArg (BitVec.ofNat 255) hlhs_u)
    have hR_on := edOnCurve_edNatSmul Q.val edOnCurve_edBasepoint
    have hR_ne := edNatSmul_pt25519_ne_edZero hQ
    have hR_L := edNatSmul_edOrderL_edNatSmul_edBasepoint Q.val
    rcases liftCanon255_ofNat_edToMontU hR_on hR_ne hR_L with ⟨P, hP, hpm⟩
    have hQ_val : Q.val = (Q.val : ZMod l25519).val :=
      (ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q)).symm
    have hrhs1 : dh255.dh k (ptToBv255 Q) =
        BitVec.ofNat 255 (edToMontU (edNatSmul c.val P)) :=
      (congrArg (dh255.dh k) (ptToBv255_of_ne_zero hQ)).trans (dh255_of_liftCanon (k := k) hP)
    have hrhs_u : edToMontU (edNatSmul c.val P) = edToMontU (edNatSmul z.val edBasepoint) := by
      have hmul_u : edToMontU (edNatSmul c.val (edNatSmul Q.val edBasepoint)) =
          edToMontU (edNatSmul z.val edBasepoint) :=
        (congrArg (fun n => edToMontU (edNatSmul c.val (edNatSmul n edBasepoint))) hQ_val).trans
          (congrArg edToMontU (edNatSmul_zmod_mul edOnCurve_edBasepoint
            edNatSmul_edOrderL_edBasepoint c (Q.val : ZMod l25519))).symm
      rcases hpm with rfl | rfl
      · exact hmul_u
      · have hneg : edNatSmul c.val (edNeg (edNatSmul Q.val edBasepoint)) =
            edNeg (edNatSmul c.val (edNatSmul Q.val edBasepoint)) := by
          rw [← edSmul_eq_edNatSmul (zmod_val_lt_two_pow_256_19 c) (edOnCurve_edNeg hR_on),
            edSmul_edNeg (zmod_val_lt_two_pow_256_19 c) hR_on,
            edSmul_eq_edNatSmul (zmod_val_lt_two_pow_256_19 c) hR_on]
        exact (congrArg edToMontU hneg).trans
          ((edToMontU_edNeg (edOnCurve_edNatSmul c.val hR_on)).trans hmul_u)
    exact hlhs.trans ((congrArg (BitVec.ofNat 255) hrhs_u.symm).trans hrhs1.symm)

theorem dh25519_commutes : dh25519.Commutes := by
  intro a b
  apply ptToBv255_inj
  have h1 : ptToBv255 (dh25519.dh a (dh25519.dh b dh25519.base)) =
      dh255.dh a (dh255.dh b dh255.base) :=
    (ptToBv255_dh25519 a _).trans (congrArg (dh255.dh a)
      ((ptToBv255_dh25519 b _).trans (congrArg (dh255.dh b) ptToBv255_base)))
  have h2 : ptToBv255 (dh25519.dh b (dh25519.dh a dh25519.base)) =
      dh255.dh b (dh255.dh a dh255.base) :=
    (ptToBv255_dh25519 b _).trans (congrArg (dh255.dh b)
      ((ptToBv255_dh25519 a _).trans (congrArg (dh255.dh a) ptToBv255_base)))
  exact h1.trans ((dh255_commutes a b).trans h2.symm)

theorem dh25519_dh_inj (a : BitVec 256) : Function.Injective (dh25519.dh a) := by
  intro Q Q' h
  have habs : absZMod (clampedScalarZMod (word256ToBytes a) * (Q.val : ZMod l25519)) =
      absZMod (clampedScalarZMod (word256ToBytes a) * (Q'.val : ZMod l25519)) :=
    congrArg Fin.val h
  have hpm : (Q.val : ZMod l25519) = (Q'.val : ZMod l25519) ∨
      (Q.val : ZMod l25519) = -(Q'.val : ZMod l25519) := by
    rcases (absZMod_eq_iff _ _).mp habs with hm | hm
    · exact Or.inl (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
    · rw [← mul_neg] at hm
      exact Or.inr (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
  have hval : absZMod (Q.val : ZMod l25519) = absZMod (Q'.val : ZMod l25519) :=
    (absZMod_eq_iff _ _).mpr hpm
  rw [absZMod_pt25519_cast, absZMod_pt25519_cast] at hval
  exact Fin.ext hval

theorem dh25519_kerUniform : DhKerUniform dh25519 := by
  intro s x Q Q'
  rw [(dh25519_dh_inj x).eq_iff, (dh25519_dh_inj s).eq_iff]

/-- Each point `Q : Pt25519` has at most `64` preimages under `w ↦ dh25519.dh w dh25519.base`
(`≤ 2` clamped scalars `±c₀` times `2^5 = 32` clamped-away bits of `w : BitVec 256`). -/
theorem dh25519_base_fiber_card (Q : Pt25519) :
    (Finset.univ.filter (fun w : BitVec 256 => dh25519.dh w dh25519.base = Q)).card ≤ 64 := by
  set S := Finset.univ.filter (fun w : BitVec 256 => dh25519.dh w dh25519.base = Q)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : dh25519.dh w0 dh25519.base = Q := (Finset.mem_filter.mp hw0).2
    set c0 := clampedScalarZMod (word256ToBytes w0)
    let b0 : ZMod l25519 := (dh25519.base.val : ZMod l25519)
    have hb0_ne : b0 ≠ 0 := baseZMod_ne_zero
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
      have hw1_eq : dh25519.dh w1 dh25519.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
      have hw2_eq : dh25519.dh w2 dh25519.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
      have hw1_abs : absZMod (clampedScalarZMod (word256ToBytes w1) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw1_eq.trans hw0_eq.symm)
        rwa [dh25519_dh_val, dh25519_dh_val] at h
      have hw2_abs : absZMod (clampedScalarZMod (word256ToBytes w2) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw2_eq.trans hw0_eq.symm)
        rwa [dh25519_dh_val, dh25519_dh_val] at h
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
        · exfalso
          exact hc0_ne_neg (hc2.symm.trans (htag_iff.mp hc1)).symm
        · exfalso
          exact hc0_ne_neg (hc1.symm.trans (htag_iff.mpr hc2)).symm
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

/-- Point-fiber probability bound `64 / 2 ^ 256 = 1 / 2 ^ 250` on `Pt25519`. -/
theorem dh25519_base_fiber_prob_le (Q : Pt25519) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | dh25519.dh x dh25519.base = Q} ≤
      (1 : ℝ≥0∞) / 2 ^ 250 := by
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample,
      Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_of_le_mul
  calc ((Finset.univ.filter (fun x : BitVec 256 => dh25519.dh x dh25519.base = Q)).card : ℝ≥0∞)
      ≤ ((64 : ℕ) : ℝ≥0∞) := by exact_mod_cast dh25519_base_fiber_card Q
    _ = (2 : ℝ≥0∞) ^ 6 := by norm_num
    _ = ((1 : ℝ≥0∞) / 2 ^ 250) * (2 : ℝ≥0∞) ^ 256 := by
      rw [one_div, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 250 * 2 ^ 6 by rw [← pow_add],
          ENNReal.inv_mul_cancel_left (by simp) (by simp)]

/-- `Crypto` witness backed by Curve25519 scalar multiplication (`c255`), FIPS 180-4 SHA-256
(`sha256Compress`), and FIPS 197 AES-256 (`aes256Enc`, `aes256Dec`). -/
@[expose] def c25519 : Crypto :=
  { c255 with
    F := sha256Compress
    E := CryptoGames.AES256.aes256Enc
    D := CryptoGames.AES256.aes256Dec }

/-- 4-field `PqxdhPrims` witness (`Q255`). -/
abbrev Q25519 : PqxdhPrims := Q255

@[expose] def W25519 : PEParams := ⟨c25519, Q25519⟩

/-- `UnreachedPqxdhPrimitives` witness (`X255`). -/
abbrev X25519 : UnreachedPqxdhPrimitives := X255

private theorem word256ToBytes_clamp256_25519 (k : BitVec 256) :
    word256ToBytes (clamp256 k) = clampScalar25519 (word256ToBytes k) := by
  have h1 : u8Vec 32 (word256ToBytes (clamp256 k)) =
      u8Vec 32 (clampScalar25519 (word256ToBytes k)) := by
    rw [u8Vec_word256ToBytes, ← clampScalar_keyVec,
        ← u8Vec_word256ToBytes, u8Vec_clampScalar25519]
  have h2 := congrArg vecU8 h1
  rwa [vecU8_u8Vec_of_length _ (length_word256ToBytes _),
       vecU8_u8Vec_of_length _ (_root_.SignalPqxdh.clampScalar25519_length _)] at h2

theorem libX25519Rel_c25519 : X25519RealizesDh c25519 dh25519 encPt25519 encT25519 := by
  refine ⟨?_, fun _ => rfl⟩
  refine
    { enc_injective := encPt25519_inj
      enc_length := encPt25519_length
      enc_zero := encPt25519_zero
      enc_base := encPt25519_base
      base_ne_zero := base25519_ne_zero
      hook := fun k Q => ?_
      pubKey_hook := fun k => ?_
      dh_clamp := fun k Q => ?_
      dh_ne_zero := dh25519_ne_zero }
  · exact (libX25519Rel_c255.1.hook k (ptToBv255 Q)).trans
      (congrArg encPt255 (ptToBv255_dh25519 k Q).symm)
  · exact (libX25519Rel_c255.1.pubKey_hook k).trans
      ((congrArg (fun b => encPt255 (dh255.dh k b)) ptToBv255_base.symm).trans
        (congrArg encPt255 (ptToBv255_dh25519 k dh25519.base).symm))
  · apply Fin.ext
    dsimp only [dh25519]
    rw [word256ToBytes_clamp256_25519, clampedScalarZMod_clamp]

private theorem isCanonicalRef_congr_fields {P₁ P₂ : SignalPqxdh.Primitives}
    (hm : P₁.montToEd = P₂.montToEd) (ht : P₁.isTorsionFree = P₂.isTorsionFree)
    (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef P₁ pk = SignalPqxdh.isCanonicalRef P₂ pk := by
  unfold SignalPqxdh.isCanonicalRef
  rw [hm, ht]

private theorem sha512Ref_congr_fields {P₁ P₂ : SignalPqxdh.Primitives}
    (hc : P₁.sha512Compress = P₂.sha512Compress) :
    SignalPqxdh.sha512Ref P₁ = SignalPqxdh.sha512Ref P₂ := by
  funext msg
  unfold SignalPqxdh.sha512Ref
  have hstep : SignalPqxdh.sha512Step P₁ = SignalPqxdh.sha512Step P₂ := by
    funext s b; unfold SignalPqxdh.sha512Step; rw [hc]
  rw [hstep]

private theorem xeddsaVerifyRef_congr_fields {P₁ P₂ : SignalPqxdh.Primitives}
    (hm : P₁.montToEd = P₂.montToEd) (hc : P₁.compress = P₂.compress)
    (hn : P₁.edNeg = P₂.edNeg) (hsw : P₁.scalarFromWide = P₂.scalarFromWide)
    (hs5 : P₁.sha512 = P₂.sha512) (hsm : P₁.scalarFromBytesModOrder = P₂.scalarFromBytesModOrder)
    (hd : P₁.doubleScalarMulBasepoint = P₂.doubleScalarMulBasepoint)
    (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef P₁ pk m sig = SignalPqxdh.xeddsaVerifyRef P₂ pk m sig := by
  unfold SignalPqxdh.xeddsaVerifyRef
  rw [hm, hc, hn, hsw, hs5, hsm, hd]

private theorem isValidDhTripleRef_congr_fields {P₁ P₂ : SignalPqxdh.Primitives}
    (hc : P₁.isCanonical = P₂.isCanonical) (hp : P₁.pow8 = P₂.pow8)
    (hb : P₁.x25519Base = P₂.x25519Base) (hx : P₁.x25519 = P₂.x25519)
    (A B Z : List UInt8) :
    SignalPqxdh.isValidDhTripleRef P₁ A B Z ↔ SignalPqxdh.isValidDhTripleRef P₂ A B Z := by
  unfold SignalPqxdh.isValidDhTripleRef SignalPqxdh.onCurveKey
  rw [hc, hp, hb, hx]

private theorem sampleKemKeyGen_congr_fields {P₁ P₂ : SignalPqxdh.Primitives}
    (hk : P₁.kemKeyGen = P₂.kemKeyGen) :
    SignalPqxdh.sampleKemKeyGen P₁ = SignalPqxdh.sampleKemKeyGen P₂ := by
  unfold SignalPqxdh.sampleKemKeyGen
  rw [hk]

private theorem mp25519_x25519 :
    (modelPrims X25519 W25519).x25519 = (modelPrims X255 W255).x25519 := rfl

private theorem mp25519_x25519Base :
    (modelPrims X25519 W25519).x25519Base = (modelPrims X255 W255).x25519Base := rfl

private theorem mp25519_pow8 :
    (modelPrims X25519 W25519).pow8 = (modelPrims X255 W255).pow8 := rfl

private theorem mp25519_kemKeyGen :
    (modelPrims X25519 W25519).kemKeyGen = (modelPrims X255 W255).kemKeyGen := rfl

private theorem mp25519_isCanonical :
    (modelPrims X25519 W25519).isCanonical = (modelPrims X255 W255).isCanonical := by
  funext pk
  exact isCanonicalRef_congr_fields (P₁ := { blockLevelPrims X25519 W25519 with
      sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X25519 W25519) })
    (P₂ := { blockLevelPrims X255 W255 with
      sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X255 W255) }) rfl rfl pk

private theorem mp25519_sha512 :
    SignalPqxdh.sha512Ref (blockLevelPrims X25519 W25519) =
      SignalPqxdh.sha512Ref (blockLevelPrims X255 W255) :=
  sha512Ref_congr_fields rfl

private theorem mp25519_sigVerify (pk m sig : List UInt8) :
    (modelPrims X25519 W25519).sigVerify pk m sig =
      (modelPrims X255 W255).sigVerify pk m sig :=
  xeddsaVerifyRef_congr_fields
    (P₁ := { blockLevelPrims X25519 W25519 with
      sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X25519 W25519) })
    (P₂ := { blockLevelPrims X255 W255 with
      sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X255 W255) })
    rfl rfl rfl rfl mp25519_sha512 rfl rfl pk m sig

theorem modelPrims_X25519_cryptoAssumptions : ModelPrimsCryptoAssumptions X25519 W25519 where
  x25519_zero_iff := fun a1 a2 pk h1 h2 hpk => by
    rw [mp25519_x25519]
    exact modelPrims_X255_cryptoAssumptions.x25519_zero_iff a1 a2 pk h1 h2 hpk
  canon_base := fun e he => by
    rw [mp25519_isCanonical, mp25519_x25519Base]
    exact modelPrims_X255_cryptoAssumptions.canon_base e he
  canon_x25519 := fun a pk ha hcan => by
    rw [mp25519_isCanonical] at hcan ⊢
    rw [mp25519_x25519]
    exact modelPrims_X255_cryptoAssumptions.canon_x25519 a pk ha hcan
  pow8_idemp := modelPrims_X255_cryptoAssumptions.pow8_idemp
  isValidDhTriple_eq_ref := fun A B Z =>
    (modelPrims_X255_cryptoAssumptions.isValidDhTriple_eq_ref A B Z).trans
      (isValidDhTripleRef_congr_fields mp25519_isCanonical mp25519_pow8
        mp25519_x25519Base mp25519_x25519 A B Z).symm
  x25519_pow8_congr := fun a pk1 pk2 ha h1 h2 hp => by
    rw [mp25519_x25519]
    exact modelPrims_X255_cryptoAssumptions.x25519_pow8_congr a pk1 pk2 ha h1 h2 hp
  x25519_congr_of_base_eq := fun a1 a2 pk h1 h2 hcan hb => by
    rw [mp25519_isCanonical] at hcan
    rw [mp25519_x25519Base] at hb
    rw [mp25519_x25519]
    exact modelPrims_X255_cryptoAssumptions.x25519_congr_of_base_eq a1 a2 pk h1 h2 hcan hb
  canon_pow8_inj := fun pk1 pk2 h1 h2 hp => by
    rw [mp25519_isCanonical] at h1 h2
    exact modelPrims_X255_cryptoAssumptions.canon_pow8_inj pk1 pk2 h1 h2 hp
  pow8_len := modelPrims_X255_cryptoAssumptions.pow8_len
  ec_coll_bound := fun targetPk => by
    rw [mp25519_x25519Base]
    exact modelPrims_X255_cryptoAssumptions.ec_coll_bound targetPk
  x25519_inj_pow8 := fun a pk1 pk2 ha h1 h2 hx => by
    rw [mp25519_x25519] at hx
    exact modelPrims_X255_cryptoAssumptions.x25519_inj_pow8 a pk1 pk2 ha h1 h2 hx
  pow8_base_len := fun p e he hp => by
    rw [mp25519_x25519Base] at hp
    exact modelPrims_X255_cryptoAssumptions.pow8_base_len p e he hp
  sigPkGen_eq_x25519Base := by
    rw [mp25519_x25519Base]
    exact modelPrims_X255_cryptoAssumptions.sigPkGen_eq_x25519Base
  scalarMul_len := modelPrims_X255_cryptoAssumptions.scalarMul_len
  scalarAdd_len := modelPrims_X255_cryptoAssumptions.scalarAdd_len
  kemKeyGen_len := modelPrims_X255_cryptoAssumptions.kemKeyGen_len
  sig_corr := fun sk msg r => by
    rw [mp25519_sigVerify]
    exact modelPrims_X255_cryptoAssumptions.sig_corr sk msg r
  kem_coll_bound := fun targetPk => by
    rw [sampleKemKeyGen_congr_fields mp25519_kemKeyGen]
    exact modelPrims_X255_cryptoAssumptions.kem_coll_bound targetPk

private theorem c25519_D_E (k : BitVec 256) (x : BitVec 128) : c25519.D k (c25519.E k x) = x :=
  LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip.aes256Dec_aes256Enc k x

private theorem encaps1Total_K255 : Encaps1Total K255 :=
  fun _ _ _ => rfl

private theorem bhEncaps1Total_W25519 : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W25519.Q.K :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem modelPrims_X25519_kemCorrectWith_zero :
    SignalPqxdh.KemDeltaCorrect (modelPrims X25519 W25519) 0 := by
  unfold SignalPqxdh.KemDeltaCorrect
  have hCorr : ∀ seed r ss ct,
      (modelPrims X25519 W25519).kemEncaps ((modelPrims X25519 W25519).kemKeyGen seed).1 r =
        some (ss, ct) →
      (modelPrims X25519 W25519).kemDecaps ((modelPrims X25519 W25519).kemKeyGen seed).2 ct =
        some ss :=
    modelPrims_kem_corr_of_decaps X25519 W25519 (fun _ _ => rfl)
  simp [SignalPqxdh.kemHonestFail_eq_false_of_kem_corr hCorr]

theorem modelPrims_X25519_cwfδ :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X25519 W25519) :=
  cryptoWellFormedPrimitivesδ_modelPrims X25519 W25519 modelPrims_X25519_cryptoAssumptions
    dh25519_commutes libX25519Rel_c25519 c25519_D_E

abbrev sessionNoopAdv (ℓ : ℕ) :
    SM.Adversary (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
      (BitVec 512) CryptoVerification.E2E.Bytes :=
  (pure false :
    SM.AdversaryComp (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
      (BitVec 512) CryptoVerification.E2E.Bytes Bool)

/-- Joint satisfiability of all hypotheses of `SessionSecure` on a carrier `Pt` of cardinality
`> 2 ^ 251` with point-fiber bound `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem session_hypotheses_satisfiable_prime_order (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep q : ℕ)
      (oa : ProbComp Unit) (_ida _idb : Unit → IdentityKey) (_s : Unit → BitVec 256)
      (A : Unit → SM.Adversary (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
        (BitVec 512) CryptoVerification.E2E.Bytes),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
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
    c25519, K255, dh25519, encPt25519, encT25519, decT25519, 1, 1,
    pure (), (fun _ => bhIdKeyOf []), (fun _ => bhIdKeyOf []), (fun _ => 0),
    (fun _ => sessionNoopAdv ℓ), ?_⟩
  exact ⟨two_pow_251_lt_card_pt25519, by decide, encaps1Total_K255, c25519_D_E, hℓ,
    dh25519_commutes, libX25519Rel_c25519, decT25519_encT25519, encT25519_inj,
    encT25519_ne_dummyKey, dh25519_zero, dh25519_kerUniform,
    show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dh25519_base_fiber_prob_le, fun _ _ => trivial⟩

/-- Instantiates `SessionSecure (Pt := Pt25519) ℓ` with the prime-order witness at
`δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem sessionSecure_prime_order_instantiable (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : SessionSecure (Pt := Pt25519) ℓ) :
    ∃ D : SessionCostedReductionFamily Pt25519 ℓ,
      SessionCostedReductionFamilyBounded ℓ D ∧
      𝒟[(pure () : ProbComp Unit) >>= fun o =>
          SM.gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr c25519 (LibsignalSpqrV1.spqrV1SessionUniformCoins c25519.F K255)
                (bhIdKeyOf []) (bhIdKeyOf []))
              ℓ (0 : BitVec 256))
            3 1 (configRefuseEarlyBobCorr decT25519 encT25519)
            ((fun _ : Unit => sessionNoopAdv ℓ) o)].boolBias ≤
        sessionAdvantageBound ℓ D c25519 K255 dh25519 encPt25519 encT25519 decT25519 1 1
          ((1 : ℝ≥0∞) / 2 ^ 250) (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf [])
          (fun _ => 0) (fun _ => sessionNoopAdv ℓ)
          + 2 * sessionKemFailProb c25519 K255 ℓ decT25519 encT25519 1 (pure ())
            (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
            (fun _ => sessionNoopAdv ℓ) := by
  rcases hSec with ⟨D, hD, hMain⟩
  exact ⟨D, hD, hMain c25519 K255 dh25519 encPt25519 encT25519 decT25519
    encaps1Total_K255 c25519_D_E hℓ dh25519_commutes libX25519Rel_c25519
    decT25519_encT25519 encT25519_ne_dummyKey dh25519_zero dh25519_kerUniform
    1 1 (by decide) ((1 : ℝ≥0∞) / 2 ^ 250) dh25519_base_fiber_prob_le
    (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
    (fun _ => sessionNoopAdv ℓ) (fun _ _ => trivial)⟩

/-- Joint satisfiability of the hypotheses of `LibsignalCliPqSecure` with
`2 ^ 251 < Fintype.card Pt`, `δ_kem = 0`, and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem cli_pq_headline_hypotheses_satisfiable_prime_order
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
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
    pqModelRun X25519 W25519, X25519, W25519, dh25519, encPt25519, encT25519, decT25519,
    1, b1, 1, fun _ => 1, A0, ?_⟩
  exact ⟨two_pow_251_lt_card_pt25519, by decide, by decide,
    cliSpecPq_pqModelRun X25519 W25519, bhEncaps1Total_W25519,
    modelPrims_X25519_cwfδ, modelPrims_X25519_kemCorrectWith_zero, hℓ,
    dh25519_commutes, libX25519Rel_c25519, decT25519_encT25519, encT25519_inj,
    encT25519_ne_dummyKey, dh25519_zero, c25519_D_E, dh25519_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dh25519_base_fiber_prob_le,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Closed specialization of `cli_pq_headline_hypotheses_satisfiable_prime_order` at `N_id = 2`
and `ℓ = 32`. -/
theorem cli_pq_headline_hypotheses_satisfiable_prime_order_concrete :
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
    cli_pq_headline_hypotheses_satisfiable_prime_order S0 32 (by decide)
  exact ⟨S0, 32, Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
    b, qStart, qs, A, by decide, by decide, by decide, by decide, hRest⟩

/-- Joint satisfiability of the prime-order `CliPqxdhElfSecurePlaced` primitive hypotheses with
`W.C.F = sha256Compress`, `W.C.E = CryptoGames.AES256.aes256Enc`, and
`W.C.D = CryptoGames.AES256.aes256Dec`. -/
theorem cli_pq_elf_placed_hypotheses_satisfiable_prime_order
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (W : CliHooks) (X : UnreachedPqxdhPrimitives)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      let Wp : PEParams := ⟨W.C, W.Q⟩
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      W.C.F = sha256Compress ∧
      W.C.E = CryptoGames.AES256.aes256Enc ∧
      W.C.D = CryptoGames.AES256.aes256Dec ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh Wp.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, Wp.C.D k (Wp.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 0, 1, 0⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := cliRoCoinDrAdv S ℓ (BitVec 512)
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨W25519.C, W25519.Q⟩, X25519, dh25519, encPt25519, encT25519, decT25519,
    1, b1, 1, fun _ => 1, A0, ?_⟩
  exact ⟨two_pow_251_lt_card_pt25519, by decide, by decide, rfl, rfl, rfl,
    bhEncaps1Total_W25519, modelPrims_X25519_cwfδ, modelPrims_X25519_kemCorrectWith_zero, hℓ,
    dh25519_commutes, libX25519Rel_c25519, decT25519_encT25519, encT25519_inj,
    encT25519_ne_dummyKey, dh25519_zero, c25519_D_E, dh25519_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dh25519_base_fiber_prob_le,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Instantiates both advantage bounds of `LibsignalCliPqSecure (Pt := Pt25519) S ℓ` with the
prime-order witness at `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem libsignalCliPqSecure_prime_order_instantiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : LibsignalCliPqSecure (Pt := Pt25519) S ℓ) :
    ∃ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      CliPqxdhAdvantage S run X W ℓ qep decT25519 encT25519 A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0 +
          2 * CliKemFailProb S run X W ℓ qep decT25519 encT25519 A ∧
      CliPqxdhAdvantage S run X W ℓ qep decT25519 encT25519 A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 0
               (SignalPqxdh.GapSigEufCma (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X W) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (modelPrims X W).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0
          + 2 * CliKemFailProb S run X W ℓ qep decT25519 encT25519 A := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  rcases hMain (pqModelRun X25519 W25519) X25519 W25519 (cliSpecPq_pqModelRun X25519 W25519)
      bhEncaps1Total_W25519 c25519_D_E modelPrims_X25519_cwfδ 0 modelPrims_X25519_kemCorrectWith_zero
      dh25519 encPt25519 encT25519 decT25519 1 hℓ
      dh25519_commutes libX25519Rel_c25519 decT25519_encT25519 encT25519_ne_dummyKey
      dh25519_zero dh25519_kerUniform
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide)
      ((1 : ℝ≥0∞) / 2 ^ 250) dh25519_base_fiber_prob_le A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨pqModelRun X25519 W25519, X25519, W25519, 1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    hBound1, hBound2 1 (SignalPqxdh.keyIndRoGap_one S (modelPrims X25519 W25519) _)⟩

/-- Joint satisfiability for the `CliSpecPqxdhOrExcusedAbort` specialization of
`CliPqxdhSecurityFor` with `2 ^ 251 < Fintype.card Pt` and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem pqOom_hypotheses_satisfiable_prime_order
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
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
      b, qStart, qs, A, hCard, hqStart, hqs0, hCli, hRest⟩ :=
    cli_pq_headline_hypotheses_satisfiable_prime_order S ℓ hℓ
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
    b, qStart, qs, A, hCard, hqStart, hqs0, hCliOom, hRest⟩

/--
info: 'CryptoVerification.E2E.session_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms session_hypotheses_satisfiable_prime_order

/--
info: 'CryptoVerification.E2E.cli_pq_headline_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cli_pq_headline_hypotheses_satisfiable_prime_order

/--
info: 'CryptoVerification.E2E.pqOom_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqOom_hypotheses_satisfiable_prime_order

/-- Sanity check: `decT25519` computes constructively on the identity encoding `encT25519 0`. -/
example : decT25519 (encT25519 0) = some 0 := by with_unfolding_all rfl

end CryptoVerification.E2E
