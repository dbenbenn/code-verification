/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519Group
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Exact-Uniform `X25519Pt` Sampler and Cost Guard

**Checked by Lean.** Backs `ReductionDsl.AtomicUnifBase.cost .pt = 12` with an explicit,
exact-uniform `ReductionDsl` sampler over the concrete Curve25519 prime-order x-only subgroup
`X25519Pt`:

1. Sample `k` uniformly from `Fin ((edOrderL + 1) / 2)` (a 252-bit integer fitting in one 32-byte
   block, priced at `AtomicUnifBase.cost .bv256 = 1`, matching `I.uCost = 1` for one `unifSpec`
   draw).
2. Return `u([k]B) : X25519Pt` via one fixed-base Curve25519 Montgomery ladder `x25519Ladder k 9`
   (priced at `AtomicGroupOp.cost .ptDh = AtomicPqxdhOp.cost .x25519Base = 8`).

The map `x25519ScalarBasePt : Fin ((edOrderL + 1) / 2) → X25519Pt` sends `0 ↦ 0^32` and
`k ∈ {1, …, (edOrderL - 1) / 2} ↦ u([k]B)` bijectively (`x25519ScalarBasePt_bijective`), so
`x25519PtSamplerComp` has exact distribution `$ᵗ X25519Pt` (`x25519PtSamplerComp_evalDist_eq_unif`).
Its full `ReductionDsl.Comp.cost` is `13` (`1` scalar sample + `8` fixed-base scalar multiplication
+ `4` `Comp` AST steps: `.unit`, `.v0`, `.ret`, `.bind`), matching
`(Comp.sample (UniformSamplerTag.base AtomicUnifBase.pt) .unit).cost = 1 + 12 = 13` exactly
(`x25519PtSamplerComp_cost_eq_atomicPtSample`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Tests.Guards.X25519PtSamplerGuard

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.RFC7748 (X25519Pt x25519ZeroKey isX25519SubgroupKey publicKeyFintype
  x25519Ladder decodeU255)
open ReductionDsl (Sig Ty Ops Samplers Iface Comp Expr OpsSizeHonest SampSizeHonest
  AtomicUnifBase AtomicGroupOp AtomicPqxdhOp UniformSamplerTag atomicSig atomicSamplers)
open VerifiedLibraries.Common (p25519 edOrderL fpAdd fpSub fpMul fpNeg fpInv recoverXEven
  leBytesToNat natToLeBytes EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (montToEdwards isCanonicalX25519)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Ladder_edToMontU edToMontU_edNeg_of_onCurve)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  edOnCurve_x_lt edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg edOnCurve_edAdd
  edOnCurve_edNatSmul edAdd_comm edAdd_assoc edAdd_edZero edZero_edAdd edAdd_edNeg_self
  edNeg_edZero edNatSmul edNatSmul_edZero edNatSmul_one edNatSmul_mul edNatSmul_add
  edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edNatSmul_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_natToLeBytes_of_lt natToLeBytes_leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  edOrderL_prime edOrderL_odd)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_lt edToMontU_edNeg edToMontU_edBasepoint edBasepoint_ne_edZero
  montToEdwards_some_onCurve montToEdwards_some_ne_edZero montToEdwards_some_edToMontU
  montToEdwards_edToMontU edNatSmul_edBasepoint_eq_edZero_iff
  montToEdwards_eq_none_iff_raw montToEdwards_eq_some_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  edToMontU_eq_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  genE edOnCurve_genE edNatSmul_eight_mul_edOrderL_genE genE_exact_order edOnCurve_exists_genE
  edOnCurve_eq_of_edToMontU_eq edNatSmul_gcd_eq_zero edNatSmul_two_eq_zero_iff)

/-! ## 1. Numeric facts and `isX25519SubgroupKey` bridge -/

/-- Exact cardinality `(edOrderL + 1) / 2` of `X25519Pt`. -/
@[expose] def x25519HalfOrder : ℕ := (edOrderL + 1) / 2

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by
  unfold p25519; decide +kernel

private theorem p25519_lt_256_pow_32 : p25519 < 256 ^ 32 := by
  unfold p25519; decide +kernel

private theorem edOrderL_pos : 0 < edOrderL := by
  unfold edOrderL; decide +kernel

private theorem edOrderL_gt_one : 1 < edOrderL := by
  unfold edOrderL; decide +kernel

private theorem edOrderL_lt_two_pow_255 : edOrderL < 2 ^ 255 := by
  unfold edOrderL; decide +kernel

private theorem x25519HalfOrder_pos : 0 < x25519HalfOrder := by
  unfold x25519HalfOrder edOrderL; decide +kernel

instance : NeZero x25519HalfOrder := ⟨Nat.ne_of_gt x25519HalfOrder_pos⟩

private theorem two_mul_x25519HalfOrder : 2 * x25519HalfOrder = edOrderL + 1 := by
  unfold x25519HalfOrder edOrderL; decide +kernel

attribute [local irreducible] fpAdd fpSub fpMul fpNeg fpInv recoverXEven edSmul x25519Ladder

theorem natToLeBytes_len (k n : Nat) : (natToLeBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k _ => simp [natToLeBytes]

private theorem natToLeBytes_zero : ∀ n, natToLeBytes n 0 = List.replicate n 0#8
  | 0 => rfl
  | n + 1 => by simp [natToLeBytes, List.replicate_succ]

private theorem x25519Ladder_zero_nine : x25519Ladder 0 9 = 0 := by
  rw [← edToMontU_edBasepoint, x25519Ladder_edToMontU (by decide +kernel) edOnCurve_edBasepoint]
  exact (edToMontU_eq_zero_iff edOnCurve_edZero).mpr rfl

private def montLiftEdWith (recFn : Nat → Option Nat) (u p1 : Nat) (signOdd : Bool) :
    Option EdPoint :=
  if u == p1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    (recFn y).map fun xEven => ⟨if signOdd then fpNeg xEven else xEven, y⟩

private theorem montLiftEdWith_of_eq (recFn : Nat → Option Nat) (u : Nat) (signOdd : Bool) :
    montLiftEdWith recFn u u signOdd = none := by
  unfold montLiftEdWith; simp

private theorem montLiftEdWith_of_ne_none (recFn : Nat → Option Nat) {u p1 : Nat} (signOdd : Bool)
    (hne : u ≠ p1) (hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = none) :
    montLiftEdWith recFn u p1 signOdd = none := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1)))).map _ = none
  rw [hrec]; rfl

private theorem montLiftEdWith_of_ne_some (recFn : Nat → Option Nat) {u p1 xEven : Nat}
    (signOdd : Bool) (hne : u ≠ p1)
    (hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = some xEven) :
    montLiftEdWith recFn u p1 signOdd =
      some ⟨if signOdd then fpNeg xEven else xEven, fpMul (fpSub u 1) (fpInv (fpAdd u 1))⟩ := by
  unfold montLiftEdWith
  have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hne (beq_iff_eq.mp heq))
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  change (recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1)))).map _ = _
  rw [hrec]; rfl

private theorem decodeU255_eq (bs : List (BitVec 8)) :
    decodeU255 bs = leBytesToNat (bs.take 32) % (2 ^ 255) := rfl

private theorem montLiftEd_eq_liftWith (bs : List (BitVec 8)) :
    SignalPqxdh.montLiftEd bs 0#8 =
      montLiftEdWith recoverXEven
        ((leBytesToNat (bs.take 32) % (2 ^ 255)) % p25519) (p25519 - 1)
        ((0#8 &&& 1#8) == 1#8) :=
  rfl

private theorem montLiftEd_eq_montToEdwards0 (bs : List (BitVec 8)) :
    SignalPqxdh.montLiftEd bs 0#8 = montToEdwards bs 0 := by
  rw [montLiftEd_eq_liftWith, ← decodeU255_eq]
  cases hm : montToEdwards bs 0 with
  | none =>
    rcases (montToEdwards_eq_none_iff_raw bs 0).mp hm with hup | ⟨hne, hrec⟩
    · rw [hup]; exact montLiftEdWith_of_eq _ _ _
    · exact montLiftEdWith_of_ne_none _ _ hne hrec
  | some P =>
    rcases (montToEdwards_eq_some_iff bs 0 P).mp hm with ⟨hne, xEven, hrec, rfl⟩
    rw [montLiftEdWith_of_ne_some _ _ hne hrec]
    rfl

private theorem isX25519SubgroupKey_eq (pk : PublicKey) :
    isX25519SubgroupKey pk = (pk == x25519ZeroKey || isCanonicalX25519 pk.bytes.toList) := by
  unfold isX25519SubgroupKey isCanonicalX25519
  have hlen : pk.bytes.toList.length = 32 := pk.bytes.2
  rw [hlen, beq_self_eq_true, Bool.true_and, montLiftEd_eq_montToEdwards0]
  cases montToEdwards pk.bytes.toList 0 <;> rfl

private theorem isX25519SubgroupKey_iff (pk : PublicKey) :
    isX25519SubgroupKey pk = true ↔
      pk = x25519ZeroKey ∨ isCanonicalX25519 pk.bytes.toList = true := by
  have h := isX25519SubgroupKey_eq pk
  have hbeq : (pk == x25519ZeroKey) = true ↔ pk = x25519ZeroKey := beq_iff_eq
  rw [h, Bool.or_eq_true, hbeq]

private theorem gcd_two_edOrderL : Nat.gcd 2 edOrderL = 1 := by
  have hodd := edOrderL_odd
  have hle : Nat.gcd 2 edOrderL ≤ 2 := Nat.gcd_le_left edOrderL (by decide)
  have hdvd : Nat.gcd 2 edOrderL ∣ edOrderL := Nat.gcd_dvd_right 2 edOrderL
  have hpos : 0 < Nat.gcd 2 edOrderL := Nat.gcd_pos_of_pos_left edOrderL (by decide)
  have hne2 : Nat.gcd 2 edOrderL ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    omega
  omega

private theorem edOnCurve_x_ne_zero_of_prime_order {P : EdPoint}
    (hP : edOnCurve P = true) (hord : edNatSmul edOrderL P = edZero) (hne : P ≠ edZero) :
    P.x ≠ 0 := by
  intro hx0
  have h2 : edNatSmul 2 P = edZero := (edNatSmul_two_eq_zero_iff hP).mpr hx0
  have h1 : edNatSmul 1 P = edZero := by
    rw [← gcd_two_edOrderL]
    exact edNatSmul_gcd_eq_zero hP h2 hord
  rw [edNatSmul_one hP] at h1
  exact hne h1

private theorem edNatSmul_edNeg_eq (n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero => exact edNeg_edZero.symm
  | succ k ih =>
    have hk := edOnCurve_edNatSmul k hP
    have hnegP := edOnCurve_edNeg hP
    have hnegk := edOnCurve_edNeg hk
    have hadd_cancel : edAdd (edAdd (edNatSmul k (edNeg P)) (edNeg P))
        (edAdd (edNatSmul k P) P) = edZero := by
      rw [ih]
      calc
        edAdd (edAdd (edNeg (edNatSmul k P)) (edNeg P)) (edAdd (edNatSmul k P) P)
            = edAdd (edNeg (edNatSmul k P)) (edAdd (edNeg P) (edAdd (edNatSmul k P) P)) :=
              edAdd_assoc hnegk hnegP (edOnCurve_edAdd hk hP)
        _ = edAdd (edNeg (edNatSmul k P)) (edAdd (edNatSmul k P) (edAdd (edNeg P) P)) := by
              rw [edAdd_comm (edNatSmul k P) P,
                  ← edAdd_assoc hnegP hP hk,
                  edAdd_comm (edAdd (edNeg P) P) (edNatSmul k P)]
        _ = edAdd (edNeg (edNatSmul k P)) (edNatSmul k P) := by
              rw [edAdd_comm (edNeg P) P, edAdd_edNeg_self hP, edAdd_edZero hk]
        _ = edZero := by
              rw [edAdd_comm (edNeg (edNatSmul k P)) (edNatSmul k P), edAdd_edNeg_self hk]
    have hsum_on : edOnCurve (edAdd (edNatSmul k P) P) = true := edOnCurve_edAdd hk hP
    have hlhs_on : edOnCurve (edAdd (edNatSmul k (edNeg P)) (edNeg P)) = true :=
      edOnCurve_edAdd (edOnCurve_edNatSmul k hnegP) hnegP
    have hstep := congrArg (fun Q => edAdd Q (edNeg (edAdd (edNatSmul k P) P))) hadd_cancel
    rw [edAdd_assoc hlhs_on hsum_on (edOnCurve_edNeg hsum_on),
        edAdd_edNeg_self hsum_on, edAdd_edZero hlhs_on,
        edZero_edAdd (edOnCurve_edNeg hsum_on)] at hstep
    rw [edAdd_comm (edNatSmul k (edNeg P)) (edNeg P),
        edAdd_comm (edNatSmul k P) P] at hstep
    simpa only [edNatSmul] using hstep

private theorem edOnCurve_eq_or_edNeg_of_edToMontU_eq {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : edToMontU P = edToMontU Q) :
    P = Q ∨ P = edNeg Q := by
  by_cases hpar : P.x % 2 = Q.x % 2
  · exact Or.inl (edOnCurve_eq_of_edToMontU_eq hP hQ hPx hQx hu hpar)
  · right
    have hQneg_on : edOnCurve (edNeg Q) = true := edOnCurve_edNeg hQ
    have hQx_lt : Q.x < p25519 := edOnCurve_x_lt hQ
    have hQx_mod : Q.x % p25519 ≠ 0 := by rwa [Nat.mod_eq_of_lt hQx_lt]
    have hQneg_par : (edNeg Q).x % 2 = 1 - Q.x % 2 := by
      have h := fpNeg_mod_two_of_ne_zero hQx_mod
      change fpNeg Q.x % 2 = 1 - Q.x % 2
      rwa [Nat.mod_eq_of_lt hQx_lt] at h
    have hQneg_x_ne : (edNeg Q).x ≠ 0 := by
      intro h0
      have h1 : (edNeg Q).x % 2 = 0 := by omega
      have hQ0 : edNeg (edNeg Q) = Q := by
        have hadd : edAdd Q (edNeg Q) = edZero := edAdd_edNeg_self hQ
        have h := congrArg (fun R => edAdd R (edNeg (edNeg Q))) hadd
        rw [edAdd_assoc hQ hQneg_on (edOnCurve_edNeg hQneg_on),
             edAdd_edNeg_self hQneg_on, edAdd_edZero hQ,
             edZero_edAdd (edOnCurve_edNeg hQneg_on)] at h
        exact h.symm
      have h2Q : edNatSmul 2 (edNeg Q) = edZero := (edNatSmul_two_eq_zero_iff hQneg_on).mpr h0
      rw [edNatSmul_edNeg_eq 2 hQ] at h2Q
      have h2Q' : edNatSmul 2 Q = edZero := by
        have h := congrArg edNeg h2Q
        rw [edNeg_edZero] at h
        have h_on := edOnCurve_edNatSmul 2 hQ
        have hinv : edNeg (edNeg (edNatSmul 2 Q)) = edNatSmul 2 Q := by
          have ha : edAdd (edNatSmul 2 Q) (edNeg (edNatSmul 2 Q)) = edZero :=
            edAdd_edNeg_self h_on
          have hb := congrArg (fun R => edAdd R (edNeg (edNeg (edNatSmul 2 Q)))) ha
          rw [edAdd_assoc h_on (edOnCurve_edNeg h_on) (edOnCurve_edNeg (edOnCurve_edNeg h_on)),
               edAdd_edNeg_self (edOnCurve_edNeg h_on), edAdd_edZero h_on,
               edZero_edAdd (edOnCurve_edNeg (edOnCurve_edNeg h_on))] at hb
          exact hb.symm
        rwa [hinv] at h
      exact hQx ((edNatSmul_two_eq_zero_iff hQ).mp h2Q')
    have hu' : edToMontU P = edToMontU (edNeg Q) := by
      rw [hu, edToMontU_edNeg_of_onCurve hQ]
    exact edOnCurve_eq_of_edToMontU_eq hP hQneg_on hPx hQneg_x_ne hu' (by omega)

/-! ## 2. Exact bijection `Fin ((edOrderL + 1) / 2) ≃ X25519Pt` -/

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

private theorem isCanonicalX25519_eq_true_iff (bs : List (BitVec 8)) :
    isCanonicalX25519 bs = true ↔
      bs.length = 32 ∧ leBytesToNat bs < p25519 ∧
      ∃ P, montToEdwards bs 0 = some P ∧ edSmul edOrderL P = edZero := by
  constructor
  · intro h
    have h1 : ((bs.length == 32 && decide (leBytesToNat bs < p25519)) &&
        match montToEdwards bs 0 with
        | none => false | some P => edSmul edOrderL P == edZero) = true := h
    obtain ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨hlen, hlt⟩ := (Bool.and_eq_true _ _).mp hhead
    obtain ⟨P, hm, heq⟩ := match_edPoint_eq_true _ (fun P => edSmul edOrderL P == edZero) htail
    exact ⟨beq_iff_eq.mp hlen, of_decide_eq_true hlt, P, hm, beq_iff_eq.mp heq⟩
  · rintro ⟨hlen, hlt, P, hm, heq⟩
    have hhead : (bs.length == 32 && decide (leBytesToNat bs < p25519)) = true :=
      (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hlen, decide_eq_true hlt⟩
    have htail : (match montToEdwards bs 0 with
        | none => false | some P => edSmul edOrderL P == edZero) = true :=
      match_edPoint_of_some _ P (fun P => edSmul edOrderL P == edZero) hm (beq_iff_eq.mpr heq)
    exact (Bool.and_eq_true _ _).mpr ⟨hhead, htail⟩

/-- Montgomery u-coordinate `PublicKey` of `[k]B` (`0^32` at `k = 0`). -/
@[expose] def x25519ScalarBaseKey (k : Fin x25519HalfOrder) : PublicKey :=
  ⟨⟨natToLeBytes 32 (x25519Ladder k.val 9), natToLeBytes_len 32 _⟩⟩

theorem isX25519SubgroupKey_scalarBaseKey (k : Fin x25519HalfOrder) :
    isX25519SubgroupKey (x25519ScalarBaseKey k) = true := by
  rw [isX25519SubgroupKey_iff]
  by_cases hk0 : k.val = 0
  · left
    apply congrArg PublicKey.mk
    apply List.Vector.eq
    change natToLeBytes 32 (x25519Ladder k.val 9) = List.replicate 32 0#8
    rw [hk0, x25519Ladder_zero_nine, natToLeBytes_zero]
  · right
    have hlt_l : k.val < edOrderL := by have := k.isLt; have := two_mul_x25519HalfOrder; omega
    have hlt_255 : k.val < 2 ^ 255 := Nat.lt_trans hlt_l edOrderL_lt_two_pow_255
    have hpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    set P : EdPoint := edNatSmul k.val edBasepoint
    have hP_on : edOnCurve P = true := edOnCurve_edNatSmul k.val edOnCurve_edBasepoint
    have hP_ne : P ≠ edZero := by
      intro h0
      have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff k.val).mp h0
      exact Nat.not_dvd_of_pos_of_lt hpos hlt_l hdvd
    have hP_ord : edNatSmul edOrderL P = edZero := by
      dsimp only [P]
      rw [← edNatSmul_mul edOrderL k.val edOnCurve_edBasepoint,
          Nat.mul_comm edOrderL k.val,
          edNatSmul_mul k.val edOrderL edOnCurve_edBasepoint,
          edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
    have hladder : x25519Ladder k.val 9 = edToMontU P := by
      rw [← edToMontU_edBasepoint, x25519Ladder_edToMontU hlt_255 edOnCurve_edBasepoint]
    have hu_lt : edToMontU P < p25519 := edToMontU_lt P
    have hu_lt_256 : edToMontU P < 256 ^ 32 := Nat.lt_trans hu_lt p25519_lt_256_pow_32
    change isCanonicalX25519 (natToLeBytes 32 (x25519Ladder k.val 9)) = true
    rw [hladder]
    have hPx_ne : P.x ≠ 0 := edOnCurve_x_ne_zero_of_prime_order hP_on hP_ord hP_ne
    have hPx_lt : P.x < p25519 := edOnCurve_x_lt hP_on
    have hlift : ∃ Q : EdPoint, montToEdwards (natToLeBytes 32 (edToMontU P)) 0 = some Q ∧
        edOnCurve Q = true ∧ edNatSmul edOrderL Q = edZero := by
      by_cases heven : P.x % 2 = 0
      · refine ⟨P, ?_, hP_on, hP_ord⟩
        have h := montToEdwards_edToMontU hP_on hP_ne
        rwa [heven] at h
      · have hPx_mod : P.x % p25519 ≠ 0 := by rwa [Nat.mod_eq_of_lt hPx_lt]
        have hneg_even : (edNeg P).x % 2 = 0 := by
          have h := fpNeg_mod_two_of_ne_zero hPx_mod
          rw [Nat.mod_eq_of_lt hPx_lt] at h
          change fpNeg P.x % 2 = 0
          omega
        have hneg_on : edOnCurve (edNeg P) = true := edOnCurve_edNeg hP_on
        have hneg_ne : edNeg P ≠ edZero := by
          intro h0
          have h1 := congrArg (edAdd P) h0
          rw [edAdd_edNeg_self hP_on, edAdd_edZero hP_on] at h1
          exact hP_ne h1.symm
        have hneg_ord : edNatSmul edOrderL (edNeg P) = edZero := by
          rw [edNatSmul_edNeg_eq edOrderL hP_on, hP_ord, edNeg_edZero]
        refine ⟨edNeg P, ?_, hneg_on, hneg_ord⟩
        have h := montToEdwards_edToMontU hneg_on hneg_ne
        rw [hneg_even, edToMontU_edNeg_of_onCurve hP_on] at h
        exact h
    rcases hlift with ⟨Q, hQ_lift, hQ_on, hQ_ord⟩
    have hQ_smul : edSmul edOrderL Q = edZero := by
      rw [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hQ_on, hQ_ord]
    exact (isCanonicalX25519_eq_true_iff _).mpr
      ⟨natToLeBytes_len _ _, by rwa [leBytesToNat_natToLeBytes_of_lt hu_lt_256], Q, hQ_lift, hQ_smul⟩

/-- Bijective map `Fin ((edOrderL + 1) / 2) → X25519Pt` computing `u([k]B)` via one fixed-base
Curve25519 Montgomery ladder. -/
@[expose] def x25519ScalarBasePt (k : Fin x25519HalfOrder) : X25519Pt :=
  ⟨x25519ScalarBaseKey k, isX25519SubgroupKey_scalarBaseKey k⟩

private theorem edNatSmul_mod_eight_mul_edOrderL_genE (n : Nat) :
    edNatSmul n genE = edNatSmul (n % (8 * edOrderL)) genE := by
  have hdiv : n = 8 * edOrderL * (n / (8 * edOrderL)) + n % (8 * edOrderL) :=
    (Nat.div_add_mod n (8 * edOrderL)).symm
  conv_lhs => rw [hdiv]
  rw [edNatSmul_add _ _ edOnCurve_genE,
      Nat.mul_comm (8 * edOrderL),
      edNatSmul_mul _ (8 * edOrderL) edOnCurve_genE,
      edNatSmul_eight_mul_edOrderL_genE, edNatSmul_edZero,
      edZero_edAdd (edOnCurve_edNatSmul _ edOnCurve_genE)]

private theorem eight_dvd_of_edNatSmul_edOrderL_genE {i : Nat}
    (hord : edNatSmul edOrderL (edNatSmul i genE) = edZero) : 8 ∣ i := by
  have hmul : edNatSmul (edOrderL * i) genE = edZero := by
    rw [edNatSmul_mul edOrderL i edOnCurve_genE]
    exact hord
  rw [edNatSmul_mod_eight_mul_edOrderL_genE] at hmul
  have hmod0 : (edOrderL * i) % (8 * edOrderL) = 0 := by
    by_contra hne
    have hpos : 0 < (edOrderL * i) % (8 * edOrderL) := Nat.pos_of_ne_zero hne
    have hlt : (edOrderL * i) % (8 * edOrderL) < 8 * edOrderL :=
      Nat.mod_lt _ (by have := edOrderL_pos; omega)
    exact genE_exact_order hpos hlt hmul
  have hdvd : 8 * edOrderL ∣ edOrderL * i := Nat.dvd_of_mod_eq_zero hmod0
  rw [Nat.mul_comm 8 edOrderL] at hdvd
  exact (Nat.mul_dvd_mul_iff_left edOrderL_pos).mp hdvd

private theorem exists_edNatSmul_edBasepoint_of_prime_order {P : EdPoint}
    (hP : edOnCurve P = true) (hord : edNatSmul edOrderL P = edZero) :
    ∃ m : Nat, m < edOrderL ∧ P = edNatSmul m edBasepoint := by
  obtain ⟨b, hb_lt, hb_eq⟩ := edOnCurve_exists_genE edOnCurve_edBasepoint
  obtain ⟨i, hi_lt, hi_eq⟩ := edOnCurve_exists_genE hP
  have hb_ord : edNatSmul edOrderL (edNatSmul b genE) = edZero := by
    rw [← hb_eq]; exact edNatSmul_edOrderL_edBasepoint
  have hi_ord : edNatSmul edOrderL (edNatSmul i genE) = edZero := by
    rw [← hi_eq]; exact hord
  obtain ⟨b0, hb0_eq⟩ := eight_dvd_of_edNatSmul_edOrderL_genE hb_ord
  obtain ⟨i0, hi0_eq⟩ := eight_dvd_of_edNatSmul_edOrderL_genE hi_ord
  have hb0_lt : b0 < edOrderL := by omega
  have hi0_lt : i0 < edOrderL := by omega
  have hb0_pos : 0 < b0 := by
    by_contra h0
    have hb0 : b0 = 0 := by omega
    rw [hb0, Nat.mul_zero] at hb0_eq
    rw [hb0_eq] at hb_eq
    exact edBasepoint_ne_edZero hb_eq
  have hgcd : Nat.gcd b0 edOrderL = 1 := by
    have hdvd_l : Nat.gcd b0 edOrderL ∣ edOrderL := Nat.gcd_dvd_right b0 edOrderL
    rcases edOrderL_prime.2 _ hdvd_l with h1 | hl
    · exact h1
    · have hdvd_b0 : edOrderL ∣ b0 := hl ▸ Nat.gcd_dvd_left b0 edOrderL
      exact absurd hdvd_b0 (Nat.not_dvd_of_pos_of_lt hb0_pos hb0_lt)
  -- Find `m < edOrderL` with `b0 * m ≡ i0 (mod edOrderL)` via Bezout (`Int.gcdA`).
  let invB : Nat := (Int.gcdA (b0 : Int) (edOrderL : Int) % (edOrderL : Int)).toNat
  have hBez : (b0 : Int) * Int.gcdA (b0 : Int) (edOrderL : Int) +
      (edOrderL : Int) * Int.gcdB (b0 : Int) (edOrderL : Int) = 1 := by
    have h := Int.gcd_eq_gcd_ab (b0 : Int) (edOrderL : Int)
    have hg : Int.gcd (b0 : Int) (edOrderL : Int) = 1 := by
      simpa only [Int.gcd_natCast_natCast] using hgcd
    rw [hg] at h
    exact h.symm
  have hl_pos_z : (0 : Int) < (edOrderL : Int) := by have := edOrderL_pos; omega
  have hinvB_mod : (invB : Int) = Int.gcdA (b0 : Int) (edOrderL : Int) % (edOrderL : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hl_pos_z))
  have hmul_mod_z : ((b0 * invB : Nat) : Int) % (edOrderL : Int) = 1 % (edOrderL : Int) := by
    rw [Int.natCast_mul, hinvB_mod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    have h1 : (b0 : Int) * Int.gcdA (b0 : Int) (edOrderL : Int) =
        1 + (edOrderL : Int) * (-Int.gcdB (b0 : Int) (edOrderL : Int)) := by linarith
    rw [h1, Int.add_mul_emod_self_left]
  have hmul_mod : (b0 * invB) % edOrderL = 1 := by
    have h1 : (1 : Int) % (edOrderL : Int) = 1 :=
      Int.emod_eq_of_lt (by omega) (by have := edOrderL_gt_one; omega)
    rw [h1] at hmul_mod_z
    have hcast : (((b0 * invB) % edOrderL : Nat) : Int) = (1 : Nat) := by
      simpa [Int.natCast_emod] using hmul_mod_z
    exact Int.ofNat.inj hcast
  let m : Nat := (invB * i0) % edOrderL
  have hm_lt : m < edOrderL := Nat.mod_lt _ edOrderL_pos
  have hbm_mod : (b0 * m) % edOrderL = i0 := by
    dsimp only [m]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc,
        Nat.mul_mod (b0 * invB), hmul_mod, Nat.one_mul, Nat.mod_mod,
        Nat.mod_eq_of_lt hi0_lt]
  refine ⟨m, hm_lt, ?_⟩
  rw [hi_eq, hb_eq, hb0_eq, hi0_eq,
      ← edNatSmul_mul m (8 * b0) edOnCurve_genE,
      show m * (8 * b0) = 8 * (b0 * m) by ring,
      edNatSmul_mod_eight_mul_edOrderL_genE (8 * (b0 * m)),
      Nat.mul_mod_mul_left, hbm_mod]

theorem x25519ScalarBasePt_injective : Function.Injective x25519ScalarBasePt := by
  intro k₁ k₂ hEq
  have hbytes : natToLeBytes 32 (x25519Ladder k₁.val 9) = natToLeBytes 32 (x25519Ladder k₂.val 9) :=
    congrArg (fun Q : X25519Pt => Q.val.bytes.toList) hEq
  have hlt1 : k₁.val < edOrderL := by have := k₁.isLt; have := two_mul_x25519HalfOrder; omega
  have hlt2 : k₂.val < edOrderL := by have := k₂.isLt; have := two_mul_x25519HalfOrder; omega
  have hlt1_255 : k₁.val < 2 ^ 255 := Nat.lt_trans hlt1 edOrderL_lt_two_pow_255
  have hlt2_255 : k₂.val < 2 ^ 255 := Nat.lt_trans hlt2 edOrderL_lt_two_pow_255
  have hladder_lt : ∀ k : Fin x25519HalfOrder, x25519Ladder k.val 9 < 256 ^ 32 := by
    intro k
    have hlt_k : k.val < 2 ^ 255 :=
      Nat.lt_trans (by have := k.isLt; have := two_mul_x25519HalfOrder; omega)
        edOrderL_lt_two_pow_255
    rw [← edToMontU_edBasepoint, x25519Ladder_edToMontU hlt_k edOnCurve_edBasepoint]
    exact Nat.lt_trans (edToMontU_lt _) p25519_lt_256_pow_32
  have hu_eq : x25519Ladder k₁.val 9 = x25519Ladder k₂.val 9 := by
    have h1 := congrArg leBytesToNat hbytes
    rwa [leBytesToNat_natToLeBytes_of_lt (hladder_lt k₁),
         leBytesToNat_natToLeBytes_of_lt (hladder_lt k₂)] at h1
  have hnz_u_ne0 : ∀ k : Fin x25519HalfOrder, 0 < k.val → x25519Ladder k.val 9 ≠ 0 := by
    intro k hkpos hu0
    have hlt_k : k.val < edOrderL := by have := k.isLt; have := two_mul_x25519HalfOrder; omega
    have hlt_k255 : k.val < 2 ^ 255 := Nat.lt_trans hlt_k edOrderL_lt_two_pow_255
    rw [← edToMontU_edBasepoint, x25519Ladder_edToMontU hlt_k255 edOnCurve_edBasepoint] at hu0
    set P := edNatSmul k.val edBasepoint
    have hP_on : edOnCurve P = true := edOnCurve_edNatSmul k.val edOnCurve_edBasepoint
    have hP_ne : P ≠ edZero := by
      intro h0
      exact Nat.not_dvd_of_pos_of_lt hkpos hlt_k ((edNatSmul_edBasepoint_eq_edZero_iff k.val).mp h0)
    have hP_ord : edNatSmul edOrderL P = edZero := by
      dsimp only [P]
      rw [← edNatSmul_mul edOrderL k.val edOnCurve_edBasepoint, Nat.mul_comm,
          edNatSmul_mul k.val edOrderL edOnCurve_edBasepoint,
          edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
    have hPx_ne : P.x ≠ 0 := edOnCurve_x_ne_zero_of_prime_order hP_on hP_ord hP_ne
    exact hPx_ne ((edToMontU_eq_zero_iff hP_on).mp hu0)
  by_cases h1 : k₁.val = 0
  · by_cases h2 : k₂.val = 0
    · exact Fin.ext (by omega)
    · rw [h1, x25519Ladder_zero_nine] at hu_eq
      exact absurd hu_eq.symm (hnz_u_ne0 k₂ (Nat.pos_of_ne_zero h2))
  · by_cases h2 : k₂.val = 0
    · rw [h2, x25519Ladder_zero_nine] at hu_eq
      exact absurd hu_eq (hnz_u_ne0 k₁ (Nat.pos_of_ne_zero h1))
    · have hpos1 : 0 < k₁.val := Nat.pos_of_ne_zero h1
      have hpos2 : 0 < k₂.val := Nat.pos_of_ne_zero h2
      rw [← edToMontU_edBasepoint,
          x25519Ladder_edToMontU hlt1_255 edOnCurve_edBasepoint,
          x25519Ladder_edToMontU hlt2_255 edOnCurve_edBasepoint] at hu_eq
      set P₁ := edNatSmul k₁.val edBasepoint
      set P₂ := edNatSmul k₂.val edBasepoint
      have hP₁_on : edOnCurve P₁ = true := edOnCurve_edNatSmul k₁.val edOnCurve_edBasepoint
      have hP₂_on : edOnCurve P₂ = true := edOnCurve_edNatSmul k₂.val edOnCurve_edBasepoint
      have hP₁_ne : P₁ ≠ edZero := fun h0 =>
        Nat.not_dvd_of_pos_of_lt hpos1 hlt1 ((edNatSmul_edBasepoint_eq_edZero_iff k₁.val).mp h0)
      have hP₂_ne : P₂ ≠ edZero := fun h0 =>
        Nat.not_dvd_of_pos_of_lt hpos2 hlt2 ((edNatSmul_edBasepoint_eq_edZero_iff k₂.val).mp h0)
      have hP₁_ord : edNatSmul edOrderL P₁ = edZero := by
        dsimp only [P₁]
        rw [← edNatSmul_mul edOrderL k₁.val edOnCurve_edBasepoint, Nat.mul_comm,
            edNatSmul_mul k₁.val edOrderL edOnCurve_edBasepoint,
            edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
      have hP₂_ord : edNatSmul edOrderL P₂ = edZero := by
        dsimp only [P₂]
        rw [← edNatSmul_mul edOrderL k₂.val edOnCurve_edBasepoint, Nat.mul_comm,
            edNatSmul_mul k₂.val edOrderL edOnCurve_edBasepoint,
            edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]
      have hP₁_x : P₁.x ≠ 0 := edOnCurve_x_ne_zero_of_prime_order hP₁_on hP₁_ord hP₁_ne
      have hP₂_x : P₂.x ≠ 0 := edOnCurve_x_ne_zero_of_prime_order hP₂_on hP₂_ord hP₂_ne
      rcases edOnCurve_eq_or_edNeg_of_edToMontU_eq hP₁_on hP₂_on hP₁_x hP₂_x hu_eq with
        heq | hneg
      · by_cases hle : k₁.val ≤ k₂.val
        · have hsub : edNatSmul (k₂.val - k₁.val) edBasepoint = edZero := by
            have hsum : edAdd (edNatSmul (k₂.val - k₁.val) edBasepoint) P₁ = P₂ := by
              dsimp only [P₁, P₂]
              rw [← edNatSmul_add _ _ edOnCurve_edBasepoint, Nat.sub_add_cancel hle]
            rw [← heq] at hsum
            have h := congrArg (fun Q => edAdd Q (edNeg P₁)) hsum
            rwa [edAdd_assoc (edOnCurve_edNatSmul _ edOnCurve_edBasepoint) hP₁_on
                   (edOnCurve_edNeg hP₁_on),
                 edAdd_edNeg_self hP₁_on,
                 edAdd_edZero (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)] at h
          have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff _).mp hsub
          by_cases hdiff : k₂.val - k₁.val = 0
          · exact Fin.ext (by omega)
          · exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
        · have hsub : edNatSmul (k₁.val - k₂.val) edBasepoint = edZero := by
            have hsum : edAdd (edNatSmul (k₁.val - k₂.val) edBasepoint) P₂ = P₁ := by
              dsimp only [P₁, P₂]
              rw [← edNatSmul_add _ _ edOnCurve_edBasepoint, Nat.sub_add_cancel (by omega)]
            rw [heq] at hsum
            have h := congrArg (fun Q => edAdd Q (edNeg P₂)) hsum
            rwa [edAdd_assoc (edOnCurve_edNatSmul _ edOnCurve_edBasepoint) hP₂_on
                   (edOnCurve_edNeg hP₂_on),
                 edAdd_edNeg_self hP₂_on,
                 edAdd_edZero (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)] at h
          have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff _).mp hsub
          exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      · have hsum : edNatSmul (k₁.val + k₂.val) edBasepoint = edZero := by
          rw [edNatSmul_add k₁.val k₂.val edOnCurve_edBasepoint]
          change edAdd P₁ P₂ = edZero
          rw [hneg, edAdd_comm (edNeg P₂) P₂, edAdd_edNeg_self hP₂_on]
        have hdvd := (edNatSmul_edBasepoint_eq_edZero_iff _).mp hsum
        have hsum_lt : k₁.val + k₂.val < edOrderL := by
          have := k₁.isLt; have := k₂.isLt; have := two_mul_x25519HalfOrder; omega
        exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by omega) hsum_lt)

theorem x25519ScalarBasePt_surjective : Function.Surjective x25519ScalarBasePt := by
  intro Q
  rcases (isX25519SubgroupKey_iff Q.val).mp Q.property with h0 | hcan
  · refine ⟨⟨0, x25519HalfOrder_pos⟩, Subtype.ext ?_⟩
    rw [h0]
    apply congrArg PublicKey.mk
    apply List.Vector.eq
    change natToLeBytes 32 (x25519Ladder 0 9) = List.replicate 32 0#8
    rw [x25519Ladder_zero_nine, natToLeBytes_zero]
  · have hlen : Q.val.bytes.toList.length = 32 := Q.val.bytes.2
    rcases (isCanonicalX25519_eq_true_iff _).mp hcan with ⟨_, hu_lt, P, hm, hsmul⟩
    have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hm
    have hP_ne : P ≠ edZero := montToEdwards_some_ne_edZero hm
    have hP_u : edToMontU P = decodeU255 Q.val.bytes.toList % p25519 :=
      montToEdwards_some_edToMontU hm
    have hP_ord : edNatSmul edOrderL P = edZero := by
      rwa [edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on] at hsmul
    obtain ⟨m, hm_lt, hP_eq⟩ := exists_edNatSmul_edBasepoint_of_prime_order hP_on hP_ord
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      rw [hm0] at hP_eq
      exact hP_ne hP_eq
    have h2half := two_mul_x25519HalfOrder
    let kVal : Nat := if m < x25519HalfOrder then m else edOrderL - m
    have hkVal_lt : kVal < x25519HalfOrder := by dsimp only [kVal]; split <;> omega
    have hkVal_255 : kVal < 2 ^ 255 :=
      Nat.lt_trans (by omega) edOrderL_lt_two_pow_255
    have hu_kVal : x25519Ladder kVal 9 = edToMontU P := by
      rw [← edToMontU_edBasepoint, x25519Ladder_edToMontU hkVal_255 edOnCurve_edBasepoint]
      dsimp only [kVal]
      split
      · rw [hP_eq]
      · have hneg_eq : edNatSmul (edOrderL - m) edBasepoint = edNeg P := by
          have hadd : edAdd (edNatSmul (edOrderL - m) edBasepoint) P = edZero := by
            rw [hP_eq, ← edNatSmul_add _ _ edOnCurve_edBasepoint,
                Nat.sub_add_cancel (Nat.le_of_lt hm_lt), edNatSmul_edOrderL_edBasepoint]
          have h := congrArg (fun R => edAdd R (edNeg P)) hadd
          rwa [edAdd_assoc (edOnCurve_edNatSmul _ edOnCurve_edBasepoint) hP_on
                 (edOnCurve_edNeg hP_on),
               edAdd_edNeg_self hP_on,
               edAdd_edZero (edOnCurve_edNatSmul _ edOnCurve_edBasepoint),
               edZero_edAdd (edOnCurve_edNeg hP_on)] at h
        rw [hneg_eq, edToMontU_edNeg_of_onCurve hP_on]
    have hdec_eq : decodeU255 Q.val.bytes.toList % p25519 = leBytesToNat Q.val.bytes.toList := by
      unfold decodeU255
      rw [List.take_of_length_le (by omega)]
      rw [Nat.mod_eq_of_lt (Nat.lt_trans hu_lt p25519_lt_two_pow_255), Nat.mod_eq_of_lt hu_lt]
    refine ⟨⟨kVal, hkVal_lt⟩, Subtype.ext ?_⟩
    apply congrArg PublicKey.mk
    apply List.Vector.eq
    change natToLeBytes 32 (x25519Ladder kVal 9) = Q.val.bytes.toList
    rw [hu_kVal, hP_u, hdec_eq]
    have hnat := natToLeBytes_leBytesToNat Q.val.bytes.toList
    rwa [hlen] at hnat

theorem x25519ScalarBasePt_bijective : Function.Bijective x25519ScalarBasePt :=
  ⟨x25519ScalarBasePt_injective, x25519ScalarBasePt_surjective⟩

/-- Exact equivalence `Fin ((edOrderL + 1) / 2) ≃ X25519Pt`. -/
noncomputable def x25519ScalarBaseEquiv : Fin x25519HalfOrder ≃ X25519Pt :=
  Equiv.ofBijective x25519ScalarBasePt x25519ScalarBasePt_bijective

/-! ## 3. Explicit `ReductionDsl` sampler program, uniformity, and exact cost match -/

/-- Minimal `ReductionDsl` signature for the explicit `X25519Pt` uniform sampler:
a 252-bit scalar in `Fin ((edOrderL + 1) / 2)` (1 32-byte block) and a subgroup point `X25519Pt`
(1 32-byte block). -/
inductive X25519SamplerSort where
  | scalar | pt
  deriving DecidableEq

@[expose, reducible] def x25519PtSamplerSig : Sig where
  Base := X25519SamplerSort
  den
    | .scalar => Fin x25519HalfOrder
    | .pt => X25519Pt
  sz _ _ := 1

/-- Uniform scalar draw `$ᵗ (Fin ((edOrderL + 1) / 2))`, priced at `AtomicUnifBase.cost .bv256 = 1`
(one 256-bit block, matching `I.uCost = 1` for one `unifSpec` draw). -/
@[expose, reducible] def x25519PtSamplerSamplers : Samplers x25519PtSamplerSig where
  Samp := Unit
  sDom := fun _ => .unit
  sTy := fun _ => .base X25519SamplerSort.scalar
  samp := fun _ _ => $ᵗ (Fin x25519HalfOrder)
  sCost := fun _ => AtomicUnifBase.cost .bv256

/-- Fixed-base Curve25519 scalar multiplication `k ↦ u([k]B) : X25519Pt`, priced at
`AtomicGroupOp.cost .ptDh = AtomicPqxdhOp.cost .x25519Base = 8`. -/
@[expose, reducible] def x25519PtSamplerOps : Ops x25519PtSamplerSig where
  Op := Unit
  dom := fun _ => .base X25519SamplerSort.scalar
  cod := fun _ => .base X25519SamplerSort.pt
  eval := fun _ k => x25519ScalarBasePt k
  cost := fun _ => AtomicGroupOp.cost .ptDh

/-- Coin-only `ProbComp` interface carrying `x25519PtSamplerSamplers`. -/
@[expose, reducible] def x25519PtSamplerIface : Iface x25519PtSamplerSig unifSpec where
  fwdU := QueryImpl.id' unifSpec
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun g _ => g.elim
  dec := fun g _ => g.elim
  qCost := Empty.elim
  smp := x25519PtSamplerSamplers

/-- Explicit 2-step exact-uniform `X25519Pt` sampler in `ReductionDsl`:
`k ← $ᵗ (Fin ((edOrderL + 1) / 2)); return x25519ScalarBasePt k`. -/
@[expose] def x25519PtSamplerComp :
    Comp x25519PtSamplerOps x25519PtSamplerIface [] (.base X25519SamplerSort.pt) :=
  .bind (.sample () .unit) (.ret (.op () .v0))

theorem x25519PtSamplerSamplers_sizeHonest : SampSizeHonest x25519PtSamplerSamplers := by
  intro _ _ B _ _ _
  change 1 ≤ B + 1
  omega

theorem x25519PtSamplerOps_sizeHonest : OpsSizeHonest x25519PtSamplerOps := by
  intro _ _ B _
  change 1 ≤ B + 8
  omega

private theorem x25519PtSampler_liftP_id {α : Type} (p : ProbComp α) :
    x25519PtSamplerIface.liftP p = p := by
  unfold Iface.liftP
  have hid : (fun n => x25519PtSamplerIface.fwdU n : QueryImpl unifSpec ProbComp) =
      QueryImpl.id' unifSpec := by
    funext n
    rfl
  rw [hid, simulateQ_id']

/-- The explicit `ReductionDsl` sampler `x25519PtSamplerComp` produces the exact uniform
distribution on `X25519Pt`. -/
theorem x25519PtSamplerComp_evalDist_eq_unif :
    letI : MeasurableSpace X25519Pt := ⊤
    𝒟[x25519PtSamplerComp.eval .nil] = 𝒟[($ᵗ X25519Pt : ProbComp X25519Pt)] := by
  let _ : MeasurableSpace X25519Pt := ⊤
  let _ : DiscreteMeasurableSpace X25519Pt := ⟨fun _ => trivial⟩
  let _ : Fintype X25519Pt := @Subtype.fintype PublicKey
    (fun pk => isX25519SubgroupKey pk = true) inferInstance publicKeyFintype
  have heval : x25519PtSamplerComp.eval .nil =
      x25519ScalarBaseEquiv <$> ($ᵗ (Fin x25519HalfOrder) : ProbComp (Fin x25519HalfOrder)) := by
    change (x25519PtSamplerIface.liftP ($ᵗ (Fin x25519HalfOrder))) >>=
        (fun k => pure (x25519ScalarBasePt k)) = _
    rw [x25519PtSampler_liftP_id, map_eq_bind_pure_comp]
    rfl
  rw [heval]
  have hcard : Fintype.card (Fin x25519HalfOrder) = Fintype.card X25519Pt :=
    Fintype.card_congr x25519ScalarBaseEquiv
  apply Measure.ext_of_singleton
  intro Q
  rw [evalDist_map_of_discrete, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton Q)]
  have hpre : x25519ScalarBaseEquiv ⁻¹' {Q} = {x25519ScalarBaseEquiv.symm Q} := by
    ext k
    simp [Equiv.eq_symm_apply]
  rw [hpre, SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample]
  have h1 := ProbabilityTheory.uniformOn_apply_finset
    (s := (Finset.univ : Finset (Fin x25519HalfOrder))) (t := {x25519ScalarBaseEquiv.symm Q})
  have h2 := ProbabilityTheory.uniformOn_apply_finset
    (s := (Finset.univ : Finset X25519Pt)) (t := {Q})
  simp only [Finset.coe_univ, Finset.coe_singleton, Finset.univ_inter, Finset.card_singleton,
    Nat.cast_one, Finset.card_univ] at h1 h2
  rw [h1, h2, hcard]

/-- `AtomicUnifBase.cost .pt` is `12`. -/
theorem atomicUnifBase_pt_cost : AtomicUnifBase.cost .pt = 12 := rfl

/-- `x25519PtSamplerComp` has exact `ReductionDsl.Comp.cost` equal to `13`
(`1` scalar sample + `8` fixed-base scalar multiplication + `4` `Comp` AST glue steps). -/
theorem x25519PtSamplerComp_cost : x25519PtSamplerComp.cost = 13 := rfl

/-- Every `Comp.sample (UniformSamplerTag.base AtomicUnifBase.pt) .unit` in `atomicSamplers` pays
the exact `Comp.cost` (`13`) of the explicit exact-uniform sampler `x25519PtSamplerComp`. -/
theorem x25519PtSamplerComp_cost_eq_atomicPtSample (ℓ : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ X25519Pt) T} (hSmp : I.smp = atomicSamplers ℓ X25519Pt)
    (O : Ops (atomicSig ℓ X25519Pt)) :
    x25519PtSamplerComp.cost =
      (by
        rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
        dsimp only at hSmp; subst hSmp
        exact (Comp.sample (O := O)
          (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ X25519Pt⟩)
          (Γ := []) (UniformSamplerTag.base AtomicUnifBase.pt) .unit).cost) := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hSmp
  subst hSmp
  rfl

end Computational.Tests.Guards.X25519PtSamplerGuard
