/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbNafMath -- proof-setup: allow-public-import

/-!
# Straus Double-Scalar Multiplication Bridge (`LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge`)

Pure `0-sorry` mathematical bridge proving `dsmb_compress_eq`:
`encodeEd (edExtToAffine (edDoubleScalarMulBasepoint k_bs negA_bs s_bs)) =`
`encodeEd (edSub (edSmul (leBytesToNat s_bs) edBasepoint) (edSmul (leBytesToNat k_bs) Apt))`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  p25519 edOrderL fpPow fpInv EdPoint EdExtPoint edExtZero edExtOfAffine edExtToAffine
  edBasepoint edOnCurve edExtAdd edAdd edNeg edSub edSmul leBytesToNat encodeEd recoverXEven
  decodeEdDalek)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  oddMultiplesBasepointBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51ValAt fe51Point4Bounded edExtOfBytes edExtNeg edProjDouble edAddProjNiels edSubProjNiels
  edAddAffineNiels edSubAffineNiels edAsProjective edAsExtended edAsProjNiels nafTable5Step
  nafTable5Points naf5Loop naf8Loop findMaxNafIdx edStrausStepA edAffineBasepointEntry
  edStrausStepB edStrausStep edStrausLoop edProjectiveToExtended edDoubleScalarMulBasepoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp edOnCurve_edZero edOnCurve_edBasepoint edOnCurve_edNeg edOnCurve_edAdd edAdd_comm
  edAdd_edZero edZero_edAdd edNeg_edAdd_self edAdd_assoc EdExtValid edExtToAffine_fp_x
  edExtToAffine_fp_y edExtToAffine_edExtZero edExtValid_edExtZero edExtToAffine_edExtOfAffine
  edExtValid_edExtOfAffine edExtAdd_toAffine edExtValid_edExtAdd edNatSmul edOnCurve_edNatSmul
  edNatSmul_one edNatSmul_add edNatSmul_two edNatSmul_mul edSmul_eq_edNatSmul
  edOrderL_lt_two_pow_256)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  edOnCurve_of_decodeEdDalek)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbNafMath (
  naf5EntryOk naf8EntryOk nafHorner naf5Loop_spec naf8Loop_spec findMaxNafIdx_le_self
  nafHorner_findMaxNafIdx)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 (
  nielsFromBytes checkTable8 getD_nielsFromBytes fe51ValAt_slice_eq edExtNeg_toAffine
  edExtValid_edExtNeg EdProjValid edProjValid_of_edExtValid edCompToAffine EdCompValid
  edAsExtended_toAffine edExtValid_edAsExtended edAsProjective_toAffine
  edProjValid_edAsProjective edProjSqToExt_spec edProjDouble_toAffine edCompValid_edProjDouble
  EdAffineNielsValid edAddAffineNiels_toAffine edCompValid_edAddAffineNiels
  edSubAffineNiels_toAffine edCompValid_edSubAffineNiels EdProjNielsValid
  edAddProjNiels_toAffine edCompValid_edAddProjNiels edSubProjNiels_toAffine
  edCompValid_edSubProjNiels)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul2 (
  edIntSmul edOnCurve_edIntSmul edIntSmul_zero edIntSmul_ofNat edNatSmul_edNeg edIntSmul_neg
  edIntSmul_add of_checkTable8)
attribute [local irreducible] fpInv fpPow recoverXEven

/-! ## 1. `.rodata` `oddMultiplesBasepointBytes` Soundness (`[2*j + 1] B` for `0 ≤ j < 64`) -/

theorem nielsFromBytes_oddMultiplesBasepoint_length :
    (nielsFromBytes oddMultiplesBasepointBytes 64).length = 64 := by decide +kernel

theorem checkTable64_oddMultiplesBasepoint :
    checkTable8 (nielsFromBytes oddMultiplesBasepointBytes 64)
      (edExtAdd (edExtOfAffine edBasepoint) (edExtOfAffine edBasepoint))
      (edExtNeg (edExtOfAffine edBasepoint)) 64 = true := by decide +kernel

theorem edAffineBasepointEntry_valid {j : Nat} (hj : j < 64) :
    let e := edAffineBasepointEntry j
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (2 * j + 1) edBasepoint) := by
  have hB1 : EdExtValid (edExtOfAffine edBasepoint) :=
    edExtValid_edExtOfAffine edOnCurve_edBasepoint
  have hB1_aff : edExtToAffine (edExtOfAffine edBasepoint) = edBasepoint :=
    edExtToAffine_edExtOfAffine edOnCurve_edBasepoint
  have hB2 : EdExtValid (edExtAdd (edExtOfAffine edBasepoint) (edExtOfAffine edBasepoint)) :=
    edExtValid_edExtAdd hB1 hB1
  have hnegB1 : EdExtValid (edExtNeg (edExtOfAffine edBasepoint)) :=
    edExtValid_edExtNeg hB1
  have hchk := of_checkTable8 hB2 hnegB1 checkTable64_oddMultiplesBasepoint
    nielsFromBytes_oddMultiplesBasepoint_length hj
  dsimp only at hchk
  rw [getD_nielsFromBytes nielsFromBytes_oddMultiplesBasepoint_length hj] at hchk
  have hpt :
      edAdd (edExtToAffine (edExtNeg (edExtOfAffine edBasepoint)))
        (edNatSmul (j + 1)
          (edExtToAffine (edExtAdd (edExtOfAffine edBasepoint) (edExtOfAffine edBasepoint)))) =
      edNatSmul (2 * j + 1) edBasepoint := by
    rw [edExtNeg_toAffine hB1, edExtAdd_toAffine hB1 hB1, hB1_aff,
        ← edNatSmul_two edOnCurve_edBasepoint,
        ← edNatSmul_mul (j + 1) 2 edOnCurve_edBasepoint,
        show (j + 1) * 2 = 1 + (2 * j + 1) by omega,
        edNatSmul_add 1 (2 * j + 1) edOnCurve_edBasepoint,
        edNatSmul_one edOnCurve_edBasepoint,
        ← edAdd_assoc (edOnCurve_edNeg edOnCurve_edBasepoint) edOnCurve_edBasepoint
          (edOnCurve_edNatSmul (2 * j + 1) edOnCurve_edBasepoint),
        edNeg_edAdd_self edOnCurve_edBasepoint,
        edZero_edAdd (edOnCurve_edNatSmul (2 * j + 1) edOnCurve_edBasepoint)]
  rw [hpt] at hchk
  have hentry :
      edAffineBasepointEntry j =
      (fe51ValAt oddMultiplesBasepointBytes (120 * j) % p25519,
       fe51ValAt oddMultiplesBasepointBytes (120 * j + 40) % p25519,
       fe51ValAt oddMultiplesBasepointBytes (120 * j + 80) % p25519) := by
    unfold edAffineBasepointEntry
    dsimp only
    generalize oddMultiplesBasepointBytes = bs
    rw [fe51ValAt_slice_eq bs _ _ _ (by omega),
        fe51ValAt_slice_eq bs _ _ _ (by omega),
        fe51ValAt_slice_eq bs _ _ _ (by omega),
        Nat.add_zero]
  dsimp only
  rwa [hentry]

/-! ## 2. Dynamic `NafLookupTable5::from` Soundness (`[2*j + 1] Q`) -/

theorem edProjNielsValid_edAsProjNiels {P : EdExtPoint} (hP : EdExtValid P) :
    EdProjNielsValid (edAsProjNiels P) (edExtToAffine P) where
  on_curve := hP.on_curve
  z_ne_zero := by
    unfold edAsProjNiels
    rw [Fp.ofNat_mod]
    exact hP.z_ne_zero
  ypx_eq := by
    have hZ := hP.z_ne_zero
    unfold edAsProjNiels
    rw [Fp.ofNat_fpAdd, Fp.ofNat_mod, edExtToAffine_fp_x, edExtToAffine_fp_y]
    grind
  ymx_eq := by
    have hZ := hP.z_ne_zero
    unfold edAsProjNiels
    rw [Fp.ofNat_fpSub, Fp.ofNat_mod, edExtToAffine_fp_x, edExtToAffine_fp_y]
    grind
  t2d_eq := by
    have hZ := hP.z_ne_zero
    have hTZ := hP.tz_eq_xy
    unfold edAsProjNiels
    rw [Fp.ofNat_fpMul, Fp.ofNat_edD2, Fp.ofNat_mod, edExtToAffine_fp_x, edExtToAffine_fp_y]
    grind

attribute [local irreducible] edAdd edBasepoint edSmul encodeEd decodeEdDalek
  edExtToAffine edCompToAffine edAsProjNiels edAffineBasepointEntry
  edAddProjNiels edSubProjNiels edAddAffineNiels edSubAffineNiels
  edAsExtended edAsProjective edProjDouble

theorem nafTable5Points_valid {A : EdExtPoint} (hA : EdExtValid A) :
    ∀ j : Nat, EdProjNielsValid (nafTable5Points A j) (edNatSmul (2 * j + 1) (edExtToAffine A))
  | 0 => by
    unfold nafTable5Points
    rw [show 2 * 0 + 1 = 1 from rfl, edNatSmul_one hA.on_curve]
    exact edProjNielsValid_edAsProjNiels hA
  | j + 1 => by
    unfold nafTable5Points nafTable5Step
    let C2 := edProjDouble A.X A.Y A.Z
    have hC2 : EdCompValid C2 := edCompValid_edProjDouble (edProjValid_of_edExtValid hA)
    let A2 := edAsExtended C2
    have hA2 : EdExtValid A2 := edExtValid_edAsExtended hC2
    have hA2_aff : edExtToAffine A2 = edNatSmul 2 (edExtToAffine A) := by
      dsimp only [A2, C2]
      rw [edAsExtended_toAffine hC2, edProjDouble_toAffine (edProjValid_of_edExtValid hA),
          ← edNatSmul_two hA.on_curve]
    have ih := nafTable5Points_valid hA j
    let Cnext := edAddProjNiels A2 (nafTable5Points A j)
    have hCnext : EdCompValid Cnext := edCompValid_edAddProjNiels hA2 ih
    have hEnext : EdExtValid (edAsExtended Cnext) := edExtValid_edAsExtended hCnext
    have haff :
        edExtToAffine (edAsExtended Cnext) =
          edNatSmul (2 * (j + 1) + 1) (edExtToAffine A) := by
      rw [edAsExtended_toAffine hCnext]
      dsimp only [Cnext]
      rw [edAddProjNiels_toAffine hA2 ih, hA2_aff,
          ← edNatSmul_add 2 (2 * j + 1) hA.on_curve,
          show 2 + (2 * j + 1) = 2 * (j + 1) + 1 by omega]
    rw [← haff]
    exact edProjNielsValid_edAsProjNiels hEnext

/-! ## 3. Signed NAF Step & Straus Horner Loop Equivalence -/

private theorem naf5EntryOk_props :
    ∀ d : BitVec 8, naf5EntryOk d = true →
      ((d == 0#8) = true ∧ d.toInt = 0) ∨
      ((d == 0#8) = false ∧ d.msb = false ∧ d.toNat / 2 < 8 ∧
        d.toInt = Int.ofNat (2 * (d.toNat / 2) + 1)) ∨
      ((d == 0#8) = false ∧ d.msb = true ∧ (256 - d.toNat) / 2 < 8 ∧
        d.toInt = -Int.ofNat (2 * ((256 - d.toNat) / 2) + 1)) := by
  decide +kernel

private theorem naf8EntryOk_props :
    ∀ d : BitVec 8, naf8EntryOk d = true →
      ((d == 0#8) = true ∧ d.toInt = 0) ∨
      ((d == 0#8) = false ∧ d.msb = false ∧ d.toNat / 2 < 64 ∧
        d.toInt = Int.ofNat (2 * (d.toNat / 2) + 1)) ∨
      ((d == 0#8) = false ∧ d.msb = true ∧ (256 - d.toNat) / 2 < 64 ∧
        d.toInt = -Int.ofNat (2 * ((256 - d.toNat) / 2) + 1)) := by
  decide +kernel

theorem edStrausStepA_spec {C A : EdExtPoint} {da : BitVec 8}
    (hC : EdCompValid C) (hA : EdExtValid A) (hda : naf5EntryOk da = true) :
    EdCompValid (edStrausStepA C (nafTable5Points A) da) ∧
    edCompToAffine (edStrausStepA C (nafTable5Points A) da) =
      edAdd (edCompToAffine C) (edIntSmul da.toInt (edExtToAffine A)) := by
  unfold edStrausStepA
  rcases naf5EntryOk_props da hda with ⟨hz, hi0⟩ | ⟨hnz, hmsb, hidx, hi_pos⟩ | ⟨hnz, hmsb, hidx, hi_neg⟩
  · simp only [hz, ↓reduceIte, hi0, edIntSmul_zero, edAdd_edZero hC.on_curve]
    exact ⟨hC, trivial⟩
  · simp only [hnz, hmsb, Bool.false_eq_true, Bool.not_false, ↓reduceIte]
    have hE : EdExtValid (edAsExtended C) := edExtValid_edAsExtended hC
    have hN := nafTable5Points_valid hA (da.toNat / 2)
    refine ⟨edCompValid_edAddProjNiels hE hN, ?_⟩
    rw [edAddProjNiels_toAffine hE hN, edAsExtended_toAffine hC, hi_pos, edIntSmul_ofNat]
  · simp only [hnz, hmsb, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
    have hE : EdExtValid (edAsExtended C) := edExtValid_edAsExtended hC
    have hN := nafTable5Points_valid hA ((256 - da.toNat) / 2)
    refine ⟨edCompValid_edSubProjNiels hE hN, ?_⟩
    rw [edSubProjNiels_toAffine hE hN, edAsExtended_toAffine hC, hi_neg,
        edIntSmul_neg _ hA.on_curve, edIntSmul_ofNat]
    rfl

theorem edStrausStepB_spec {C : EdExtPoint} {db : BitVec 8}
    (hC : EdCompValid C) (hdb : naf8EntryOk db = true) :
    EdCompValid (edStrausStepB C db) ∧
    edCompToAffine (edStrausStepB C db) =
      edAdd (edCompToAffine C) (edIntSmul db.toInt edBasepoint) := by
  unfold edStrausStepB
  rcases naf8EntryOk_props db hdb with ⟨hz, hi0⟩ | ⟨hnz, hmsb, hidx, hi_pos⟩ | ⟨hnz, hmsb, hidx, hi_neg⟩
  · simp only [hz, ↓reduceIte, hi0, edIntSmul_zero, edAdd_edZero hC.on_curve]
    exact ⟨hC, trivial⟩
  · simp only [hnz, hmsb, Bool.false_eq_true, Bool.not_false, ↓reduceIte]
    have hE : EdExtValid (edAsExtended C) := edExtValid_edAsExtended hC
    have hN := edAffineBasepointEntry_valid hidx
    dsimp only at hN
    refine ⟨edCompValid_edAddAffineNiels hE hN, ?_⟩
    rw [edAddAffineNiels_toAffine hE hN, edAsExtended_toAffine hC, hi_pos, edIntSmul_ofNat]
  · simp only [hnz, hmsb, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
    have hE : EdExtValid (edAsExtended C) := edExtValid_edAsExtended hC
    have hN := edAffineBasepointEntry_valid hidx
    dsimp only at hN
    refine ⟨edCompValid_edSubAffineNiels hE hN, ?_⟩
    rw [edSubAffineNiels_toAffine hE hN, edAsExtended_toAffine hC, hi_neg,
        edIntSmul_neg _ edOnCurve_edBasepoint, edIntSmul_ofNat]
    rfl

private theorem edAdd_pair_double {X Y : EdPoint}
    (hX : edOnCurve X = true) (hY : edOnCurve Y = true) :
    edAdd (edAdd X Y) (edAdd X Y) = edAdd (edAdd X X) (edAdd Y Y) := by
  rw [← edAdd_assoc (edOnCurve_edAdd hX hY) hX hY,
      edAdd_assoc hX hY hX,
      edAdd_comm Y X,
      ← edAdd_assoc hX hX hY,
      edAdd_assoc (edOnCurve_edAdd hX hX) hY hY]

private theorem edAdd_right_swap {X Y X' : EdPoint}
    (hX : edOnCurve X = true) (hY : edOnCurve Y = true) (hX' : edOnCurve X' = true) :
    edAdd (edAdd X Y) X' = edAdd (edAdd X X') Y := by
  rw [edAdd_assoc hX hY hX', edAdd_comm Y X', ← edAdd_assoc hX hX' hY]

theorem edStrausStep_spec {P A : EdExtPoint} {acc_a acc_b : Int} {da db : BitVec 8}
    (hP : EdProjValid P) (hA : EdExtValid A)
    (hP_aff : edExtToAffine P =
      edAdd (edIntSmul acc_a (edExtToAffine A)) (edIntSmul acc_b edBasepoint))
    (hda : naf5EntryOk da = true) (hdb : naf8EntryOk db = true) :
    EdProjValid (edStrausStep P (nafTable5Points A) da db) ∧
    edExtToAffine (edStrausStep P (nafTable5Points A) da db) =
      edAdd (edIntSmul (2 * acc_a + da.toInt) (edExtToAffine A))
            (edIntSmul (2 * acc_b + db.toInt) edBasepoint) := by
  unfold edStrausStep
  have hQ : edOnCurve (edExtToAffine A) = true := hA.on_curve
  have hB : edOnCurve edBasepoint = true := edOnCurve_edBasepoint
  let C0 := edProjDouble P.X P.Y P.Z
  have hC0 : EdCompValid C0 := edCompValid_edProjDouble hP
  have hC0_aff : edCompToAffine C0 =
      edAdd (edIntSmul (2 * acc_a) (edExtToAffine A))
            (edIntSmul (2 * acc_b) edBasepoint) := by
    dsimp only [C0]
    rw [edProjDouble_toAffine hP, hP_aff,
        edAdd_pair_double (edOnCurve_edIntSmul acc_a hQ) (edOnCurve_edIntSmul acc_b hB),
        ← edIntSmul_add acc_a acc_a hQ,
        ← edIntSmul_add acc_b acc_b hB,
        show acc_a + acc_a = 2 * acc_a by omega,
        show acc_b + acc_b = 2 * acc_b by omega]
  obtain ⟨hC1, hC1_aff⟩ := edStrausStepA_spec hC0 hA hda
  obtain ⟨hC2, hC2_aff⟩ := edStrausStepB_spec hC1 hdb
  refine ⟨edProjValid_edAsProjective hC2, ?_⟩
  rw [edAsProjective_toAffine, edAsExtended_toAffine hC2, hC2_aff, hC1_aff, hC0_aff,
      edAdd_right_swap
        (edOnCurve_edIntSmul (2 * acc_a) hQ)
        (edOnCurve_edIntSmul (2 * acc_b) hB)
        (edOnCurve_edIntSmul da.toInt hQ),
      ← edIntSmul_add (2 * acc_a) da.toInt hQ,
      edAdd_assoc
        (edOnCurve_edIntSmul (2 * acc_a + da.toInt) hQ)
        (edOnCurve_edIntSmul (2 * acc_b) hB)
        (edOnCurve_edIntSmul db.toInt hB),
      ← edIntSmul_add (2 * acc_b) db.toInt hB]

theorem edStrausLoop_spec {naf_a naf_b : List (BitVec 8)} {A : EdExtPoint}
    (hA : EdExtValid A)
    (hok_a : ∀ j < 256, naf5EntryOk (naf_a.getD j 0#8) = true)
    (hok_b : ∀ j < 256, naf8EntryOk (naf_b.getD j 0#8) = true) :
    ∀ (i : Nat) (_hi : i < 256) (P : EdExtPoint) (acc_a acc_b : Int),
      EdProjValid P →
      edExtToAffine P =
        edAdd (edIntSmul acc_a (edExtToAffine A)) (edIntSmul acc_b edBasepoint) →
      EdProjValid (edStrausLoop naf_a naf_b (nafTable5Points A) i P) ∧
      edExtToAffine (edStrausLoop naf_a naf_b (nafTable5Points A) i P) =
        edAdd (edIntSmul (nafHorner naf_a i acc_a) (edExtToAffine A))
              (edIntSmul (nafHorner naf_b i acc_b) edBasepoint)
  | 0, _, P, acc_a, acc_b, hP, hP_aff => by
    unfold edStrausLoop nafHorner
    exact edStrausStep_spec hP hA hP_aff (hok_a 0 (by decide)) (hok_b 0 (by decide))
  | k + 1, hi, P, acc_a, acc_b, hP, hP_aff => by
    unfold edStrausLoop nafHorner
    obtain ⟨hP', hP'_aff⟩ := edStrausStep_spec hP hA hP_aff
      (hok_a (k + 1) hi) (hok_b (k + 1) hi)
    exact edStrausLoop_spec hA hok_a hok_b k (by omega) _ _ _ hP' hP'_aff

/-! ## 4. End-to-End `vartime_double_scalar_mul_basepoint` Compression Bridge -/

theorem edDoubleScalarMulBasepoint_spec
    (k_bs negA_bs s_bs : List (BitVec 8)) (Apt : EdPoint)
    (_hk_len : k_bs.length = 32) (hk_lt : leBytesToNat k_bs < edOrderL)
    (_hs_len : s_bs.length = 32) (hs_lt : leBytesToNat s_bs < edOrderL)
    (hApt : ∃ pk_bs : List (BitVec 8), decodeEdDalek pk_bs = some Apt)
    (_hneg_bnd : fe51Point4Bounded negA_bs (2 ^ 52))
    (hneg_eq : edExtOfBytes negA_bs = edExtNeg (edExtOfAffine Apt)) :
    EdExtValid (edDoubleScalarMulBasepoint k_bs negA_bs s_bs) ∧
    edExtToAffine (edDoubleScalarMulBasepoint k_bs negA_bs s_bs) =
      edSub (edSmul (leBytesToNat s_bs) edBasepoint) (edSmul (leBytesToNat k_bs) Apt) := by
  obtain ⟨pk_bs, hdec⟩ := hApt
  have hApt_curve : edOnCurve Apt = true := edOnCurve_of_decodeEdDalek hdec
  have hApt_ext : EdExtValid (edExtOfAffine Apt) := edExtValid_edExtOfAffine hApt_curve
  let A := edExtOfBytes negA_bs
  have hA : EdExtValid A := by
    dsimp only [A]
    rw [hneg_eq]
    exact edExtValid_edExtNeg hApt_ext
  have hA_aff : edExtToAffine A = edNeg Apt := by
    dsimp only [A]
    rw [hneg_eq, edExtNeg_toAffine hApt_ext, edExtToAffine_edExtOfAffine hApt_curve]
  obtain ⟨_, hok_a, hval_a⟩ := naf5Loop_spec hk_lt
  obtain ⟨_, hok_b, hval_b⟩ := naf8Loop_spec hs_lt
  dsimp only [edDoubleScalarMulBasepoint, edProjectiveToExtended]
  let naf_a := naf5Loop (k_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  let naf_b := naf8Loop (s_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  let max_i := findMaxNafIdx naf_a naf_b 255
  have hmax_lt : max_i < 256 := Nat.lt_succ_of_le (findMaxNafIdx_le_self naf_a naf_b 255)
  obtain ⟨hmax_a, hmax_b⟩ := nafHorner_findMaxNafIdx naf_a naf_b 255
  have hinit_valid : EdProjValid ⟨0, 1, 1, 0⟩ := (edProjValid_of_edExtValid edExtValid_edExtZero)
  have hinit_aff :
      edExtToAffine ⟨0, 1, 1, 0⟩ =
        edAdd (edIntSmul 0 (edExtToAffine A)) (edIntSmul 0 edBasepoint) := by
    rw [edIntSmul_zero, edIntSmul_zero,
        show (⟨0, 1, 1, 0⟩ : EdExtPoint) = edExtZero from rfl,
        edExtToAffine_edExtZero, edAdd_edZero edOnCurve_edZero]
  obtain ⟨hloop_valid, hloop_aff⟩ :=
    edStrausLoop_spec hA hok_a hok_b max_i hmax_lt ⟨0, 1, 1, 0⟩ 0 0 hinit_valid hinit_aff
  obtain ⟨hext_valid, hext_aff⟩ := edProjSqToExt_spec hloop_valid
  refine ⟨hext_valid, ?_⟩
  rw [hext_aff, hloop_aff, hmax_a, hmax_b, hval_a, hval_b, hA_aff]
  have hk256 : leBytesToNat k_bs < 2 ^ 256 := Nat.lt_trans hk_lt edOrderL_lt_two_pow_256
  have hs256 : leBytesToNat s_bs < 2 ^ 256 := Nat.lt_trans hs_lt edOrderL_lt_two_pow_256
  rw [← Int.ofNat_eq_natCast, ← Int.ofNat_eq_natCast,
      edIntSmul_ofNat, edIntSmul_ofNat,
      edNatSmul_edNeg,
      edAdd_comm,
      ← edSmul_eq_edNatSmul hs256 edOnCurve_edBasepoint,
      ← edSmul_eq_edNatSmul hk256 hApt_curve]
  rfl

theorem dsmb_compress_eq
    (k_bs negA_bs s_bs : List (BitVec 8)) (Apt : EdPoint)
    (hk_len : k_bs.length = 32) (hk_lt : leBytesToNat k_bs < edOrderL)
    (hs_len : s_bs.length = 32) (hs_lt : leBytesToNat s_bs < edOrderL)
    (hApt : ∃ pk_bs : List (BitVec 8), decodeEdDalek pk_bs = some Apt)
    (hneg_bnd : fe51Point4Bounded negA_bs (2 ^ 52))
    (hneg_eq : edExtOfBytes negA_bs = edExtNeg (edExtOfAffine Apt)) :
    encodeEd (edExtToAffine (edDoubleScalarMulBasepoint k_bs negA_bs s_bs)) =
      encodeEd (edSub (edSmul (leBytesToNat s_bs) edBasepoint) (edSmul (leBytesToNat k_bs) Apt)) := by
  rw [(edDoubleScalarMulBasepoint_spec k_bs negA_bs s_bs Apt
        hk_len hk_lt hs_len hs_lt hApt hneg_bnd hneg_eq).2]

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge
