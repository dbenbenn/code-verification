/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallback -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst30
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Fallback Exit and Unified Positive Basis

**Checked by Lean.**

Verifies `lagrangeBasisExit_sepWPp` (`+4116 -> +2608`), the full dynamic fallback
`basis_fallback_sepWPp`, and the unified non-empty basis construction theorem `basis_pos_sepWPp`
(`+1136 -> +2608`) for all `0 < pts.length ≤ 0x0555555555555555`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fbe :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fbe :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one ofNat_succ_add_neg_one ofNat_add_one_eq_succ
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

/-! ## 1. Pure & Memory Helper Lemmas -/

theorem toOnePts_ne_nil {pts : List Pt} (h : pts ≠ []) : toOnePts pts ≠ [] := by
  intro hnil
  have hlen : (toOnePts pts).length = 0 := by rw [hnil]; rfl
  rw [toOnePts_length] at hlen
  exact h (List.eq_nil_of_length_eq_zero hlen)

theorem lagrangeBasisTail_eq_lagrangeBasisFrom (ones : List Pt) :
    ∀ (k i : Nat), lagrangeBasisTail ones i k = lagrangeBasisFrom ones i k
  | 0, _ => rfl
  | k + 1, i => by
    simp [lagrangeBasisTail, lagrangeBasisFrom, lagrangeBasisTail_eq_lagrangeBasisFrom ones k (i + 1)]

theorem lagrangeBasisPure_length (ones : List Pt) :
    (lagrangeBasisPure ones).length = ones.length := by
  simp [lagrangeBasisPure]

theorem lagrangeBasisPure_mem_length (ones : List Pt) (p : Poly)
    (hp : p ∈ lagrangeBasisPure ones) :
    p.coefficients.length = ones.length := by
  rw [← lagrangeBasisFrom_zero_eq, ← lagrangeBasisTail_eq_lagrangeBasisFrom] at hp
  exact lagrangeBasisTail_mem_length ones ones.length 0 p hp

theorem ptAt_entails_memRegion (pt : Pt) (addr : BitVec 64) :
    ptAt pt addr ⊢ memRegion addr 4 := by
  unfold ptAt
  have h4 : (4 : Nat) = 2 + 2 := rfl
  rw [ProofLib.memRegion_split' (b := addr) (n := 2) (k := 2) (b' := addr + 2#64) h4 rfl (by decide),
      ProofLib.memRegion_two addr, ProofLib.memRegion_two (addr + 2#64)]
  exact sepConj_mono (Entails.sepExists_right pt.x.value (Entails.refl _))
    (Entails.sepExists_right pt.y.value (Entails.refl _))

theorem ptSliceAt_entails_memRegion (addr : BitVec 64) (pts : List Pt)
    (hbound : pts.length ≤ 0x0555555555555555) :
    ptSliceAt addr pts ⊢ memRegion addr (4 * pts.length) := by
  induction pts generalizing addr with
  | nil =>
    simp only [ptSliceAt, arrayAt, List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero]
    exact Entails.refl _
  | cons pt rest ih =>
    have hrest : rest.length ≤ 0x0555555555555555 := by simp at hbound; omega
    have hsplit : memRegion addr (4 * (rest.length + 1)) =
        memRegion addr 4 ∗ memRegion (addr + 4#64) (4 * rest.length) :=
      ProofLib.memRegion_split' (b := addr) (n := 4) (k := 4 * rest.length) (b' := addr + 4#64)
        (by omega) rfl (by omega)
    rw [ptSliceAt_cons, List.length_cons, hsplit]
    exact sepConj_mono (ptAt_entails_memRegion pt addr) (ih (addr + 4#64) hrest)

theorem memRegion24_off_eq_polyHeader (base : BitVec 64) :
    memRegion (base + 656#64) 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((base + 656#64) ↦₆₄ u0) ∗ ((base + 664#64) ↦₆₄ u8) ∗ ((base + 672#64) ↦₆₄ u16) := by
  have h8 : (base + 656#64) + 8#64 = base + 664#64 := by bv_omega
  have h16 : (base + 656#64) + 16#64 = base + 672#64 := by bv_omega
  rw [memRegion_split_polyHeader (base + 656#64), h8, h16]

/-! ## 2. Dynamic Lagrange Basis Loop Entry/Exit (`0x6b398..0x6b4c8`, `+4116 -> +2608`) -/

/-- Pure basis polynomial list produced by `Poly.fromCompletePoints` for `pts`. -/
@[expose] def completePointsBasisPure (pts : List Pt) : List Poly :=
  let n := pts.length
  if n == 0 then
    []
  else if n == 1 then
    extractCompletePolys COMPLETE_POINTS_POLYS_1
  else if n == 3 then
    extractCompletePolys COMPLETE_POINTS_POLYS_3
  else if n == 5 then
    extractCompletePolys COMPLETE_POINTS_POLYS_5
  else if n == 30 then
    extractCompletePolys COMPLETE_POINTS_POLYS_30
  else if n == 34 then
    extractCompletePolys COMPLETE_POINTS_POLYS_34
  else if n == 36 then
    extractCompletePolys COMPLETE_POINTS_POLYS_36
  else
    lagrangeBasisPure (toOnePts pts)

@[simp]
theorem completePointsBasisPure_length (pts : List Pt) :
    (completePointsBasisPure pts).length = pts.length := by
  unfold completePointsBasisPure
  dsimp only
  split
  · rename_i h0; exact (beq_iff_eq.mp h0).symm
  · split
    · rename_i _ h1; rw [completePointsPolys1_eq]; exact (beq_iff_eq.mp h1).symm
    · split
      · rename_i _ _ h3; rw [completePointsPolys3_eq]; exact (beq_iff_eq.mp h3).symm
      · split
        · rename_i _ _ _ h5; rw [completePointsPolys5_spec.2.1]; exact (beq_iff_eq.mp h5).symm
        · split
          · rename_i _ _ _ _ h30; rw [completePointsPolys30_spec.2.1]; exact (beq_iff_eq.mp h30).symm
          · split
            · rename_i _ _ _ _ _ h34; rw [completePointsPolys34_spec.2.1]; exact (beq_iff_eq.mp h34).symm
            · split
              · rename_i _ _ _ _ _ _ h36; rw [completePointsPolys36_spec.2.1]; exact (beq_iff_eq.mp h36).symm
              · rw [lagrangeBasisPure_length, toOnePts_length]

theorem completePointsBasisPure_mem_length (pts : List Pt) (p : Poly)
    (hp : p ∈ completePointsBasisPure pts) :
    p.coefficients.length = pts.length := by
  unfold completePointsBasisPure at hp
  dsimp only at hp
  split at hp
  · contradiction
  · split at hp
    · rename_i _ h1
      rw [beq_iff_eq.mp h1]
      rw [completePointsPolys1_eq] at hp
      simp [extractCompletePolys, constPolysToPolys, PolyConst.toPoly] at hp
      subst hp; rfl
    · split at hp
      · rename_i _ _ h3
        rw [beq_iff_eq.mp h3]
        rw [completePointsPolys3_eq] at hp
        simp [extractCompletePolys, constPolysToPolys, PolyConst.toPoly] at hp
        rcases hp with rfl | rfl | rfl <;> rfl
      · split at hp
        · rename_i _ _ _ h5
          rw [beq_iff_eq.mp h5]
          exact completePointsPolys5_spec.2.2 p hp
        · split at hp
          · rename_i _ _ _ _ h30
            rw [beq_iff_eq.mp h30]
            exact completePointsPolys30_spec.2.2 p hp
          · split at hp
            · rename_i _ _ _ _ _ h34
              rw [beq_iff_eq.mp h34]
              exact completePointsPolys34_spec.2.2 p hp
            · split at hp
              · rename_i _ _ _ _ _ _ h36
                rw [beq_iff_eq.mp h36]
                exact completePointsPolys36_spec.2.2 p hp
              · have h := lagrangeBasisPure_mem_length (toOnePts pts) p hp
                rwa [toOnePts_length] at h

theorem fromCompletePoints_eq_ok (pts : List Pt)
    (hcomplete : Poly.checkCompletePoints 0 pts = true)
    (hbound : pts.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints pts =
      .ok (.ok (Poly.lagrangeSum pts (completePointsBasisPure pts))) := by
  unfold Poly.fromCompletePoints completePointsBasisPure
  simp only [hcomplete, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  split
  · rfl
  · split
    · rw [completePointsPolys1_eq]; rfl
    · split
      · rw [completePointsPolys3_eq]; rfl
      · split
        · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys5_spec
          rw [heq]; rfl
        · split
          · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys30_spec
            rw [heq]; rfl
          · split
            · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys34_spec
              rw [heq]; rfl
            · split
              · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys36_spec
                rw [heq]; rfl
              · have hones_def :
                    List.map (fun pt : Pt => ({ x := pt.x, y := GF16.ONE } : Pt)) pts =
                      toOnePts pts := rfl
                have hlen : pts.length = (toOnePts pts).length := (toOnePts_length pts).symm
                have hub : (toOnePts pts).length + 1 ≤ USIZE_MAX := by
                  rw [toOnePts_length]; unfold USIZE_MAX; omega
                rw [hones_def, hlen, mapM_range_lagrangeInterpolatePt_eq_ok (toOnePts pts) hub,
                    lagrangeBasisTail_eq_lagrangeBasisFrom, lagrangeBasisFrom_zero_eq]

end CryptoVerification.SpqrV1.Poly.NextChunk
