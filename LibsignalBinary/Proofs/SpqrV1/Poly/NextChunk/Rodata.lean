/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import ProofLib.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows30
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows34
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows36
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRowsCommon
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `.rodata` Lagrange Basis Tables

**Checked by Lean.**

Read-only `.rodata` separation-logic assertions (`completePointsPolysAt b`) and byte-layout
helpers for the precomputed Lagrange basis tables `COMPLETE_POINTS_POLYS_{5,30,34,36}`, together
with `PolyEncoder.PtsBounded`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

/-- Capacity bound checked inside `Vec::<Poly>::with_capacity(pts.len())`
    in the fallback branch of `Poly::from_complete_points`. -/
@[expose] def _root_.CryptoVerification.LibsignalSpqrV1.PolyEncoder.PtsBounded (enc : PolyEncoder) : Prop :=
  match enc.s with
  | .points pts => ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555
  | .polys _ => True

/-- Offset of `COMPLETE_POINTS_POLYS_5` (50 bytes = 5 × 5 × `u16`). -/
abbrev completePointsPolys5Off : Nat := 602410

/-- Offset of `COMPLETE_POINTS_POLYS_30` (1,800 bytes = 30 × 30 × `u16`). -/
abbrev completePointsPolys30Off : Nat := 602460

/-- Offset of `COMPLETE_POINTS_POLYS_34` (2,312 bytes = 34 × 34 × `u16`). -/
abbrev completePointsPolys34Off : Nat := 604260

/-- Offset of `COMPLETE_POINTS_POLYS_36` (2,592 bytes = 36 × 36 × `u16`). -/
abbrev completePointsPolys36Off : Nat := 606572

/-- Convert a `GF16` list into little-endian bytes (`2 * cs.length` bytes). -/
@[expose] def gf16SliceBytes (cs : List GF16) : List (BitVec 8) :=
  cs.flatMap (fun g => [g.value.extractLsb' 0 8, g.value.extractLsb' 8 8])

@[simp]
theorem gf16SliceBytes_nil : gf16SliceBytes [] = [] := rfl

@[simp]
theorem gf16SliceBytes_cons (g : GF16) (cs : List GF16) :
    gf16SliceBytes (g :: cs) =
      g.value.extractLsb' 0 8 :: g.value.extractLsb' 8 8 :: gf16SliceBytes cs := rfl

@[simp]
theorem gf16SliceBytes_length (cs : List GF16) :
    (gf16SliceBytes cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons _ cs ih =>
    simp only [gf16SliceBytes_cons, List.length_cons, ih]
    omega

/-- Flatten a list of `Poly`s into little-endian bytes (`u16` per `GF16` coefficient). -/
@[expose] def polysToBytes (polys : List Poly) : List (BitVec 8) :=
  polys.flatMap (fun p => gf16SliceBytes p.coefficients)

@[simp]
theorem polysToBytes_nil : polysToBytes [] = [] := rfl

@[simp]
theorem polysToBytes_cons (p : Poly) (ps : List Poly) :
    polysToBytes (p :: ps) = gf16SliceBytes p.coefficients ++ polysToBytes ps := rfl

/-- Extract `List Poly` from `Except PolyPanic (List (PolyConst n))`. -/
@[expose] def extractCompletePolys {n : Nat} (r : Except PolyPanic (List (PolyConst n))) : List Poly :=
  match r with
  | .ok cps => constPolysToPolys cps
  | .error _ => []

/-- Combined boolean check for a precomputed `COMPLETE_POINTS_POLYS_N` table
    so kernel reduction evaluates `r` only once. -/
def checkCompletePolys (n _off : Nat) (r : Except PolyPanic (List (PolyConst n))) : Bool :=
  match r with
  | .error _ => false
  | .ok cps =>
    let polys := constPolysToPolys cps
    let bs := polysToBytes polys
    decide (polys.length = n) &&
    polys.all (fun p => decide (p.coefficients.length = n)) &&
    decide (bs.length = 2 * n * n)

theorem checkCompletePolys_spec {n off : Nat} {r : Except PolyPanic (List (PolyConst n))}
    (h : checkCompletePolys n off r = true) :
    (∃ cps, r = .ok cps ∧ constPolysToPolys cps = extractCompletePolys r) ∧
    (extractCompletePolys r).length = n ∧
    (∀ p ∈ extractCompletePolys r, p.coefficients.length = n) ∧
    (polysToBytes (extractCompletePolys r)).length = 2 * n * n ∧
    True := by
  unfold checkCompletePolys extractCompletePolys at *
  cases r with
  | error e => contradiction
  | ok cps =>
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨⟨cps, rfl, rfl⟩, h.1.1, h.1.2, h.2, trivial⟩

private def checkCompletePolysFast (n _off : Nat)
    (r : Except PolyPanic (List (PolyConst n))) : Bool :=
  match r with
  | .error _ => false
  | .ok cps =>
    let polys := constPolysToPolys cps
    let bs := polysToBytes polys
    Nat.beq polys.length n &&
    polys.all (fun p => Nat.beq p.coefficients.length n) &&
    Nat.beq bs.length (2 * n * n)

private theorem checkCompletePolys_of_fast {n off : Nat}
    {r : Except PolyPanic (List (PolyConst n))}
    (h : checkCompletePolysFast n off r = true) :
    checkCompletePolys n off r = true := by
  unfold checkCompletePolysFast checkCompletePolys at *
  cases r with
  | error _ => nomatch h
  | ok cps =>
    dsimp only at h ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    refine ⟨⟨decide_eq_true (Nat.eq_of_beq_eq_true h.1.1), ?_⟩,
      decide_eq_true (Nat.eq_of_beq_eq_true h.2)⟩
    intro p hp
    exact decide_eq_true (Nat.eq_of_beq_eq_true (h.1.2 p hp))

/-- Exact value of `COMPLETE_POINTS_POLYS_1`. -/
theorem completePointsPolys1_eq :
    COMPLETE_POINTS_POLYS_1 = .ok [{ coefficients := [⟨1#16⟩] }] :=
  completePointsPolys_eq_of_fast 1 [{ coefficients := [⟨1#16⟩] }] (by rfl_kernel)

/-- Exact value of `COMPLETE_POINTS_POLYS_3`. -/
theorem completePointsPolys3_eq :
    COMPLETE_POINTS_POLYS_3 = .ok
      [ { coefficients := [⟨0x0001#16⟩, ⟨0x8804#16⟩, ⟨0x8805#16⟩] }
      , { coefficients := [⟨0x0000#16⟩, ⟨0xf007#16⟩, ⟨0xf006#16⟩] }
      , { coefficients := [⟨0x0000#16⟩, ⟨0x7803#16⟩, ⟨0x7803#16⟩] } ] :=
  completePointsPolys_eq_of_fast 3
    [ { coefficients := [⟨0x0001#16⟩, ⟨0x8804#16⟩, ⟨0x8805#16⟩] }
    , { coefficients := [⟨0x0000#16⟩, ⟨0xf007#16⟩, ⟨0xf006#16⟩] }
    , { coefficients := [⟨0x0000#16⟩, ⟨0x7803#16⟩, ⟨0x7803#16⟩] } ] (by rfl_kernel)

/-- The 50 little-endian bytes of `COMPLETE_POINTS_POLYS_5`. -/
@[expose] def completePointsPolys5Bytes : List (BitVec 8) :=
  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_5)

set_option maxRecDepth 200000

theorem checkCompletePolys5 :
    checkCompletePolys 5 completePointsPolys5Off COMPLETE_POINTS_POLYS_5 = true := by
  unfold COMPLETE_POINTS_POLYS_5
  rw [GF16Fast.lagrangePolysForCompletePoints_eq_fast]
  exact checkCompletePolys_of_fast (by rfl_kernel)

theorem completePointsPolys5Bytes_length : completePointsPolys5Bytes.length = 50 :=
  (checkCompletePolys_spec checkCompletePolys5).2.2.2.1

@[expose] def completePointsPolys5At (b : BitVec 64) : SepProp :=
  (b + bv% completePointsPolys5Off) ↦ᵣ completePointsPolys5Bytes

/-- The 1,800 little-endian bytes of `COMPLETE_POINTS_POLYS_30`. -/
@[expose] def completePointsPolys30Bytes : List (BitVec 8) :=
  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_30)

theorem checkCompletePolys30 :
    checkCompletePolys 30 completePointsPolys30Off COMPLETE_POINTS_POLYS_30 = true := by
  rw [completePointsPolys30_eq]
  exact checkCompletePolys_of_fast (by rfl_kernel)

theorem completePointsPolys30Bytes_length : completePointsPolys30Bytes.length = 1800 :=
  (checkCompletePolys_spec checkCompletePolys30).2.2.2.1

@[expose] def completePointsPolys30At (b : BitVec 64) : SepProp :=
  (b + bv% completePointsPolys30Off) ↦ᵣ completePointsPolys30Bytes

/-- The 2,312 little-endian bytes of `COMPLETE_POINTS_POLYS_34`. -/
@[expose] def completePointsPolys34Bytes : List (BitVec 8) :=
  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_34)

theorem checkCompletePolys34 :
    checkCompletePolys 34 completePointsPolys34Off COMPLETE_POINTS_POLYS_34 = true := by
  rw [completePointsPolys34_eq]
  exact checkCompletePolys_of_fast (by rfl_kernel)

theorem completePointsPolys34Bytes_length : completePointsPolys34Bytes.length = 2312 :=
  (checkCompletePolys_spec checkCompletePolys34).2.2.2.1

@[expose] def completePointsPolys34At (b : BitVec 64) : SepProp :=
  (b + bv% completePointsPolys34Off) ↦ᵣ completePointsPolys34Bytes

/-- The 2,592 little-endian bytes of `COMPLETE_POINTS_POLYS_36`. -/
@[expose] def completePointsPolys36Bytes : List (BitVec 8) :=
  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_36)

theorem checkCompletePolys36 :
    checkCompletePolys 36 completePointsPolys36Off COMPLETE_POINTS_POLYS_36 = true := by
  rw [completePointsPolys36_eq]
  exact checkCompletePolys_of_fast (by rfl_kernel)

theorem completePointsPolys36Bytes_length : completePointsPolys36Bytes.length = 2592 :=
  (checkCompletePolys_spec checkCompletePolys36).2.2.2.1

@[expose] def completePointsPolys36At (b : BitVec 64) : SepProp :=
  (b + bv% completePointsPolys36Off) ↦ᵣ completePointsPolys36Bytes

/-- Bundled read-only separation-logic assertion for `COMPLETE_POINTS_POLYS_{5,30,34,36}` in `.rodata`. -/
@[expose] def completePointsPolysAt (b : BitVec 64) : SepProp :=
  completePointsPolys5At b ∗
  completePointsPolys30At b ∗
  completePointsPolys34At b ∗
  completePointsPolys36At b

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (completePointsPolysAt)
end CryptoVerification.SpqrV1.Poly
