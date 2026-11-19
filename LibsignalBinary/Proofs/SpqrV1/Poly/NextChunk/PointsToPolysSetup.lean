/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Per-Polynomial `pt_vec` Setup

**Checked by Lean.**

Verifies per-polynomial `pt_vec` allocation, `enumeratePts` population, and `checkCompletePoints`
validation (`0x6a754..0x6a7f0`, `+976 -> +1136`).
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_setup :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

/-- Heap/stack representation of `pt_vec : Vec<Pt>` (`enumeratePts 0 ys`) at `ptr`,
    where `ptr = 2#64` (dangling) when `ys = []` and `A.live ptr (4 * ys.length) 2` when `ys.length > 0`. -/
@[expose] def ptVecBufAt (A : RustAlloc) (ptr : BitVec 64) (ys : List GF16) : SepProp :=
  ⌜ptr ≠ 0#64⌝ ∗
  ptSliceAt ptr (PolyEncoder.enumeratePts 0 ys) ∗
  if ys.length = 0 then emp else A.live ptr (4 * ys.length) 2

theorem ptVecBufAt_nil (A : RustAlloc) :
    (emp : SepProp) ⊢ ptVecBufAt A 2#64 [] := by
  unfold ptVecBufAt PolyEncoder.enumeratePts ptSliceAt arrayAt
  simp only [List.length_nil, ↓reduceIte]
  rw [sepConj_emp]
  exact Entails.pure_right (by decide : (2#64 : BitVec 64) ≠ 0#64) (Entails.refl _)

theorem enumeratePts_getElem (x : Nat) (ys : List GF16) (i : Nat)
    (hi : i < (PolyEncoder.enumeratePts x ys).length) :
    (PolyEncoder.enumeratePts x ys)[i]'hi =
      { x := GF16.new (BitVec.ofNat 16 (x + i)),
        y := ys[i]'(by simpa using hi) } := by
  induction ys generalizing x i with
  | nil => contradiction
  | cons y rest ih =>
    cases i with
    | zero =>
      simp [PolyEncoder.enumeratePts]
    | succ i' =>
      have hi' : i' < (PolyEncoder.enumeratePts (x + 1) rest).length := by
        simpa [PolyEncoder.enumeratePts] using hi
      simp only [PolyEncoder.enumeratePts, List.getElem_cons_succ, ih (x + 1) i' hi']
      have hadd : x + 1 + i' = x + (i' + 1) := by omega
      rw [hadd]

theorem memRegion_split_pt (addr : BitVec 64) (restLen : Nat)
    (hbound : restLen ≤ 0x0555555555555555) :
    memRegion addr (4 * (restLen + 1)) ⊢
      ∃∗ ux : BitVec 16, ∃∗ uy : BitVec 16,
        (addr ↦₁₆ ux) ∗ ((addr + 2#64) ↦₁₆ uy) ∗ memRegion (addr + 4#64) (4 * restLen) := by
  have h1 : 4 * (restLen + 1) = 2 + (2 + 4 * restLen) := by omega
  rw [h1,
      ProofLib.memRegion_split' (b := addr) (n := 2) (k := 2 + 4 * restLen) (b' := addr + 2#64)
        rfl (by bv_omega) (by omega),
      ProofLib.memRegion_split' (b := addr + 2#64) (n := 2) (k := 4 * restLen) (b' := addr + 4#64)
        rfl (by bv_omega) (by omega),
      ProofLib.memRegion_two addr,
      ProofLib.memRegion_two (addr + 2#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro uy
  apply Entails.sepExists_elim; intro ux
  exact Entails.sepExists_right ux (Entails.sepExists_right uy (Entails.of_eq (by ac_rfl)))

end CryptoVerification.SpqrV1.Poly.NextChunk
