/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Block A Initialization

**Checked by Lean.**

Verifies OOM panic tails and Block A (`0x6a538..0x6a754`, `+436 -> +976`), which allocates 16
initial 2-byte `Poly::zero()` buffers and scatters their headers into `[fsp + 256 .. fsp + 640)`.
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

theorem polyOf_empty_cap1_intro (A : RustAlloc) (addr p : BitVec 64) (hp : p ≠ 0#64) :
    ((addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
     (A.live p 2 2 ∗ memRegion p 2)) ⊢
    polyOf A addr ⟨[]⟩ := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  refine Entails.sepExists_right 1#64 (Entails.sepExists_right p ?_)
  have h1ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 0 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, h1ne, ↓reduceIte,
    arrayAt, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMul]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_112_split_spills (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u184 : BitVec 64, ∃∗ u192 : BitVec 64, ∃∗ u200 : BitVec 64,
      ∃∗ u208 : BitVec 64, ∃∗ u216 : BitVec 64, ∃∗ u224 : BitVec 64,
        memRegion (fsp + 112#64) 72 ∗
        ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
        ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
        ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 72) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 8) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 184#64),
      ProofLib.memRegion_eight (fsp + 192#64),
      ProofLib.memRegion_eight (fsp + 200#64),
      ProofLib.memRegion_eight (fsp + 208#64),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u224
  apply Entails.sepExists_elim; intro u216
  apply Entails.sepExists_elim; intro u208
  apply Entails.sepExists_elim; intro u200
  apply Entails.sepExists_elim; intro u192
  apply Entails.sepExists_elim; intro u184
  exact Entails.sepExists_right u184 (Entails.sepExists_right u192
    (Entails.sepExists_right u200 (Entails.sepExists_right u208
      (Entails.sepExists_right u216 (Entails.sepExists_right u224 (Entails.of_eq (by ac_rfl)))))))

theorem memRegion_112_fold_spills (fsp u184 u192 u200 u208 u216 u224 : BitVec 64) :
    memRegion (fsp + 112#64) 72 ∗
    ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
    ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
    ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ⊢
    memRegion (fsp + 112#64) 120 := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 72) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 8) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 184#64),
      ProofLib.memRegion_eight (fsp + 192#64),
      ProofLib.memRegion_eight (fsp + 200#64),
      ProofLib.memRegion_eight (fsp + 208#64),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u224
  apply Entails.sepExists_right u216
  apply Entails.sepExists_right u208
  apply Entails.sepExists_right u200
  apply Entails.sepExists_right u192
  apply Entails.sepExists_right u184
  exact Entails.of_eq (by ac_rfl)

/-- One initialized `Poly::zero()` slot (`cap = 1, ptr = p, len = 0`, with a live 2-byte allocation). -/
@[expose] def zeroPolySlotAt (A : RustAlloc) (addr : BitVec 64) : SepProp :=
  ∃∗ ptr,
    ⌜ptr ≠ 0#64⌝ ∗
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
    A.live ptr 2 2 ∗ memRegion ptr 2

/-- `n` contiguous `zeroPolySlotAt` headers starting at `base` with stride 24. -/
@[expose] def zeroPolySlotsAt (A : RustAlloc) (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => zeroPolySlotAt A base ∗ zeroPolySlotsAt A (base + 24#64) n

theorem zeroPolySlotAt_intro (A : RustAlloc) (addr ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
      (A.live ptr 2 2 ∗ memRegion ptr 2) ⊢
      zeroPolySlotAt A addr := by
  unfold zeroPolySlotAt
  refine Entails.sepExists_right ptr ?_
  exact Entails.pure_right hptr (Entails.of_eq (by ac_rfl))

theorem zeroPolySlotAt_entails_polyOf (A : RustAlloc) (addr : BitVec 64) :
    zeroPolySlotAt A addr ⊢ polyOf A addr ⟨[]⟩ := by
  unfold zeroPolySlotAt
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro hptr
  exact polyOf_empty_cap1_intro A addr ptr hptr

theorem zeroPolySlotsAt_entails_polyListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      zeroPolySlotsAt A base n ⊢ polyListOf A base (List.replicate n ⟨[]⟩)
  | 0, base => by
    simp [zeroPolySlotsAt, polyListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    simp only [zeroPolySlotsAt, List.replicate_succ, polyListOf, arrayAt, vecHeaderBytes,
      BitVec.ofNat_eq_ofNat]
    exact sepConj_mono (zeroPolySlotAt_entails_polyOf A base)
      (zeroPolySlotsAt_entails_polyListOf A n (base + 24#64))

theorem sepWP_cells_succ {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target_pc s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) post) :
    SepWP prog target_pc s (cells a (k + 1) ∗ Rest) post := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact ProofLib.SepWP.exists_left h

theorem sepWP_cells_zero {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s Rest post) :
    SepWP prog target_pc s (cells a 0 ∗ Rest) post := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

end CryptoVerification.SpqrV1.Poly.NextChunk
