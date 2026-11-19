/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Constant Basis Cases (`n = 0, 1, 3`)

**Checked by Lean.**

Verifies OOM panic helpers and constant Lagrange basis construction (`0x6a7f4..0x6ad74`,
`+1136..+2608` / `+4004`) for `n ∈ {0, 1, 3}`.
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
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two exists_pow_two_eq_eight
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre

theorem pointsTo32_split16 (p : BitVec 64) (w : BitVec 32) :
    (p ↦₃₂ w) = (p ↦₁₆ w.extractLsb' 0 16) ∗ ((p + 2#64) ↦₁₆ w.extractLsb' 16 16) := by
  have hp3 : p + 3#64 = (p + 2#64) + 1#64 := by bv_arith
  have hlo : w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w.extractLsb' 0 16 := by bv_bits
  have hhi : w.extractLsb' 24 8 ++ w.extractLsb' 16 8 = w.extractLsb' 16 16 := by bv_bits
  rw [pointsTo32_split8, ← sepConj_assoc (p ↦₈ _), pointsTo8_pair, hlo, hp3, pointsTo8_pair, hhi]

theorem mem32_to_mem16_pair (p : BitVec 64) (w : BitVec 32) (c0 c1 : BitVec 16)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w) :
    (p ↦₃₂ w) ⊢ (p ↦₁₆ c0) ∗ ((p + 2#64) ↦₁₆ c1) := by
  subst hc0 hc1
  exact Entails.of_eq (pointsTo32_split16 p w)

/-- Constructing `polyAt A addr 1#64 p ⟨[GF16.ZERO]⟩` from raw stack header `(1#64, p, 1#64)` and `p ↦₁₆ 0#16`. -/
theorem polyAt_zero_one_intro (A : RustAlloc) (addr p : BitVec 64) (hp : p ≠ 0#64) :
    ((addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 1#64) ∗
     A.live p 2 2 ∗ (p ↦₁₆ 0#16)) ⊢
    polyAt A addr 1#64 p ⟨[GF16.ZERO]⟩ := by
  unfold polyAt vecAt vecHeader vecBuf gf16Stride gf16Align
  have h1ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 1 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, h1ne, ↓reduceIte,
    arrayAt, gf16At, GF16.ZERO, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

/-- Constructing `polyAt A addr 1#64 p ⟨[GF16.ONE]⟩` from raw stack header `(1#64, p, 1#64)` and `p ↦₁₆ 1#16`. -/
theorem polyAt_const_one_intro (A : RustAlloc) (addr p : BitVec 64) (hp : p ≠ 0#64) :
    ((addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 1#64) ∗
     A.live p 2 2 ∗ (p ↦₁₆ 1#16)) ⊢
    polyAt A addr 1#64 p ⟨[GF16.ONE]⟩ := by
  unfold polyAt vecAt vecHeader vecBuf gf16Stride gf16Align
  have h1ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 1 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, h1ne, ↓reduceIte,
    arrayAt, gf16At, GF16.ONE, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

/-- Constructing `polyAt A addr 3#64 p ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩]⟩` from `(3#64, p, 3#64)` and `(p ↦₃₂ w01) ∗ ((p + 4#64) ↦₁₆ c2)`. -/
theorem polyAt_deg2_intro (A : RustAlloc) (addr p : BitVec 64)
    (w01 : BitVec 32) (c0 c1 c2 : BitVec 16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w01)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w01) :
    ((addr ↦₆₄ 3#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 3#64) ∗
     A.live p 6 2 ∗ (p ↦₃₂ w01) ∗ ((p + 4#64) ↦₁₆ c2)) ⊢
    polyAt A addr 3#64 p ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩]⟩ := by
  subst hc0 hc1
  rw [pointsTo32_split16 p w01]
  unfold polyAt vecAt vecHeader vecBuf gf16Stride gf16Align
  have h3ne : (3#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 3 ≤ (3#64 : BitVec 64).toNat ∧ (3#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, h3ne, ↓reduceIte,
    arrayAt, gf16At, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul,
    Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
    BitVec.reduceAdd]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

theorem align8_of_mod8_eq_zero {p : BitVec 64} (h : p.toNat % 8 = 0) :
    (p &&& 7#64 == 0#64) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change p.toNat &&& 7 = 0
  rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact h

theorem align8_add_of_mod8_eq_zero {p k : BitVec 64} (hp : p.toNat % 8 = 0) (hk : k.toNat % 8 = 0) :
    ((p + k) &&& 7#64 == 0#64) = true := by
  apply align8_of_mod8_eq_zero
  rw [BitVec.toNat_add]
  omega

theorem memRegion_split_polyHeader (p : BitVec 64) :
    memRegion p 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 16) (b' := p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 8) (b' := p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_split_polyHeader_off (p off0 off8 off16 : BitVec 64)
    (h8 : (p + off0) + 8#64 = p + off8)
    (h16 : (p + off0) + 16#64 = p + off16) :
    memRegion (p + off0) 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((p + off0) ↦₆₄ u0) ∗ ((p + off8) ↦₆₄ u8) ∗ ((p + off16) ↦₆₄ u16) := by
  rw [memRegion_split_polyHeader (p + off0), h8, h16]

theorem memRegion_split_basis3 (p : BitVec 64) :
    memRegion p 72 =
      memRegion p 24 ∗ memRegion (p + 24#64) 24 ∗ memRegion (p + 48#64) 24 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 24) (k := 48) (b' := p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 24) (k := 24) (b' := p + 48#64) rfl (by bv_omega) (by decide)]

theorem memRegion_split_deg2 (p : BitVec 64) :
    memRegion p 6 =
      ∃∗ u4 : BitVec 16, ∃∗ w01 : BitVec 32,
        (p ↦₃₂ w01) ∗ ((p + 4#64) ↦₁₆ u4) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 4) (k := 2) (b' := p + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four p,
      ProofLib.memRegion_two (p + 4#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_split_deg4 (p : BitVec 64) :
    memRegion p 10 =
      ∃∗ u8 : BitVec 16, ∃∗ w03 : BitVec 64,
        (p ↦₆₄ w03) ∗ ((p + 8#64) ↦₁₆ u8) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 2) (b' := p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_two (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem polyOf_deg2_intro (A : RustAlloc) (addr p : BitVec 64)
    (w01 : BitVec 32) (c0 c1 c2 : BitVec 16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w01)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w01) :
    ((addr ↦₆₄ 3#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 3#64) ∗
     A.live p 6 2 ∗ (p ↦₃₂ w01) ∗ ((p + 4#64) ↦₁₆ c2)) ⊢
    polyOf A addr ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩]⟩ := by
  refine Entails.trans (polyAt_deg2_intro A addr p w01 c0 c1 c2 hp hc0 hc1) ?_
  unfold polyOf vecOf
  exact Entails.sepExists_right 3#64 (Entails.sepExists_right p (Entails.refl _))

theorem polyOf_deg2_intro_off (A : RustAlloc) (base off0 off8 off16 p : BitVec 64)
    (w01 : BitVec 32) (c0 c1 c2 : BitVec 16)
    (h8 : (base + off0) + 8#64 = base + off8)
    (h16 : (base + off0) + 16#64 = base + off16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w01)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w01) :
    (((base + off0) ↦₆₄ 3#64) ∗ ((base + off8) ↦₆₄ p) ∗ ((base + off16) ↦₆₄ 3#64) ∗
     A.live p 6 2 ∗ (p ↦₃₂ w01) ∗ ((p + 4#64) ↦₁₆ c2)) ⊢
    polyOf A (base + off0) ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩]⟩ := by
  rw [← h8, ← h16]
  exact polyOf_deg2_intro A (base + off0) p w01 c0 c1 c2 hp hc0 hc1

/-- Heap representation of a non-empty `Vec<Poly>` buffer at `ptr` with capacity `polys.length`. -/
@[expose] def basisVecAt (A : RustAlloc) (ptr : BitVec 64) (polys : List Poly) : SepProp :=
  ⌜ptr ≠ 0#64⌝ ∗ A.live ptr (24 * polys.length) 8 ∗ polyListOf A ptr polys

end CryptoVerification.SpqrV1.Poly.NextChunk

