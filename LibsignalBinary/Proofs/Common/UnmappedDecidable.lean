/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.RustHeap.Alloc

/-!
# Bounded `Unmapped` Decidability and Fuel-Bounded Index Search

Shared constructive decidability for `CryptoVerification.RustHeap.Unmapped` (`min size (2 ^ 64)`
byte offsets) and fuel-bounded lowest-index search `findIdxFrom`, used by non-vacuity and legacy
bump-allocator witness hooks. `instDecidableUnmapped` is `scoped` so importing this module does not
install a `2 ^ 64`-scanning `Decidable` instance globally.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Common.UnmappedDecidable

open Arm64
open CryptoVerification.RustHeap (Unmapped)

theorem unmapped_iff_bounded (m : Memory) (base : BitVec 64) (size : Nat) :
    Unmapped m base size ↔
      ∀ i < min size (2 ^ 64), (m.perm (base + BitVec.ofNat 64 i)).mapped = false := by
  constructor
  · intro h i hi
    apply h
    simp only [InRegion]
    have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h a ha
    simp only [InRegion] at ha
    have hi : (a - base).toNat < min size (2 ^ 64) := by
      have := (a - base).isLt
      omega
    have ha_eq : base + BitVec.ofNat 64 (a - base).toNat = a := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
      have := a.isLt
      have := base.isLt
      omega
    have hperm := h (a - base).toNat hi
    rwa [ha_eq] at hperm

/-- Constructively decides `Unmapped m base size` by checking `min size (2 ^ 64)` byte offsets
(`scoped` so it is active only where explicitly opened). -/
scoped instance instDecidableUnmapped (m : Memory) (base : BitVec 64) (size : Nat) :
    Decidable (Unmapped m base size) :=
  decidable_of_iff (∀ i < min size (2 ^ 64), (m.perm (base + BitVec.ofNat 64 i)).mapped = false)
    (unmapped_iff_bounded m base size).symm

/-- Lowest-index search over `[i, i + fuel)` for `P k = true`. -/
@[expose] def findIdxFrom (P : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i => if P i then some i else findIdxFrom P fuel (i + 1)

theorem findIdxFrom_some_spec (P : Nat → Bool) :
    ∀ {fuel i k : Nat}, findIdxFrom P fuel i = some k → i ≤ k ∧ k < i + fuel ∧ P k = true
  | 0, _, _, h => nomatch h
  | fuel + 1, i, k, h => by
    simp only [findIdxFrom] at h
    by_cases hp : P i = true
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, by omega, hp⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hik, hkf, hpk⟩ := findIdxFrom_some_spec P h
      exact ⟨by omega, by omega, hpk⟩

theorem findIdxFrom_isSome_iff (P : Nat → Bool) :
    ∀ (fuel i : Nat),
      (findIdxFrom P fuel i).isSome = true ↔ ∃ k, i ≤ k ∧ k < i + fuel ∧ P k = true
  | 0, i => by
    simp only [findIdxFrom, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨k, hik, hki, _⟩; omega
  | fuel + 1, i => by
    simp only [findIdxFrom]
    by_cases hp : P i = true
    · simp only [hp, ↓reduceIte, Option.isSome_some, true_iff]
      exact ⟨i, Nat.le_refl i, by omega, hp⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, findIdxFrom_isSome_iff P fuel (i + 1)]
      constructor
      · rintro ⟨k, hik, hkf, hpk⟩
        exact ⟨k, by omega, by omega, hpk⟩
      · rintro ⟨k, hik, hkf, hpk⟩
        have hne : k ≠ i := fun heq => hp (heq ▸ hpk)
        exact ⟨k, by omega, by omega, hpk⟩

end LibsignalBinary.Proofs.Common.UnmappedDecidable
