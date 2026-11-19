/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Lits
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# Read-Only Literal Duplication, `Stores::open()` Packaging, and `adrp` Helpers (`main_m4`)

Read-only `.rodata` literal duplication (`m4RoLits_dup`), assembly of `storesAt ... StoresGhost.opened`
from the 40 stack words written in `main_m4`, and page-aligned `adrp` + offset identities.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## 1. Read-only literal duplication -/

@[expose] def m4RoLits (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) : SepProp :=
  ls.foldr (fun l P => ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ P) emp

@[simp] theorem m4RoLits_nil (base : BitVec 64) : m4RoLits base [] = emp := rfl

@[simp] theorem m4RoLits_cons (base : BitVec 64) (l : Nat × List (BitVec 8))
    (ls : List (Nat × List (BitVec 8))) :
    m4RoLits base (l :: ls) = ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ m4RoLits base ls := rfl

@[simp] theorem m4RoLits_dup (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) :
    (m4RoLits base ls ∗ m4RoLits base ls) = m4RoLits base ls := by
  induction ls with
  | nil => rw [m4RoLits_nil, emp_sepConj]
  | cons l ls ih =>
    rw [m4RoLits_cons, sepConj_assoc, sepConj_left_comm (m4RoLits base ls), ← sepConj_assoc,
      pointsToBytesRO_dup, ih]

private def m4LitList : List (Nat × List (BitVec 8)) :=
  (coinsLitOff.toNat, utf8 "coins") :: dirLits.map fun l => (l.1.toNat, utf8 l.2)

private theorem m4_foldr_lits_eq_roLits (base : BitVec 64) (ls : List (BitVec 64 × String)) :
    ls.foldr (fun l P => ((base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp =
      m4RoLits base (ls.map fun l => (l.1.toNat, utf8 l.2)) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldr_cons, ih, List.map_cons, m4RoLits_cons, BitVec.ofNat_toNat, BitVec.setWidth_eq]

abbrev dirLit0Off : BitVec 64 := (dirLits[0]).1
abbrev dirLit1Off : BitVec 64 := (dirLits[1]).1
abbrev dirLit2Off : BitVec 64 := (dirLits[2]).1
abbrev dirLit3Off : BitVec 64 := (dirLits[3]).1
abbrev dirLit4Off : BitVec 64 := (dirLits[4]).1
abbrev dirLit5Off : BitVec 64 := (dirLits[5]).1
abbrev dirLit6Off : BitVec 64 := (dirLits[6]).1

theorem dirAt_new_intro (A : RustAlloc) (d p : BitVec 64) (bs : List (BitVec 8)) :
    ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64) ∗
      ((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) ⊢
      dirAt A d (.new bs) := by
  unfold dirAt DirGhost.new
  have hvec :
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ⊢
        RustHeap.vecOf A 48 8 (dirEntryAt A) d [] := by
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    change ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ⊢
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 48 < 2 ^ 63 ∧
        (8#64 : BitVec 64) ≠ 0⌝ ∗ emp
    have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 48 < 2 ^ 63 ∧
        (8#64 : BitVec 64) ≠ 0) = True := eq_true ⟨by decide, by decide, by decide⟩
    rw [hpure, pure_true, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  have hstr :
      (((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) ⊢
        strRefAt (d + 0x18#64) bs := by
    unfold strRefAt
    refine Entails.sepExists_right p ?_
    have h32 : d + 0x18#64 + 8#64 = d + 32#64 := by bv_omega
    rw [h32]
    exact Entails.refl _
  have hassoc :
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64) ∗
        ((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) =
      (((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ∗
        (((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs))) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono hvec hstr

/-- The 5 stack words of an opened empty `Dir` at stack offset `fsp + base` with path `(p, len)`. -/
@[expose] def openDirWords (fsp : BitVec 64) (base : Nat) (p : BitVec 64) (len : Nat) : SepProp :=
  ((fsp + BitVec.ofNat 64 base) ↦₆₄ 0#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 8)) ↦₆₄ 8#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 16)) ↦₆₄ 0#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 24)) ↦₆₄ p) ∗
  ((fsp + BitVec.ofNat 64 (base + 32)) ↦₆₄ BitVec.ofNat 64 len)

theorem openDirWords_to_dirAt (A : RustAlloc) (fsp : BitVec 64) (base : Nat)
    (p : BitVec 64) (bs : List (BitVec 8)) {len : Nat} (hlen : bs.length = len) :
    openDirWords fsp base p len ∗ (p ↦ᵣ bs) ⊢
      dirAt A (fsp + BitVec.ofNat 64 base) (.new bs) := by
  subst hlen
  unfold openDirWords
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (dirAt_new_intro A (fsp + BitVec.ofNat 64 base) p bs)

theorem openDir0_to_dirAt (A : RustAlloc) (fsp : BitVec 64) :
    openDirWords fsp 0x310 1#64 0 ⊢ dirAt A (fsp + 0x310#64) (.new []) := by
  have h := openDirWords_to_dirAt A fsp 0x310 1#64 [] rfl
  rwa [pointsToBytesRO_nil, sepConj_emp] at h

end CryptoVerification.SignalSession.Cli.MainHops
