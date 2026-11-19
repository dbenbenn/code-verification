/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Addr
public meta import Lean

/-!
# Deterministic Key-First Bi-Abduction Engine (`ProofLib.Sep.BiAbd`)

Separation-logic entailment and frame-inference tactics (`bi_entail` and `bi_frame`) over
`Arm64.SepProp`, built on `ProofLib.Sep.Addr`:

1. **Zero-`Qq`, Zero-Typeclass `DiscrTree` Rule Registry**:
   - `register_sep_key <ident> [<idx>,*]` and `@[sep_key <idx>,*]` index spatial predicates by
     `(headName, keyArgIndices)` so spatial keys are matched *before* unifying payload metavariables.
   - `register_biabd_rule <ident> (prio)?` and `@[biabd_rule]` / `@[biabd_rule <prio>]` register
     first-order bi-abductive subsumption and carving lemmas (`H ⊢ G`, `H ⊢ G ∗ Rest`,
     `H = G ∗ Rest`) indexed in `Lean.Meta.DiscrTree`.
2. **Deterministic 5-Phase Bi-Abduction Pipeline**:
   - **Phase 1 (Single-Pass Zipper Skolemize & Delayed Telescope)**: Pulls LHS `∃∗` and `⌜φ⌝` into
     `LocalContext`, creates delayed witness metavariables for RHS `∃∗`, and defers RHS `⌜ψ⌝` into
     `Q_pure` in one linear pass without per-binder `SepTree` sorting.
   - **Phase 2 (Root-Bucketed Key-First Worklist + Symbolic Address Deferral)**: Canonicalizes
     64-bit addresses via `ProofLib.Sep.canonAddr64` (including 1-step `BitVec.ofNat 64 u.toNat` to
     `u.zeroExtend 64` normalization and $O(1)$ syntactic rejection of unequal offsets without
     `whnf` or `isDefEq`), cascades newly grounded witnesses, and defers unique root-and-head
     symbolic address equations into `Q_addr`.
   - **Phase 3 (Unified Bi-Abductive Carving & Coalescing)**: Applies `DiscrTree` carve/subsumption
     rules, dynamic runtime-offset `ByteSlice` splitting and coalescing, and multi-atom `memRegion`
     covering alongside `∃∗` witness synthesis and `?Frame` inference.
   - **Phase 4 (Single-Certificate Spine Assembly)**: Emits at most one `SepSolver.eqAC`
     (`SepTree.eq_of_sortIdx`) permutation certificate across the entire entailment.
   - **Phase 5 (Scheduled Side-Condition Discharge)**: Grounds syntactic/`ByteSlice` equations
     first, discharges `Q_addr` second, and discharges ground `Q_pure` obligations last.
-/

namespace ProofLib.Sep

open Arm64 ProofLib

public section

universe u

/-! ## Section 1: Kernel Zipper, Bi-Abduction, & `ByteSlice` Lemmas -/

/-- Begin single-pass LHS reduction on `P ⊢ Q`. -/
theorem lhs_start {P Q : SepProp} (h : (emp ∗ (P ∗ emp)) ⊢ Q) : P ⊢ Q := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Complete single-pass LHS reduction once focus and work-stack are `emp`. -/
theorem lhs_done {Acc Q : SepProp} (h : Acc ⊢ Q) : (Acc ∗ (emp ∗ emp)) ⊢ Q := by
  simpa [sepConj_emp] using h

/-- Complete single-pass LHS reduction when `Acc` is still `emp`. -/
theorem lhs_done_emp {Q : SepProp} (h : emp ⊢ Q) : (emp ∗ (emp ∗ emp)) ⊢ Q := by
  simpa [sepConj_emp] using h

/-- Push right child `B` of `A ∗ B` onto an empty LHS work-stack (`Rest = emp`). -/
theorem lhs_sep_emp {Acc A B Q : SepProp}
    (h : (Acc ∗ (A ∗ B)) ⊢ Q) : (Acc ∗ ((A ∗ B) ∗ emp)) ⊢ Q := by
  simpa [sepConj_emp] using h

/-- Push right child `B` of `A ∗ B` onto a non-empty LHS work-stack `Rest`. -/
theorem lhs_sep {Acc A B Rest Q : SepProp}
    (h : (Acc ∗ (A ∗ (B ∗ Rest))) ⊢ Q) : (Acc ∗ ((A ∗ B) ∗ Rest)) ⊢ Q := by
  simpa [sepConj_assoc] using h

/-- Pop `Rest` when LHS focus is `emp`. -/
theorem lhs_emp {Acc Rest Q : SepProp}
    (h : (Acc ∗ (Rest ∗ emp)) ⊢ Q) : (Acc ∗ (emp ∗ Rest)) ⊢ Q := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Extract LHS pure guard `⌜φ⌝` into the local context in `O(1)` proof nodes. -/
theorem lhs_pure {Acc : SepProp} {φ : Prop} {Rest Q : SepProp}
    (h : φ → ((Acc ∗ (Rest ∗ emp)) ⊢ Q)) : (Acc ∗ (⌜φ⌝ ∗ Rest)) ⊢ Q := by
  rw [← sepConj_assoc, sepConj_comm Acc ⌜φ⌝, sepConj_assoc]
  exact Entails.pure_left fun hφ => by simpa [sepConj_emp] using h hφ

/-- Split LHS conjunction `⌜φ₁ ∧ φ₂⌝` directly into two local hypotheses. -/
theorem lhs_pure_and {Acc : SepProp} {φ₁ φ₂ : Prop} {Rest Q : SepProp}
    (h : φ₁ → φ₂ → ((Acc ∗ (Rest ∗ emp)) ⊢ Q)) : (Acc ∗ (⌜φ₁ ∧ φ₂⌝ ∗ Rest)) ⊢ Q :=
  lhs_pure fun ⟨h1, h2⟩ => h h1 h2

/-- Skolemize LHS `∃∗ x, F x` into the local context in `O(1)` proof nodes. -/
theorem lhs_exists {α : Sort u} {Acc : SepProp} {F : α → SepProp} {Rest Q : SepProp}
    (h : ∀ x : α, (Acc ∗ (F x ∗ Rest)) ⊢ Q) : (Acc ∗ ((∃∗ x, F x) ∗ Rest)) ⊢ Q := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim h

/-- Rewrite LHS focus along an explicit equation `Focus = Focus'`. -/
theorem lhs_eq {Acc Focus Focus' Rest Q : SepProp} (heq : Focus = Focus')
    (h : (Acc ∗ (Focus' ∗ Rest)) ⊢ Q) : (Acc ∗ (Focus ∗ Rest)) ⊢ Q := by
  rw [heq]; exact h

/-- Shift the first clean spatial subtree `A` into an empty `Acc`. -/
theorem lhs_keep_first {A Rest Q : SepProp}
    (h : (A ∗ (Rest ∗ emp)) ⊢ Q) : (emp ∗ (A ∗ Rest)) ⊢ Q := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Shift a clean spatial subtree `A` onto `Acc`. -/
theorem lhs_keep {Acc A Rest Q : SepProp}
    (h : ((Acc ∗ A) ∗ (Rest ∗ emp)) ⊢ Q) : (Acc ∗ (A ∗ Rest)) ⊢ Q := by
  simpa [sepConj_assoc, sepConj_emp] using h

/-- Begin single-pass RHS reduction on `P ⊢ Q`. -/
theorem rhs_start {P Q : SepProp} (h : P ⊢ (emp ∗ (Q ∗ emp))) : P ⊢ Q := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Complete single-pass RHS reduction once focus and work-stack are `emp`. -/
theorem rhs_done {P Acc : SepProp} (h : P ⊢ Acc) : P ⊢ (Acc ∗ (emp ∗ emp)) := by
  simpa [sepConj_emp] using h

/-- Push right child `B` of `A ∗ B` onto an empty RHS work-stack (`Rest = emp`). -/
theorem rhs_sep_emp {P Acc A B : SepProp}
    (h : P ⊢ (Acc ∗ (A ∗ B))) : P ⊢ (Acc ∗ ((A ∗ B) ∗ emp)) := by
  simpa [sepConj_emp] using h

/-- Push right child `B` of `A ∗ B` onto a non-empty RHS work-stack `Rest`. -/
theorem rhs_sep {P Acc A B Rest : SepProp}
    (h : P ⊢ (Acc ∗ (A ∗ (B ∗ Rest)))) : P ⊢ (Acc ∗ ((A ∗ B) ∗ Rest)) := by
  simpa [sepConj_assoc] using h

/-- Pop `Rest` when RHS focus is `emp`. -/
theorem rhs_emp {P Acc Rest : SepProp}
    (h : P ⊢ (Acc ∗ (Rest ∗ emp))) : P ⊢ (Acc ∗ (emp ∗ Rest)) := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Defer RHS pure guard `⌜ψ⌝` into `Q_pure` in `O(1)` proof nodes. -/
theorem rhs_pure {P Acc : SepProp} {ψ : Prop} {Rest : SepProp}
    (hψ : ψ) (h : P ⊢ (Acc ∗ (Rest ∗ emp))) : P ⊢ (Acc ∗ (⌜ψ⌝ ∗ Rest)) := by
  rw [← sepConj_assoc, sepConj_comm Acc ⌜ψ⌝, sepConj_assoc]
  exact Entails.pure_right hψ (by simpa [sepConj_emp] using h)

/-- Instantiate RHS `∃∗ y, G y` with delayed witness `w` in `O(1)` proof nodes. -/
theorem rhs_exists {β : Sort u} {P Acc : SepProp} {G : β → SepProp} {Rest : SepProp}
    (w : β) (h : P ⊢ (Acc ∗ (G w ∗ Rest))) : P ⊢ (Acc ∗ ((∃∗ y, G y) ∗ Rest)) := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right w h

/-- Rewrite RHS focus along an explicit equation `Focus = Focus'`. -/
theorem rhs_eq {P Acc Focus Focus' Rest : SepProp} (heq : Focus = Focus')
    (h : P ⊢ (Acc ∗ (Focus' ∗ Rest))) : P ⊢ (Acc ∗ (Focus ∗ Rest)) := by
  rw [heq]; exact h

/-- Shift the first clean spatial subtree `A` into an empty RHS `Acc`. -/
theorem rhs_keep_first {P A Rest : SepProp}
    (h : P ⊢ (A ∗ (Rest ∗ emp))) : P ⊢ (emp ∗ (A ∗ Rest)) := by
  simpa [emp_sepConj, sepConj_emp] using h

/-- Shift a clean spatial subtree `A` onto RHS `Acc`. -/
theorem rhs_keep {P Acc A Rest : SepProp}
    (h : P ⊢ ((Acc ∗ A) ∗ (Rest ∗ emp))) : P ⊢ (Acc ∗ (A ∗ Rest)) := by
  simpa [sepConj_assoc, sepConj_emp] using h

/-- Parameterized bi-abductive subsumption: `a ↦₈ v ⊢ memRegion b n`. -/
theorem biabd_pointsTo8_memRegion (a b : BitVec 64) (v : BitVec 8) (n : Nat)
    (haddr : a = b) (hlen : 1 = n) :
    (a ↦₈ v) ⊢ memRegion b n := by
  subst haddr hlen; exact ProofLib.pointsTo8_entails_memRegion a v

/-- Parameterized bi-abductive subsumption: `a ↦₁₆ v ⊢ memRegion b n`. -/
theorem biabd_pointsTo16_memRegion (a b : BitVec 64) (v : BitVec 16) (n : Nat)
    (haddr : a = b) (hlen : 2 = n) :
    (a ↦₁₆ v) ⊢ memRegion b n := by
  subst haddr hlen; exact ProofLib.pointsTo16_entails_memRegion a v

/-- Parameterized bi-abductive subsumption: `a ↦₃₂ v ⊢ memRegion b n`. -/
theorem biabd_pointsTo32_memRegion (a b : BitVec 64) (v : BitVec 32) (n : Nat)
    (haddr : a = b) (hlen : 4 = n) :
    (a ↦₃₂ v) ⊢ memRegion b n := by
  subst haddr hlen; exact ProofLib.pointsTo32_entails_memRegion a v

/-- Parameterized bi-abductive subsumption: `a ↦₆₄ v ⊢ memRegion b n`. -/
theorem biabd_pointsTo64_memRegion (a b v : BitVec 64) (n : Nat)
    (haddr : a = b) (hlen : 8 = n) :
    (a ↦₆₄ v) ⊢ memRegion b n := by
  subst haddr hlen; exact ProofLib.pointsTo64_entails_memRegion a v

/-- Parameterized bi-abductive subsumption: `a ↦₁₂₈ v ⊢ memRegion b n`. -/
theorem biabd_pointsTo128_memRegion (a b : BitVec 64) (v : BitVec 128) (n : Nat)
    (haddr : a = b) (hlen : 16 = n) :
    (a ↦₁₂₈ v) ⊢ memRegion b n := by
  subst haddr hlen; exact pointsTo128_entails_memRegion a v

/-- Parameterized bi-abductive subsumption: `a ↦ₛ bs ⊢ memRegion b n`. -/
theorem biabd_pointsToBytes_memRegion (a b : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (haddr : a = b) (hlen : bs.length = n) :
    (a ↦ₛ bs) ⊢ memRegion b n := by
  subst haddr hlen; exact pointsToBytes_entails_memRegion a bs

/-- Length of `unpackL ws` is `8 * ws.length`. -/
theorem unpackL_length (ws : List (BitVec 64)) : (unpackL ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [unpackL, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [unpackL] at ih
    have h8 : (unpack64 w).length = 8 := rfl
    rw [h8, ih]
    omega

/-- Parameterized bi-abductive subsumption: `a ↦₆₄* ws ⊢ memRegion b n`. -/
theorem biabd_pointsToWords64_memRegion (a b : BitVec 64) (ws : List (BitVec 64)) (n : Nat)
    (haddr : a = b) (hlen : 8 * ws.length = n) :
    (a ↦₆₄* ws) ⊢ memRegion b n := by
  subst haddr hlen
  rw [pointsToWords64_eq_pointsToBytes]
  have h1 := pointsToBytes_entails_memRegion a (unpackL ws)
  rwa [unpackL_length] at h1

/-- Multi-atom inductive region cover: peel leading `memRegion a k` and continue at `a + k`. -/
theorem biabd_entails_memRegion_cons {P Q : SepProp} {a b : BitVec 64} {k r n : Nat}
    (hp : P ⊢ memRegion a k)
    (hb : a + BitVec.ofNat 64 k = b)
    (hn : k + r = n)
    (hle : n ≤ 2 ^ 64)
    (hq : Q ⊢ memRegion b r) :
    (P ∗ Q) ⊢ memRegion a n := by
  rw [ProofLib.SepFrameInfer.memRegion_carve_left a b n k r hb hn hle]
  exact sepConj_mono hp hq

/-- Bi-abductive 3-way slice carve at symbolic offset `off` and length `len`. -/
theorem biabd_pointsToBytes_split3 (base b' : BitVec 64) (buf : List (BitVec 8)) (off len : Nat)
    (haddr : base + BitVec.ofNat 64 off = b')
    (hle : off + len ≤ buf.length) :
    (base ↦ₛ buf) ⊢
      ((b' ↦ₛ (buf.drop off).take len) ∗
        ((base ↦ₛ buf.take off) ∗
         ((base + BitVec.ofNat 64 (off + len)) ↦ₛ buf.drop (off + len)))) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_split3 base buf off len hle)

/-- Bi-abductive 3-way slice focus (`ProofLib.ByteSlice.slice`) at symbolic offset `off` and length `len`. -/
theorem biabd_pointsToBytes_focus (base b' : BitVec 64) (buf : List (BitVec 8)) (off len : Nat)
    (haddr : base + BitVec.ofNat 64 off = b')
    (hle : off + len ≤ buf.length) :
    (base ↦ₛ buf) ⊢
      ((b' ↦ₛ ProofLib.ByteSlice.slice buf off len) ∗
        ((base ↦ₛ buf.take off) ∗
         ((base + BitVec.ofNat 64 (off + len)) ↦ₛ buf.drop (off + len)))) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_focus base buf off len hle)

/-- Bi-abductive single-byte focus (`↦₈`) out of `base ↦ₛ bs`. -/
theorem biabd_pointsToBytes_focus8 (base b' : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (haddr : base + BitVec.ofNat 64 off = b')
    (hlt : off < bs.length) :
    (base ↦ₛ bs) ⊢
      ((b' ↦₈ bs.getD off 0#8) ∗
        ((base ↦ₛ bs.take off) ∗
         ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)))) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_focus8 base bs off hlt)

/-- Bi-abductive 64-bit little-endian focus (`↦₆₄`) out of `base ↦ₛ bs`. -/
theorem biabd_pointsToBytes_focus64_le (base b' : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (haddr : base + BitVec.ofNat 64 off = b')
    (hle : off + 8 ≤ bs.length) :
    (base ↦ₛ bs) ⊢
      ((b' ↦₆₄ ProofLib.ByteSlice.readLE bs off 8) ∗
        ((base ↦ₛ bs.take off) ∗
         ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)))) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_focus64_le base bs off hle)

/-- Bi-abductive prefix carve `(base ↦ₛ bs) ⊢ (b' ↦ₛ bs.take k) ∗ ...`. -/
theorem biabd_pointsToBytes_partition_left (base b' : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (haddr : base = b')
    (hk : k ≤ bs.length) :
    (base ↦ₛ bs) ⊢ ((b' ↦ₛ bs.take k) ∗ ((base + BitVec.ofNat 64 k) ↦ₛ bs.drop k)) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_partition base bs k hk)

/-- Bi-abductive suffix carve `(base ↦ₛ bs) ⊢ ((b' ↦ₛ bs.drop k) ∗ (base ↦ₛ bs.take k))`. -/
theorem biabd_pointsToBytes_partition_right (base b' : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (haddr : base + BitVec.ofNat 64 k = b')
    (hk : k ≤ bs.length) :
    (base ↦ₛ bs) ⊢ ((b' ↦ₛ bs.drop k) ∗ (base ↦ₛ bs.take k)) := by
  subst haddr
  rw [sepConj_comm]
  exact Entails.of_eq (pointsToBytes_partition base bs k hk)

/-- Bi-abductive `memRegion` interior carve. -/
theorem biabd_memRegion_carve (a b c : BitVec 64) (n off k r : Nat)
    (hb : a + BitVec.ofNat 64 off = b) (hc : b + BitVec.ofNat 64 k = c)
    (hn : off + k + r = n) (hle : n ≤ 2 ^ 64) :
    memRegion a n ⊢ (memRegion b k ∗ (memRegion a off ∗ memRegion c r)) := by
  rw [ProofLib.SepFrameInfer.memRegion_carve a b c n off k r hb hc hn hle]
  rw [← sepConj_assoc, sepConj_comm (memRegion a off) (memRegion b k), sepConj_assoc]
  exact Entails.refl _

/-- Coalesce two contiguous `↦ₛ` slices at symbolic addresses. -/
theorem pointsToBytes_coalesce2 (a₁ a₂ : BitVec 64) (xs ys : List (BitVec 8))
    (haddr : a₁ + BitVec.ofNat 64 xs.length = a₂) :
    ((a₁ ↦ₛ xs) ∗ (a₂ ↦ₛ ys)) ⊢ (a₁ ↦ₛ (xs ++ ys)) := by
  subst haddr
  exact Entails.of_eq (pointsToBytes_append a₁ xs ys).symm

/-- View a single `↦₈` cell as a 1-byte `↦ₛ` slice for slice coalescing. -/
theorem pointsTo8_to_bytes (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ (a ↦ₛ [v]) :=
  Entails.of_eq (pointsToBytes_singleton a v).symm

/-- A 64-bit write disjoint from `[off, off + n)` preserves `ProofLib.ByteSlice.readLE _ off n`. -/
theorem readLE_write64_of_disjoint (bs : List (BitVec 8)) (off n i : Nat) (x : BitVec 64)
    (hi : i + 8 ≤ off ∨ off + n ≤ i) (hlen : i ≤ bs.length) :
    ProofLib.ByteSlice.readLE (ProofLib.ByteSlice.write64 bs i x) off n =
      ProofLib.ByteSlice.readLE bs off n := by
  apply ProofLib.ByteSlice.readLE_congr
  intro j hj
  rw [ProofLib.ByteSlice.getD_write64 bs i x _ _ hlen]
  have hne : ¬ (i ≤ off + j ∧ off + j < i + 8) := by omega
  simp only [hne, ↓reduceIte]

/-- Reading a single byte at the exact index written by `ProofLib.ByteSlice.write8`. -/
theorem getD_write8_self (bs : List (BitVec 8)) (i : Nat) (v d : BitVec 8)
    (hlen : i ≤ bs.length) :
    (ProofLib.ByteSlice.write8 bs i v).getD i d = v := by
  rw [ProofLib.ByteSlice.getD_write8 bs i v i d hlen]
  simp

/-- Reading a single byte at an index distinct from `ProofLib.ByteSlice.write8`. -/
theorem getD_write8_ne (bs : List (BitVec 8)) (i j : Nat) (v d : BitVec 8)
    (hne : j ≠ i) (hlen : i ≤ bs.length) :
    (ProofLib.ByteSlice.write8 bs i v).getD j d = bs.getD j d := by
  rw [ProofLib.ByteSlice.getD_write8 bs i v j d hlen]
  simp [hne]

/-- Reading a single byte outside the 8-byte window written by `ProofLib.ByteSlice.write64`. -/
theorem getD_write64_ne (bs : List (BitVec 8)) (i j : Nat) (v : BitVec 64) (d : BitVec 8)
    (hout : j < i ∨ i + 8 ≤ j) (hlen : i ≤ bs.length) :
    (ProofLib.ByteSlice.write64 bs i v).getD j d = bs.getD j d := by
  rw [ProofLib.ByteSlice.getD_write64 bs i v j d hlen]
  have hno : ¬ (i ≤ j ∧ j < i + 8) := by omega
  simp only [hno, ↓reduceIte]

/-- Writing byte 0 of any length-1 byte list yields `[v]`. -/
theorem write8_len_one (xs : List (BitVec 8)) (v : BitVec 8) (h : xs.length = 1) :
    ProofLib.ByteSlice.write8 xs 0 v = [v] := by
  cases xs with
  | nil => cases h
  | cons _ tl =>
    cases tl with
    | nil => rfl
    | cons _ _ => cases h

/-- Transport `m ⊨ P` along `P ⊢ Q`. -/
theorem satisfies_of_entails {m : Memory} {P Q : SepProp}
    (hm : m ⊨ P) (hent : P ⊢ Q) : m ⊨ Q :=
  Satisfies.mono hent hm

/-- Reduce `m ⊨ Q` to `P ⊢ Q ∗ Frame` given `hm : m ⊨ P`. -/
theorem satisfies_of_bi_frame {m : Memory} {P Q Frame : SepProp}
    (hm : m ⊨ P) (hent : P ⊢ (Q ∗ Frame)) : m ⊨ Q :=
  Satisfies.of_sep_left (Satisfies.mono hent hm)

end

/-! ## Section 2: Zero-`Qq`, Zero-Typeclass `DiscrTree` Rule Registry -/

public meta section

open Lean Meta Elab Command Tactic

/-- Classification of a spatial atom head by the indices into `Expr.getAppArgs` that form its
    spatial key (matched *before* unifying payload metavariables). -/
structure SepKeySpec where
  headName      : Name
  keyArgIndices : Array Nat
  addrArgIdx    : Option Nat := keyArgIndices[0]?
  deriving Repr, Inhabited

/-- Kind of first-order bi-abduction rule stored in the `DiscrTree` registry. -/
inductive BiAbdRuleKind where
  | entailsSub
  | entailsCarve
  | eqSplit
  deriving Repr, Inhabited, BEq

/-- A registered first-order `BiAbd` rule (`H ⊢ G`, `H ⊢ G ∗ Rest`, or `H = G ∗ Rest`), indexed in
    `Lean.Meta.DiscrTree` by `Entails H G` with zero `Qq` and zero typeclasses. -/
structure BiAbdRule where
  thmName : Name
  prio    : Nat
  kind    : BiAbdRuleKind
  keys    : Array DiscrTree.Key
  deriving Inhabited

instance : BEq BiAbdRule where
  beq a b := a.thmName == b.thmName && a.prio == b.prio && a.kind == b.kind

/-- Active registry assembled from built-in specifications plus module/environment registrations. -/
structure BiAbdRegistry where
  keySpecs : Std.HashMap Name SepKeySpec
  rules    : DiscrTree BiAbdRule
  deriving Inhabited

/-- Internal environment marker prefix for `SepKeySpec` constants. -/
def sepKeyMarker : Name := `_SepBiAbdRegistry.sepKey

/-- Internal environment marker prefix for `BiAbdRule` constants. -/
def biAbdMarker  : Name := `_SepBiAbdRegistry.biAbdRule

/-- Encode `(headName, keyArgIndices)` as a zero-cost `Unit` constant in `Environment` so
    registrations can be declared and queried both within the same `.lean` module and across
    downstream `module` imports. -/
def registerSepKey (headName : Name) (keyArgIndices : Array Nat) : CoreM Unit := do
  let env ← getEnv
  unless env.contains headName do
    throwError "registerSepKey: unknown constant '{headName}'"
  let isPriv := Lean.isPrivateName headName
  let idxPart := keyArgIndices.foldl Name.mkNum sepKeyMarker
  let rawDeclName := (idxPart.str "_TARGET_") ++ headName
  let declName := if isPriv then Lean.mkPrivateName env rawDeclName else rawDeclName
  unless env.contains declName do
    Lean.withExporting (isExporting := !isPriv) do
      addDecl <| .defnDecl {
        name        := declName
        levelParams := []
        type        := mkConst ``Unit
        value       := mkConst ``Unit.unit
        hints       := .abbrev
        safety      := .safe
      }

/-- Decode a `SepKeySpec` constant name if `cName` was created by `registerSepKey`. -/
def decodeSepKeyName? (cName : Name) : Option (Name × Array Nat) :=
  let comps := (Lean.privateToUserName cName).components
  if comps.take 2 != [Name.mkSimple "_SepBiAbdRegistry", Name.mkSimple "sepKey"] then none
  else
    let rest := comps.drop 2
    match rest.findIdx? (· == Name.mkSimple "_TARGET_") with
    | none => none
    | some splitIdx =>
      let idxComps := rest.take splitIdx
      let headComps := rest.drop (splitIdx + 1)
      if headComps.isEmpty then none
      else
        let idxs? := idxComps.foldl (init := some #[]) fun acc? c =>
          match acc?, c with
          | some arr, .num _ k => some (arr.push k)
          | _, _ => none
        match idxs? with
        | none => none
        | some idxs =>
          let headName := headComps.foldl Name.append .anonymous
          some (headName, idxs)

/-- Check whether `ty` is `BitVec 64` (reducing only type-level abbreviations). -/
def isBV64Type (ty0 : Expr) : MetaM Bool := do
  let ty := ty0.consumeMData
  if ty.isAppOfArity ``BitVec 1 then
    if let some 64 ← evalClosedNat? (ty.getArg! 0) then
      return true
  let tyW ← withReducible (whnf ty)
  if tyW.isAppOfArity ``BitVec 1 then
    if let some 64 ← evalClosedNat? (tyW.getArg! 0) then
      return true
  return false

/-- Check whether expression `e` has type `BitVec 64`. -/
def isBV64Expr (e : Expr) : MetaM Bool := do
  isBV64Type (← inferType e)

/-- Find the first key argument index in `keyIdxs` whose parameter type in `headName` is `BitVec 64`. -/
def inferAddrKeyIdx (headName : Name) (keyIdxs : Array Nat) : MetaM (Option Nat) := do
  if keyIdxs.isEmpty then return none
  let some ci := (← getEnv).find? headName | return keyIdxs[0]?
  let (mvars, _, _) ← forallMetaTelescope ci.type
  for k in keyIdxs do
    if k < mvars.size then
      let kTy ← inferType mvars[k]!
      if ← isBV64Type kTy then
        return some k
  return none

/-- Extract `(width, val)` from a syntactic `BitVec` literal (`BitVec.ofNat w n` or `OfNat.ofNat`). -/
def bvLitPure? (e : Expr) : Option (Nat × Nat) :=
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then
    match (e.getArg! 0).rawNatLit?, (e.getArg! 1).rawNatLit? with
    | some w, some v => some (w, v % (2 ^ w))
    | _, _ => none
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := (e.getArg! 0).consumeMData
    if ty.isAppOfArity ``BitVec 1 then
      let w? := (ty.getArg! 0).rawNatLit?.orElse fun _ =>
        if (ty.getArg! 0).isAppOfArity ``OfNat.ofNat 3 then ((ty.getArg! 0).getArg! 1).rawNatLit? else none
      let v? := (e.getArg! 1).rawNatLit?.orElse fun _ =>
        if (e.getArg! 1).isAppOfArity ``OfNat.ofNat 3 then ((e.getArg! 1).getArg! 1).rawNatLit? else none
      match w?, v? with
      | some w, some v => some (w, v % (2 ^ w))
      | _, _ => none
    else none
  else none

/-- Canonicalize bit-vector numerals so `DiscrTree.mkPath` keys agree regardless of surface form. -/
def canonBvLits (e : Expr) : Expr :=
  e.replace fun t =>
    match bvLitPure? t with
    | some (w, v) => some (mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit w) (mkRawNatLit v))
    | none => none

/-- Inspect the conclusion of `thmName` to classify it as `.entailsSub`, `.entailsCarve`, or
    `.eqSplit` and compute its `DiscrTree` key path over `Entails lhs primaryGoal`. -/
def parseBiAbdRule (thmName : Name) (prio : Nat := 1000) : MetaM BiAbdRule := do
  let ci ← getConstInfo thmName
  let (_, _, concl0) ← forallMetaTelescope ci.type
  let concl := (← instantiateMVars concl0).consumeMData
  let (kind, lhs, goal) ←
    if concl.isAppOfArity ``Arm64.SepProp.Entails 2 then
      let l := concl.getArg! 0
      let r := (concl.getArg! 1).consumeMData
      if r.isAppOfArity ``Arm64.SepProp.sepConj 2 then
        pure (BiAbdRuleKind.entailsCarve, l, r.getArg! 0)
      else
        pure (BiAbdRuleKind.entailsSub, l, r)
    else if concl.isAppOfArity ``Eq 3 && (concl.getArg! 0).isConstOf ``Arm64.SepProp then
      let l := concl.getArg! 1
      let r := (concl.getArg! 2).consumeMData
      if r.isAppOfArity ``Arm64.SepProp.sepConj 2 then
        pure (BiAbdRuleKind.eqSplit, l, r.getArg! 0)
      else
        pure (BiAbdRuleKind.entailsSub, l, r)
    else
      throwError "registerBiAbdRule: conclusion of '{thmName}' must be `H ⊢ G`, `H ⊢ G ∗ Rest`, or `H = G ∗ Rest`, got:{indentExpr concl}"
  let keyExpr := mkApp2 (mkConst ``Arm64.SepProp.Entails) (canonBvLits lhs) (canonBvLits goal)
  let keys ← DiscrTree.mkPath keyExpr
  return { thmName, prio, kind, keys }

/-- Validate and register a first-order `BiAbd` theorem in the `Environment`. -/
def registerBiAbdRule (thmName : Name) (prio : Nat := 1000) : MetaM Unit := do
  let _ ← parseBiAbdRule thmName prio
  let env ← getEnv
  let isPriv := Lean.isPrivateName thmName
  let rawDeclName := ((biAbdMarker.num prio).str "_TARGET_") ++ thmName
  let declName := if isPriv then Lean.mkPrivateName env rawDeclName else rawDeclName
  unless env.contains declName do
    Lean.withExporting (isExporting := !isPriv) do
      addDecl <| .defnDecl {
        name        := declName
        levelParams := []
        type        := mkConst ``Unit
        value       := mkConst ``Unit.unit
        hints       := .abbrev
        safety      := .safe
      }

/-- Decode a `(thmName, prio)` entry if `cName` was created by `registerBiAbdRule`. -/
def decodeBiAbdRuleName? (cName : Name) : Option (Name × Nat) :=
  let comps := (Lean.privateToUserName cName).components
  if comps.take 2 != [Name.mkSimple "_SepBiAbdRegistry", Name.mkSimple "biAbdRule"] then none
  else
    let rest := comps.drop 2
    match rest with
    | (.num _ p) :: tgt :: thmComps =>
      if tgt == Name.mkSimple "_TARGET_" && !thmComps.isEmpty then
        some (thmComps.foldl Name.append .anonymous, p)
      else none
    | _ => none

/-- Extract the declared identifier from a named declaration command (`def`, `abbrev`, `theorem`). -/
partial def findDeclId? (stx : Syntax) : Option Ident :=
  if stx.getKind == ``Lean.Parser.Command.declId then
    some ⟨stx[0]⟩
  else
    stx.getArgs.findSome? findDeclId?

/-- Command syntax `register_sep_key <ident> [<idx>,*]` for registering spatial atom keys. -/
elab "register_sep_key " id:ident "[" idxs:num,* "]" : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let arr := idxs.getElems.map (·.getNat)
  liftCoreM <| _root_.ProofLib.Sep.registerSepKey name arr

/-- Attribute-style wrapper `@[sep_key <idx>,*] def/abbrev ...` for registering spatial atom keys. -/
elab (priority := high) "@[sep_key" idxs:num,* "]" cmd:command : command => do
  elabCommand cmd
  let some rawId := _root_.ProofLib.Sep.findDeclId? cmd.raw
    | throwError "@[sep_key]: expected a named declaration"
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload rawId
  let arr := idxs.getElems.map (·.getNat)
  liftCoreM <| _root_.ProofLib.Sep.registerSepKey fullName arr

/-- Zero-argument attribute-style wrapper `@[sep_key] def/abbrev ...` for nullary spatial tokens. -/
elab (priority := high) "@[sep_key]" cmd:command : command => do
  elabCommand cmd
  let some rawId := _root_.ProofLib.Sep.findDeclId? cmd.raw
    | throwError "@[sep_key]: expected a named declaration"
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload rawId
  liftCoreM <| _root_.ProofLib.Sep.registerSepKey fullName #[]

/-- Command syntax `register_biabd_rule <ident> (prio)?` for registering `BiAbd` hint rules. -/
elab "register_biabd_rule " id:ident prio?:(num)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let prio := prio?.map (·.getNat) |>.getD 1000
  liftTermElabM <| _root_.ProofLib.Sep.registerBiAbdRule name prio

/-- Attribute-style wrapper `@[biabd_rule] theorem ...` (default priority `1000`). -/
elab (priority := high) "@[biabd_rule]" cmd:command : command => do
  elabCommand cmd
  let some rawId := _root_.ProofLib.Sep.findDeclId? cmd.raw
    | throwError "@[biabd_rule]: expected a named theorem or declaration"
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload rawId
  liftTermElabM <| _root_.ProofLib.Sep.registerBiAbdRule fullName 1000

/-- Attribute-style wrapper `@[biabd_rule <prio>] theorem ...` with explicit priority. -/
elab (priority := high) "@[biabd_rule" prio:num "]" cmd:command : command => do
  elabCommand cmd
  let some rawId := _root_.ProofLib.Sep.findDeclId? cmd.raw
    | throwError "@[biabd_rule]: expected a named theorem or declaration"
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload rawId
  liftTermElabM <| _root_.ProofLib.Sep.registerBiAbdRule fullName prio.getNat

/-- Built-in spatial key table covering all `Arm64` / `ProofLib` primitive predicates. -/
def builtinSepKeySpecs : Array SepKeySpec := #[
  { headName := ``Arm64.pointsTo8,           keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo16,          keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo32,          keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo64,          keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo128,         keyArgIndices := #[0] },
  { headName := ``Arm64.pointsToBytes,       keyArgIndices := #[0] },
  { headName := ``Arm64.pointsToWords64,     keyArgIndices := #[0] },
  { headName := ``Arm64.memRegion,           keyArgIndices := #[0] },
  { headName := ``Arm64.regionBlock,         keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo8RO,         keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo16RO,        keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo32RO,        keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo64RO,        keyArgIndices := #[0] },
  { headName := ``Arm64.pointsTo128RO,       keyArgIndices := #[0] },
  { headName := ``Arm64.pointsToBytesRO,     keyArgIndices := #[0] },
  { headName := ``Arm64.pointsToWords64RO,   keyArgIndices := #[0] },
  { headName := ``Arm64.regionBlockRO,       keyArgIndices := #[0] },
  { headName := ``Arm64.memRegionProtNone,   keyArgIndices := #[0] },
  { headName := ``Arm64.memRegionLazy,       keyArgIndices := #[0] },
  { headName := ``Arm64.memMapped,           keyArgIndices := #[0] },
  { headName := ``Arm64.stackFrameAt,        keyArgIndices := #[0] },
  { headName := ``Arm64.stackFrame16At,      keyArgIndices := #[0] },
  { headName := ``Arm64.stackFrame32At,      keyArgIndices := #[0] },
  { headName := ``ProofLib.ghostMapElem,     keyArgIndices := #[0, 1], addrArgIdx := some 1 },
  { headName := ``ProofLib.ghostMapAuth,     keyArgIndices := #[0],    addrArgIdx := none },
  { headName := ``ProofLib.pointsToArray,    keyArgIndices := #[1, 2, 3], addrArgIdx := some 3 }
]

/-- Built-in `BiAbd` subsumption and carving rules. -/
def builtinBiAbdRules : Array (Name × Nat) := #[
  (``ProofLib.Sep.biabd_pointsTo8_memRegion,           900),
  (``ProofLib.Sep.biabd_pointsTo16_memRegion,          900),
  (``ProofLib.Sep.biabd_pointsTo32_memRegion,          900),
  (``ProofLib.Sep.biabd_pointsTo64_memRegion,          900),
  (``ProofLib.Sep.biabd_pointsTo128_memRegion,         900),
  (``ProofLib.Sep.biabd_pointsToBytes_memRegion,       900),
  (``ProofLib.Sep.biabd_pointsToWords64_memRegion,     900),
  (``ProofLib.Sep.biabd_pointsToBytes_split3,          1100),
  (``ProofLib.Sep.biabd_pointsToBytes_focus,           1100),
  (``ProofLib.Sep.biabd_pointsToBytes_focus8,          1100),
  (``ProofLib.Sep.biabd_pointsToBytes_focus64_le,      1100),
  (``ProofLib.Sep.biabd_pointsToBytes_partition_left,  850),
  (``ProofLib.Sep.biabd_pointsToBytes_partition_right, 850),
  (``ProofLib.Sep.biabd_memRegion_carve,               800)
]

/-- Build the active `BiAbdRegistry` by combining built-in specs/rules with any user entries
    registered in the current environment (`env.constants`). -/
def buildBiAbdRegistry : MetaM BiAbdRegistry := do
  let mut keySpecs : Std.HashMap Name SepKeySpec := {}
  for s in builtinSepKeySpecs do
    keySpecs := keySpecs.insert s.headName s
  let mut userKeys : Array (Name × Array Nat) := #[]
  let mut ruleNames : Array (Name × Nat) := builtinBiAbdRules
  let env ← getEnv
  -- Check both imported constants (`map₁`) and current-module constants (`map₂`).
  for (cName, _) in env.constants.map₁ do
    if let some k := decodeSepKeyName? cName then
      userKeys := userKeys.push k
    else if let some r := decodeBiAbdRuleName? cName then
      ruleNames := ruleNames.push r
  for (cName, _) in env.constants.map₂ do
    if let some k := decodeSepKeyName? cName then
      userKeys := userKeys.push k
    else if let some r := decodeBiAbdRuleName? cName then
      ruleNames := ruleNames.push r
  for (headName, idxs) in userKeys do
    if env.contains headName then
      let addrIdx? ← inferAddrKeyIdx headName idxs
      keySpecs := keySpecs.insert headName { headName, keyArgIndices := idxs, addrArgIdx := addrIdx? }
  let mut rules : DiscrTree BiAbdRule := {}
  for (thmName, prio) in ruleNames do
    if env.contains thmName then
      let r ← parseBiAbdRule thmName prio
      rules := rules.insertKeyValue r.keys r
  return { keySpecs, rules }

/-! ## Section 3: 5-Phase Bi-Abduction Engine -/

/-- Reduce `(Ctor a₀ ... aₙ).i` projections everywhere inside `e` without unfolding `SepProp` defs. -/
partial def reduceCtorProjs (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Core.transform e fun sub => do
    if let .proj _ idx structExpr := sub then
      let s := structExpr.consumeMData
      let ctorVal? : Option ConstructorVal :=
        match s.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some (.ctorInfo v) => some v
          | _ => none
        | none => none
      if let some ctorVal := ctorVal? then
        let args := s.getAppArgs
        if ctorVal.numParams + idx < args.size then
          return .visit args[ctorVal.numParams + idx]!
    return .continue

/-- Decide whether `ty` is a user-defined single-constructor witness record (such as a multi-field
    witness structure or `Prod`) that should be eta-expanded into field MVars when opening `∃∗`. -/
def shouldEtaWitnessStruct (ty : Expr) : MetaM (Option (ConstructorVal × Array Level)) := do
  let ty ← whnfD ty
  let .const declName us := ty.getAppFn | return none
  if declName == ``BitVec || declName == ``Fin || declName == ``Arm64.SepProp ||
      declName == ``Arm64.Memory || declName == ``Arm64.State || declName == ``Arm64.Heap ||
      declName == ``UInt8 || declName == ``UInt16 || declName == ``UInt32 || declName == ``UInt64 ||
      declName == ``Nat || declName == ``Int || declName == ``Bool || declName == ``String then
    return none
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? declName | return none
  if indVal.isRec || indVal.numIndices != 0 || indVal.ctors.length != 1 then return none
  let some (.ctorInfo ctorVal) := env.find? indVal.ctors.head! | return none
  if ctorVal.numFields == 0 || ctorVal.numFields > 12 then return none
  return some (ctorVal, us.toArray)

/-- True if `cName` is a built-in primitive `SepProp` predicate that must never be unfolded. -/
def isBuiltinOpaqueSepHead (cName : Name) : Bool :=
  builtinSepKeySpecs.any (·.headName == cName) || isKnownSpatialHead cName

/-- Collect top-level spatial constant heads appearing superficially in `e` (without unfolding
    non-reducible definitions) so symmetric user atoms stay folded when present on both sides. -/
partial def collectSurfaceHeads (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let acc ← collectSurfaceHeads (e.getArg! 0) acc
    collectSurfaceHeads (e.getArg! 1) acc
  else if e.isAppOfArity ``Arm64.SepProp.sepExists 2 then
    let body := e.getArg! 1
    if let .lam n ty b bi := body then
      withLocalDecl n bi ty fun x => collectSurfaceHeads (b.instantiate1 x) acc
    else
      return acc
  else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let acc ← collectSurfaceHeads (e.getArg! 3) acc
    collectSurfaceHeads (e.getArg! 4) acc
  else if let .fvar fv := e.getAppFn then
    if let some val ← fv.getValue? then
      collectSurfaceHeads (mkAppN val e.getAppArgs) acc
    else
      return acc
  else if let .const cName _ := e.getAppFn then
    if cName == ``Arm64.SepProp.emp || cName == ``Arm64.SepProp.pure then
      return acc
    if isBuiltinOpaqueSepHead cName then
      return acc.insert cName
    if (← getReducibilityStatus cName) == .reducible && !(← isProjectionFn cName) then
      if let some u ← withReducible (unfoldDefinition? e) then
        return ← collectSurfaceHeads u acc
    return acc.insert cName
  else
    return acc

/-- Search bounded structure projections of a local hypothesis `e : eTy` for a proof of `targetTy`. -/
partial def findStructProjMatching? (e eTy targetTy : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if ← withReducible (isDefEq eTy targetTy) then return some e
  if fuel == 0 then return none
  let eTyW ← whnfD eTy
  let .const indName _ := eTyW.getAppFn | return none
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? indName | return none
  if indVal.ctors.length != 1 then return none
  let some (.ctorInfo ctorVal) := env.find? indVal.ctors.head! | return none
  for idx in [:ctorVal.numFields] do
    let projE := Expr.proj indName idx e
    let projTy ← inferType projE
    if let some hit ← findStructProjMatching? projE projTy targetTy (fuel - 1) then
      return some hit
  return none

/-- Speculatively run `stx` on subgoal `g`, saving and restoring `Core.State.messages` (and rolling
    back `Meta.State` unless `stx` succeeds with zero logged errors and `acceptRemaining rem`) so
    speculative probes never leak error or warning diagnostics into the file's message log. -/
def runSilentTacticProbe (g : MVarId) (stx : TSyntax `tactic)
    (acceptRemaining : List MVarId → Bool := (·.isEmpty)) :
    TacticM (Option (List MVarId)) := do
  let savedMeta ← saveState
  let savedMsgs ← Core.getMessageLog
  Core.resetMessageLog
  try
    let rem ← withOptions (fun o =>
        (o.setBool `linter.unusedSimpArgs false).setBool `warningAsError false) do
      Tactic.run g do
        withoutRecover (Tactic.evalTactic stx)
    let probeMsgs ← Core.getMessageLog
    Core.setMessageLog savedMsgs
    if !probeMsgs.hasErrors && acceptRemaining rem then
      return some rem
    else
      restoreState savedMeta
      return none
  catch _ =>
    Core.setMessageLog savedMsgs
    restoreState savedMeta
    return none

/-- Try to prove `prop` or `¬ prop` quickly from local hypotheses (including nested `.1`/`.2`
    projections, `decide`, and bounded `omega`) to reduce `if c then T else E` inside `SepProp`
    definitions. -/
def tryDecideBranchProp? (prop : Expr) : TacticM (Option (Bool × Expr)) := do
  let prop ← instantiateMVars prop
  let posMVar ← mkFreshExprMVar prop
  if let some prf ← tryQuickBranchProof? posMVar.mvarId! prop then
    return some (true, prf)
  let negProp := mkApp (mkConst ``Not) prop
  let negMVar ← mkFreshExprMVar negProp
  if let some prf ← tryQuickBranchProof? negMVar.mvarId! negProp then
    return some (false, prf)
  return none
where
  tryQuickBranchProof? (g : MVarId) (ty : Expr) : TacticM (Option Expr) := do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if let some p ← findStructProjMatching? decl.toExpr decl.type ty 3 then
        return some p
    let omegaTacs ← ProofLib.omegaDefaultTacs
    if let some prf ← ProofLib.proveOmegaBoundedTerm? ty omegaTacs then
      return some prf
    let saved ← saveState
    let tac ← `(tactic| first | assumption | decide | trivial)
    if (← runSilentTacticProbe g tac).isSome then
      let prf ← instantiateMVars (mkMVar g)
      if !prf.hasExprMVar then return some prf
    restoreState saved
    return none

/-- Try one explicit unfolding or branch-reduction step on `Focus : SepProp`, returning
    `some (Focus', heq : Focus = Focus')` without triggering kernel unfolding of non-reducible defs. -/
def unfoldSepFocusStep? (reg : BiAbdRegistry) (oppHeads : NameSet) (allowLocalEqHyp : Bool)
    (e0 : Expr) : TacticM (Option (Expr × Expr)) := do
  let e := (← instantiateMVars e0).consumeMData.headBeta
  if e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    let instDec := e.getArg! 2
    let tBranch := e.getArg! 3
    let fBranch := e.getArg! 4
    if let some (isTrueBranch, hCond) ← tryDecideBranchProp? c then
      let u1 := Level.one
      if isTrueBranch then
        let heq := mkAppN (mkConst ``if_pos [u1]) #[c, instDec, hCond, mkConst ``Arm64.SepProp, tBranch, fBranch]
        return some (tBranch, heq)
      else
        let heq := mkAppN (mkConst ``if_neg [u1]) #[c, instDec, hCond, mkConst ``Arm64.SepProp, tBranch, fBranch]
        return some (fBranch, heq)
  if let .fvar fv := e.getAppFn then
    if let some val ← fv.getValue? then
      let e' := (mkAppN val e.getAppArgs).headBeta
      return some (e', ← mkEqRefl e')
    if allowLocalEqHyp && e.getAppArgs.isEmpty then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let dty := (← instantiateMVars decl.type).consumeMData
        if dty.isAppOfArity ``Eq 3 && (dty.getArg! 0).isConstOf ``Arm64.SepProp then
          if dty.getArg! 1 == e then
            let rhs := dty.getArg! 2
            if !rhs.containsFVar fv then
              return some (rhs, decl.toExpr)
  let .const cName _ := e.getAppFn | return none
  if cName == ``Arm64.SepProp.sepConj || cName == ``Arm64.SepProp.emp ||
      cName == ``Arm64.SepProp.pure || cName == ``Arm64.SepProp.sepExists ||
      isBuiltinOpaqueSepHead cName then
    return none
  if ← isProjectionFn cName then return none
  -- Keep registered user spatial predicates folded when the same head is also on the opposite side.
  if reg.keySpecs.contains cName && oppHeads.contains cName then
    return none
  if (← getReducibilityStatus cName) == .reducible then
    if let some e' ← withReducible (unfoldDefinition? e) then
      let e' ← reduceCtorProjs e'.headBeta
      return some (e', ← mkEqRefl e')
  if let some eqns ← getEqnsFor? cName then
    for eqn in eqns do
      let ci ← getConstInfo eqn
      let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
      let (mvars, _, concl) ← forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams us)
      if concl.isAppOfArity ``Eq 3 then
        let lhsEq := concl.getArg! 1
        let rhsEq := concl.getArg! 2
        if ← withReducibleAndInstances (isDefEq lhsEq e) then
          if ← mvars.allM fun mv => mv.mvarId!.isAssigned then
            let prf0 := mkAppN (mkConst eqn us) mvars
            let rhs0 ← instantiateMVars rhsEq
            let rhsClean ← reduceCtorProjs rhs0.headBeta
            let prf ← if rhsClean == rhs0 then pure prf0 else mkEqTrans prf0 (← mkEqRefl rhsClean)
            return some (rhsClean, prf)
  return none

/-- Fast check whether a `SepProp` subtree is already 100% clean spatial atoms (no `emp`, no `⌜φ⌝`,
    no `∃∗`, no `ite`, no local `SepProp` `let`/eq-hyp, and no composite defs needing unfold), so
    the zipper can shift the entire subtree in a single `O(1)` `lhs_keep` / `rhs_keep` step. -/
partial def isCleanSpatialSubtree (reg : BiAbdRegistry) (oppHeads : NameSet)
    (allowLocalEqHyp : Bool) (e0 : Expr) : TacticM Bool := do
  let e := (← instantiateMVars e0).consumeMData.headBeta
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    return (← isCleanSpatialSubtree reg oppHeads allowLocalEqHyp (e.getArg! 0)) &&
           (← isCleanSpatialSubtree reg oppHeads allowLocalEqHyp (e.getArg! 1))
  if e.isConstOf ``Arm64.SepProp.emp || e.isAppOfArity ``Arm64.SepProp.pure 1 ||
      e.isAppOfArity ``Arm64.SepProp.sepExists 2 || e.isAppOfArity ``ite 5 ||
      e.isAppOfArity ``dite 5 then
    return false
  if (← unfoldSepFocusStep? reg oppHeads allowLocalEqHyp e).isSome then
    return false
  return true

/-- Phase 1A: Single-pass LHS skolemization and pure extraction over `(Acc ∗ (Focus ∗ Rest)) ⊢ Q`.
    Calls continuation `k` with the resulting clean spatial expression `Acc` inside the extended
    `LocalContext` containing all skolemized `x` and `hφ` hypotheses. -/
partial def reduceLHS (reg : BiAbdRegistry) (rhsHeads : NameSet)
    (P0 Q : Expr) (k : Expr → TacticM Expr) : TacticM Expr := do
  if ← isCleanSpatialSubtree reg rhsHeads true P0 then
    return ← k ((← instantiateMVars P0).consumeMData.headBeta)
  let empE := mkConst ``Arm64.SepProp.emp
  let inner ← go 64 none P0 empE
  return mkApp3 (mkConst ``ProofLib.Sep.lhs_start) P0 Q inner
where
  go (unfoldFuel : Nat) (acc? : Option Expr) (focus0 rest0 : Expr) : TacticM Expr := do
    let focus := (← instantiateMVars focus0).consumeMData.headBeta
    let rest := (← instantiateMVars rest0).consumeMData.headBeta
    let accE := acc?.getD (mkConst ``Arm64.SepProp.emp)
    let empE := mkConst ``Arm64.SepProp.emp
    if focus.isConstOf ``Arm64.SepProp.emp then
      if rest.isConstOf ``Arm64.SepProp.emp then
        let sub ← k accE
        return mkApp3 (mkConst ``ProofLib.Sep.lhs_done) accE Q sub
      else
        let sub ← go 64 acc? rest empE
        return mkApp4 (mkConst ``ProofLib.Sep.lhs_emp) accE rest Q sub
    if ← isCleanSpatialSubtree reg rhsHeads true focus then
      match acc? with
      | none =>
        let sub ← go 64 (some focus) rest empE
        return mkApp4 (mkConst ``ProofLib.Sep.lhs_keep_first) focus rest Q sub
      | some acc =>
        let acc' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) acc focus
        let sub ← go 64 (some acc') rest empE
        return mkApp5 (mkConst ``ProofLib.Sep.lhs_keep) acc focus rest Q sub
    if unfoldFuel > 0 then
      if let some (focus', heq) ← unfoldSepFocusStep? reg rhsHeads true focus then
        let sub ← go (unfoldFuel - 1) acc? focus' rest
        return mkAppN (mkConst ``ProofLib.Sep.lhs_eq) #[accE, focus, focus', rest, Q, heq, sub]
    if focus.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      let a := focus.getArg! 0
      let b := focus.getArg! 1
      if rest.isConstOf ``Arm64.SepProp.emp then
        let sub ← go 64 acc? a b
        return mkApp4 (mkConst ``ProofLib.Sep.lhs_sep_emp) accE a b Q |>.app sub
      else
        let rest' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) b rest
        let sub ← go 64 acc? a rest'
        return mkAppN (mkConst ``ProofLib.Sep.lhs_sep) #[accE, a, b, rest, Q, sub]
    if focus.isAppOfArity ``Arm64.SepProp.pure 1 then
      let φ := (focus.getArg! 0).consumeMData
      if φ.isAppOfArity ``And 2 then
        let φ1 := φ.getArg! 0
        let φ2 := φ.getArg! 1
        return ← withLocalDeclD `h_pure1 φ1 fun h1 =>
          withLocalDeclD `h_pure2 φ2 fun h2 => do
            let sub ← go 64 acc? rest empE
            let fn ← mkLambdaFVars #[h1, h2] sub
            return mkAppN (mkConst ``ProofLib.Sep.lhs_pure_and) #[accE, φ1, φ2, rest, Q, fn]
      else
        return ← withLocalDeclD `h_pure φ fun hφ => do
          let sub ← go 64 acc? rest empE
          let fn ← mkLambdaFVars #[hφ] sub
          return mkAppN (mkConst ``ProofLib.Sep.lhs_pure) #[accE, φ, rest, Q, fn]
    if focus.isAppOfArity ``Arm64.SepProp.sepExists 2 then
      let α := focus.getArg! 0
      let F := focus.getArg! 1
      let u ← getLevel α
      let xName := match F with | .lam n _ _ _ => n | _ => `x_skolem
      return ← withLocalDeclD xName α fun x => do
        let fx := (F.beta #[x]).headBeta
        let sub ← go 64 acc? fx rest
        let fn ← mkLambdaFVars #[x] sub
        return mkAppN (mkConst ``ProofLib.Sep.lhs_exists [u]) #[α, accE, F, rest, Q, fn]
    match acc? with
    | none =>
      let sub ← go 64 (some focus) rest empE
      return mkApp4 (mkConst ``ProofLib.Sep.lhs_keep_first) focus rest Q sub
    | some acc =>
      let acc' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) acc focus
      let sub ← go 64 (some acc') rest empE
      return mkApp5 (mkConst ``ProofLib.Sep.lhs_keep) acc focus rest Q sub

/-- Phase 1B: Single-pass RHS telescope creation and pure deferral over `P ⊢ (Acc ∗ (Focus ∗ Rest))`.
    Creates delayed witness MVars for `∃∗` (eta-expanding user witness structures so projections
    reduce immediately) and pushes `⌜ψ⌝` goals onto `pureQueue` for Phase 5. -/
partial def reduceRHS (reg : BiAbdRegistry) (lhsHeads : NameSet)
    (pureQueue : IO.Ref (Array (MVarId × Expr)))
    (P Q0 : Expr) (k : Expr → TacticM Expr) : TacticM Expr := do
  if ← isCleanSpatialSubtree reg lhsHeads false Q0 then
    return ← k ((← instantiateMVars Q0).consumeMData.headBeta)
  let empE := mkConst ``Arm64.SepProp.emp
  let inner ← go 64 none Q0 empE
  return mkApp3 (mkConst ``ProofLib.Sep.rhs_start) P Q0 inner
where
  go (unfoldFuel : Nat) (acc? : Option Expr) (focus0 rest0 : Expr) : TacticM Expr := do
    let focus := (← instantiateMVars focus0).consumeMData.headBeta
    let rest := (← instantiateMVars rest0).consumeMData.headBeta
    let accE := acc?.getD (mkConst ``Arm64.SepProp.emp)
    let empE := mkConst ``Arm64.SepProp.emp
    if focus.isConstOf ``Arm64.SepProp.emp then
      if rest.isConstOf ``Arm64.SepProp.emp then
        let sub ← k accE
        return mkApp3 (mkConst ``ProofLib.Sep.rhs_done) P accE sub
      else
        let sub ← go 64 acc? rest empE
        return mkApp4 (mkConst ``ProofLib.Sep.rhs_emp) P accE rest sub
    if ← isCleanSpatialSubtree reg lhsHeads false focus then
      match acc? with
      | none =>
        let sub ← go 64 (some focus) rest empE
        return mkApp4 (mkConst ``ProofLib.Sep.rhs_keep_first) P focus rest sub
      | some acc =>
        let acc' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) acc focus
        let sub ← go 64 (some acc') rest empE
        return mkApp5 (mkConst ``ProofLib.Sep.rhs_keep) P acc focus rest sub
    if unfoldFuel > 0 then
      if let some (focus', heq) ← unfoldSepFocusStep? reg lhsHeads false focus then
        let sub ← go (unfoldFuel - 1) acc? focus' rest
        return mkAppN (mkConst ``ProofLib.Sep.rhs_eq) #[P, accE, focus, focus', rest, heq, sub]
    if focus.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      let a := focus.getArg! 0
      let b := focus.getArg! 1
      if rest.isConstOf ``Arm64.SepProp.emp then
        let sub ← go 64 acc? a b
        return mkAppN (mkConst ``ProofLib.Sep.rhs_sep_emp) #[P, accE, a, b, sub]
      else
        let rest' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) b rest
        let sub ← go 64 acc? a rest'
        return mkAppN (mkConst ``ProofLib.Sep.rhs_sep) #[P, accE, a, b, rest, sub]
    if focus.isAppOfArity ``Arm64.SepProp.pure 1 then
      let ψ ← reduceCtorProjs (← instantiateMVars (focus.getArg! 0)).consumeMData
      let hψ ← mkFreshExprMVar ψ
      pureQueue.modify (·.push (hψ.mvarId!, ψ))
      let sub ← go 64 acc? rest empE
      return mkAppN (mkConst ``ProofLib.Sep.rhs_pure) #[P, accE, ψ, rest, hψ, sub]
    if focus.isAppOfArity ``Arm64.SepProp.sepExists 2 then
      let β := focus.getArg! 0
      let G := focus.getArg! 1
      let u ← getLevel β
      let yName := match G with | .lam n _ _ _ => n | _ => `w
      let w ←
        if let some (ctorVal, ctorLvls) ← shouldEtaWitnessStruct β then
          let tyArgs := (← whnfD β).getAppArgs.take ctorVal.numParams
          let ctorFn := mkAppN (mkConst ctorVal.name ctorLvls.toList) tyArgs
          let ctorTy ← inferType ctorFn
          let (fieldMVars, _, _) ← forallMetaTelescope ctorTy
          pure (mkAppN ctorFn fieldMVars)
        else
          mkFreshExprMVar β (userName := yName)
      let gw0 := (G.beta #[w]).headBeta
      let gwClean ← reduceCtorProjs gw0
      let sub ←
        if gwClean == gw0 then
          go 64 acc? gw0 rest
        else
          let s ← go 64 acc? gwClean rest
          let heq ← mkEqRefl gwClean
          pure (mkAppN (mkConst ``ProofLib.Sep.rhs_eq) #[P, accE, gw0, gwClean, rest, heq, s])
      return mkAppN (mkConst ``ProofLib.Sep.rhs_exists [u]) #[β, P, accE, G, rest, w, sub]
    match acc? with
    | none =>
      let sub ← go 64 (some focus) rest empE
      return mkApp4 (mkConst ``ProofLib.Sep.rhs_keep_first) P focus rest sub
    | some acc =>
      let acc' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) acc focus
      let sub ← go 64 (some acc') rest empE
      return mkApp5 (mkConst ``ProofLib.Sep.rhs_keep) P acc focus rest sub

/-! ### Phase 2 & 3 Data Structures & Shared `ProofLib.Sep.Addr` Canonicalization -/

/-- Unfold local `let`-bound FVars inside `e` via ζ-reduction (`Eq.refl` is definitionally exact). -/
partial def unfoldAddrLets (e : Expr) : MetaM Expr := do
  Core.transform (← instantiateMVars e) fun sub => do
    if let .fvar fv := sub then
      if let some val ← fv.getValue? then
        return .visit val
    return .continue

/-- True if `e` looks like an additive offset term (`BitVec.ofNat`, numeral, `zeroExtend`, shift,
    or multiplication by stride) rather than a base pointer root. -/
def isLikelyOffsetExpr (letVals : Std.HashMap FVarId Expr) (e0 : Expr) : Bool :=
  let e := match e0.consumeMData with
    | .fvar fv => (letVals[fv]?.getD e0).consumeMData
    | other => other
  (canonBvLits e).isAppOfArity ``BitVec.ofNat 2 ||
  e.isAppOf ``BitVec.ofNat ||
  e.isAppOf ``OfNat.ofNat ||
  e.isAppOf ``BitVec.zeroExtend ||
  e.isAppOf ``BitVec.setWidth ||
  e.isAppOf ``HShiftLeft.hShiftLeft ||
  e.isAppOf ``HMul.hMul

/-- Purely syntactic base-pointer root peeler wired to `ProofLib.Sep.peelAddrRoot` and `CtxFacts`.
    Strips constant offsets, local `let` bindings, acyclic `ctx.bvEqs`, and symbolic additive
    offsets (`+ BitVec.ofNat 64 n`, `+ u.zeroExtend 64`, shifts, strides) with zero `whnf` and
    zero `isDefEq`. -/
partial def peelSymbolicBase (ctx : CtxFacts) (e0 : Expr) (fuel : Nat := 16) : Expr :=
  if fuel == 0 then e0.consumeMData
  else
    let (r0, _) := ProofLib.Sep.peelAddrRoot ctx.letVals e0
    let r := r0.consumeMData
    match ctx.bvEqs.find? (fun (lhs, _, _) => lhs == r) with
    | some (_, rhs, _) => peelSymbolicBase ctx rhs (fuel - 1)
    | none =>
      match r with
      | .fvar fv =>
        match ctx.letVals[fv]? with
        | some v => peelSymbolicBase ctx v (fuel - 1)
        | none => r
      | _ =>
        if r.isAppOfArity ``HSub.hSub 6 && (r.getArg! 0).consumeMData.isAppOfArity ``BitVec 1 then
          peelSymbolicBase ctx (r.getArg! 4) (fuel - 1)
        else if r.isAppOfArity ``HAdd.hAdd 6 && (r.getArg! 0).consumeMData.isAppOfArity ``BitVec 1 then
          let lhs := r.getArg! 4
          let rhs := r.getArg! 5
          if isLikelyOffsetExpr ctx.letVals lhs && !isLikelyOffsetExpr ctx.letVals rhs then
            peelSymbolicBase ctx rhs (fuel - 1)
          else
            peelSymbolicBase ctx lhs (fuel - 1)
        else
          r

/-- True when `a` and `b` share the exact same canonical 64-bit root with distinct signed byte
    offsets in `[-2^63, 2^63)`, making `a = b` unsatisfiable in `BitVec 64` without calling `whnf`
    or `isDefEq`. -/
def isDefinitelyUnequalAddr (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64)) (a0 b0 : Expr) : MetaM Bool := do
  let a ← instantiateMVars a0
  let b ← instantiateMVars b0
  if a == b then return false
  unless ← isBV64Expr a do return false
  let (rA, oA) := ProofLib.Sep.peelAddrRoot ctx.letVals a
  let (rB, oB) := ProofLib.Sep.peelAddrRoot ctx.letVals b
  if rA == rB && oA != oB then return true
  let la? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache a catch _ => pure none
  let lb? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache b catch _ => pure none
  if let (some la, some lb) := (la?, lb?) then
    if la.root == lb.root && la.byteOff != lb.byteOff then
      return true
  return false

/-- Fast address equality check wired to `ProofLib.Sep.peelAddrRoot`, `canonAddr64`, and
    `proveAddrEqFast?`:
    - Rejects unequal offsets on the same base (including symbolic bases `ptr + u.zeroExtend 64`)
      in $O(1)$ without calling `whnf`, `isDefEq`, or `BV.Lin.proveEq?`.
    - Canonicalizes `BitVec.ofNat 64 u.toNat` to `u.zeroExtend 64` in 1 step via
      `bitvec64_ofNat_toNat_eq_zeroExtend`. -/
def tryFastAddrEq? (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64)) (a0 b0 : Expr) : MetaM (Option Expr) := do
  let a ← instantiateMVars a0
  let b ← instantiateMVars b0
  if a == b then return some (← mkEqRefl a)
  if ← isBV64Expr a then
    let (rA, oA) := ProofLib.Sep.peelAddrRoot ctx.letVals a
    let (rB, oB) := ProofLib.Sep.peelAddrRoot ctx.letVals b
    if rA == rB && oA != oB then return none
    let la? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache a catch _ => pure none
    let lb? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache b catch _ => pure none
    if let (some la, some lb) := (la?, lb?) then
      if la.root == lb.root && la.byteOff != lb.byteOff then
        return none
    return ← ProofLib.Sep.proveAddrEqFast? ctx addrCache a b
  let aU ← unfoldAddrLets a
  let bU ← unfoldAddrLets b
  if aU == bU then return some (← mkEqRefl aU)
  if let some prf ← ProofLib.BV.Lin.proveEq? aU bU then
    if a == aU && b == bU then return some prf
    return some (← mkExpectedTypeHint prf (← mkEq a b))
  return none

/-- Full address equality prover used for contiguity checks during Phase 3 coalescing and Phase 5
    `Q_addr` discharge (`tryFastAddrEq?` + unequal-offset guard + `expandAddrExpr` + bounded
    `bv_omega`). -/
def proveAddrEqFull? (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64)) (a0 b0 : Expr) : TacticM (Option Expr) := do
  let a ← instantiateMVars a0
  let b ← instantiateMVars b0
  if let some prf ← tryFastAddrEq? ctx addrCache a b then return some prf
  if ← isDefinitelyUnequalAddr ctx addrCache a b then return none
  let is64 ← isBV64Expr a
  let (aExp, ha?) ← if is64 then ProofLib.Sep.expandAddrExpr ctx a else pure (← unfoldAddrLets a, none)
  let (bExp, hb?) ← if is64 then ProofLib.Sep.expandAddrExpr ctx b else pure (← unfoldAddrLets b, none)
  let chainBack (pMid : Expr) : MetaM Expr := do
    let p1 ← match ha? with
      | some pa => mkEqTrans pa pMid
      | none => if a == aExp then pure pMid else mkExpectedTypeHint pMid (← mkEq a bExp)
    match hb? with
    | some pb => mkEqTrans p1 (← mkEqSymm pb)
    | none => if b == bExp then pure p1 else mkExpectedTypeHint p1 (← mkEq a b)
  let eqTy ← mkEq aExp bExp
  let omegaTacs ← ProofLib.omegaDefaultTacs
  if let some prf ← ProofLib.proveOmegaBoundedTerm? eqTy omegaTacs then
    return some (← chainBack prf)
  let saved ← saveState
  let g ← mkFreshExprMVar eqTy
  let tac ← `(tactic| (
    try simp (disch := (first
      | byte_region_len
      | (try simp only [_root_.List.length_take, _root_.List.length_drop,
          _root_.List.length_append, _root_.List.length_replicate] at *; omega))) only [
      _root_.List.length_take, _root_.List.length_drop, _root_.List.length_append,
      _root_.List.length_cons, _root_.List.length_nil, _root_.List.length_replicate,
      _root_.ProofLib.ByteSlice.write8_length, _root_.ProofLib.ByteSlice.write16_length,
      _root_.ProofLib.ByteSlice.write32_length, _root_.ProofLib.ByteSlice.write64_length] at *
    bv_omega))
  if (← runSilentTacticProbe g.mvarId! tac).isSome then
    let prf ← instantiateMVars g
    if !prf.hasExprMVar then
      return some (← chainBack prf)
  restoreState saved
  return none

/-- Extract a `Nat` offset expression when `targetAddr` is at a non-negative constant or symbolic
    additive offset from `base` (used when carving a slice whose payload MVar does not fix `off`). -/
partial def inferNatOffsetFromAddr? (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (base targetAddr : Expr) : MetaM (Option Expr) := do
  let la? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache base catch _ => pure none
  let ta? ← try some <$> ProofLib.Sep.canonAddr64 ctx addrCache targetAddr catch _ => pure none
  if let (some la, some ta) := (la?, ta?) then
    if la.root == ta.root && ta.byteOff >= la.byteOff then
      return some (toExpr (ta.byteOff - la.byteOff).toNat)
  let (b, _) ← ProofLib.Sep.expandAddrExpr ctx base
  let (t, _) ← ProofLib.Sep.expandAddrExpr ctx targetAddr
  peelAddChain b t
where
  peelAddChain (b t : Expr) : MetaM (Option Expr) := do
    if b == t then return some (mkRawNatLit 0)
    if t.isAppOfArity ``HAdd.hAdd 6 then
      let l := t.getArg! 4
      let r := t.getArg! 5
      if l == b then
        return bvOffsetToNat? r
      if let some prev ← peelAddChain b l then
        if let some cur := bvOffsetToNat? r then
          return some (mkApp2 (mkConst ``Nat.add) prev cur)
    return none
  bvOffsetToNat? (off : Expr) : Option Expr :=
    let off := off.consumeMData
    if off.isAppOfArity ``BitVec.ofNat 2 then
      some (off.getArg! 1)
    else
      match bvLitPure? off with
      | some (_, v) => some (toExpr v)
      | none =>
        if off.isAppOfArity ``BitVec.zeroExtend 3 || off.isAppOfArity ``BitVec.setWidth 3 then
          some (mkApp2 (mkConst ``BitVec.toNat) (off.getArg! 0) (off.getArg! 2))
        else
          none

/-- True if `hName` is a splittable/coalesceable range predicate (`↦ₛ`, `↦ᵣ`, `memRegion`). -/
def isVariableRangeHead (hName : Name) : Bool :=
  hName == ``Arm64.pointsToBytes || hName == ``Arm64.pointsToBytesRO || hName == ``Arm64.memRegion

/-- Look up the `SepKeySpec` for an atom expression `e` (constant, local `FVar`, or projection).
    Unregistered constant heads with a leading `BitVec 64` argument default to `keyArgIndices := #[0]`;
    container-method heads `C.Pred c addr ...` default to `keyArgIndices := #[0, 1], addrArgIdx := some 1`. -/
def getAtomKeySpec (reg : BiAbdRegistry) (e : Expr) : MetaM (Option SepKeySpec) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  match e.getAppFn with
  | .const hName _ =>
    if let some s := reg.keySpecs[hName]? then return some s
    if args.isEmpty then
      return some { headName := hName, keyArgIndices := #[], addrArgIdx := none }
    if ← isBV64Expr args[0]! then
      return some { headName := hName, keyArgIndices := #[0], addrArgIdx := some 0 }
    if args.size >= 2 then
      if ← isBV64Expr args[1]! then
        return some { headName := hName, keyArgIndices := #[0, 1], addrArgIdx := some 1 }
    return some { headName := hName, keyArgIndices := #[0], addrArgIdx := none }
  | .fvar fv =>
    let tag := Name.mkSimple "_fvarHead" ++ fv.name
    if args.isEmpty then
      return some { headName := tag, keyArgIndices := #[], addrArgIdx := none }
    if ← isBV64Expr args[0]! then
      return some { headName := tag, keyArgIndices := #[0], addrArgIdx := some 0 }
    return some { headName := tag, keyArgIndices := #[0], addrArgIdx := none }
  | .proj tyName idx _ =>
    let tag := (Name.mkSimple "_projHead" ++ tyName).num idx
    if args.isEmpty then
      return some { headName := tag, keyArgIndices := #[], addrArgIdx := none }
    if ← isBV64Expr args[0]! then
      return some { headName := tag, keyArgIndices := #[0], addrArgIdx := some 0 }
    return some { headName := tag, keyArgIndices := #[0], addrArgIdx := none }
  | _ => return none

/-- Check whether `gAtom` and `hAtom` share the exact same spatial predicate head. -/
def atomHeadMatches (gAtom hAtom : Expr) (gSpec : SepKeySpec) : Bool :=
  match gAtom.getAppFn.constName?, hAtom.getAppFn.constName? with
  | some gn, some hn => gn == hn && gn == gSpec.headName
  | none, none       => gAtom.getAppFn == hAtom.getAppFn
  | _, _             => false

/-- Flatten a spatial `SepProp` expression into an array of leaf atoms (dropping `emp`). -/
partial def flattenSpatialAtoms (e0 : Expr) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e0).consumeMData.headBeta
  if e.isConstOf ``Arm64.SepProp.emp then return #[]
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    return (← flattenSpatialAtoms (e.getArg! 0)) ++ (← flattenSpatialAtoms (e.getArg! 1))
  return #[e]

/-- Build a right-associated `∗`-chain from an array of `SepProp`s (`emp` if empty). -/
def mkSepChain (as : Array Expr) : Expr :=
  if as.isEmpty then mkConst ``Arm64.SepProp.emp
  else
    let last := as[as.size - 1]!
    (as.pop.foldr (fun a acc => mkApp2 (mkConst ``Arm64.SepProp.sepConj) a acc) last)

/-- Build congruence equality `f a₀ ... aₙ = f b₀ ... bₙ` given per-argument optional proofs. -/
def buildAppCongrEq (fn : Expr) (oldArgs newArgs : Array Expr)
    (argEqs : Array (Option Expr)) : MetaM (Option Expr) := do
  if argEqs.all Option.isNone then return none
  let mut prf ← mkEqRefl fn
  for oldA in oldArgs, p? in argEqs do
    match p? with
    | some p => prf ← mkCongr prf p
    | none   => prf ← mkCongrFun prf oldA
  let _ := newArgs
  return some prf

/-- Match non-key (payload) arguments of `H` (`hArgs`) against `G` (`gArgs`) after spatial keys
    have already been matched. Uses `withReducible` when both sides are ground so non-reducible
    `BitVec`/`List` operations are never unfolded during Phase 2. -/
def unifyPayloadsAfterKeyMatch (keyIdxs : Array Nat) (allowGroundPayloadEq : Bool)
    (hArgs gArgs : Array Expr)
    (pureQueue : IO.Ref (Array (MVarId × Expr))) :
    MetaM (Option (Array Expr × Array (Option Expr))) := do
  if hArgs.size != gArgs.size then return none
  let saved ← saveState
  let mut newArgs := hArgs
  let mut eqs : Array (Option Expr) := Array.replicate hArgs.size none
  let mut pendingPures : Array (MVarId × Expr) := #[]
  for idx in [:hArgs.size] do
    if keyIdxs.contains idx then continue
    let ha ← instantiateMVars hArgs[idx]!
    let ga ← instantiateMVars gArgs[idx]!
    if ha == ga then continue
    let bothGround := !ha.hasExprMVar && !ga.hasExprMVar
    let defEqOk ← if bothGround then withReducible (isDefEq ha ga) else isDefEq ha ga
    if defEqOk then
      let ga' ← instantiateMVars ga
      newArgs := newArgs.set! idx ga'
    else if allowGroundPayloadEq && bothGround then
      let haTy ← inferType ha
      let gaTy ← inferType ga
      unless ← withReducibleAndInstances (isDefEq haTy gaTy) do
        restoreState saved
        return none
      let eqTy ← mkEq ha ga
      let eqMVar ← mkFreshExprMVar eqTy
      pendingPures := pendingPures.push (eqMVar.mvarId!, eqTy)
      newArgs := newArgs.set! idx ga
      eqs := eqs.set! idx (some eqMVar)
    else
      restoreState saved
      return none
  for p in pendingPures do
    pureQueue.modify (·.push p)
  return some (newArgs, eqs)

/-- Active LHS item tracked during Phases 2–4. -/
structure PoolAtom where
  expr  : Expr
  alive : Bool := true
  deriving Inhabited

/-- Try to apply a registered `BiAbdRule` from `reg.rules` (`DiscrTree`) to consume `hExpr` and
    produce `gExpr` (plus optional carved residuals), resolving 1-step canonical address equalities
    immediately and rejecting unequal offsets without calling `whnf` or `isDefEq`. -/
def tryApplyDiscrTreeRule? (reg : BiAbdRegistry) (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (addrQueue : IO.Ref (Array (MVarId × Expr)))
    (pureQueue : IO.Ref (Array (MVarId × Expr)))
    (hExpr gExpr : Expr) : MetaM (Option (Expr × Expr × Array Expr)) := do
  let hExpr ← instantiateMVars hExpr
  let gExpr ← instantiateMVars gExpr
  let query := mkApp2 (mkConst ``Arm64.SepProp.Entails) (canonBvLits hExpr) (canonBvLits gExpr)
  let candidates ← reg.rules.getUnify query
  let sorted := candidates.qsort (fun a b => a.prio > b.prio)
  for rule in sorted do
    let saved ← saveState
    let ci ← getConstInfo rule.thmName
    let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let (mvars, _, concl0) ← forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams us)
    let concl := (← instantiateMVars concl0).consumeMData
    let (rLhs, rGoal, rRest?) ←
      match rule.kind with
      | .entailsSub =>
        pure (concl.getArg! 0, concl.getArg! 1, none)
      | .entailsCarve =>
        let r := (concl.getArg! 1).consumeMData
        pure (concl.getArg! 0, r.getArg! 0, some (r.getArg! 1))
      | .eqSplit =>
        let r := (concl.getArg! 2).consumeMData
        pure (concl.getArg! 1, r.getArg! 0, some (r.getArg! 1))
    -- Key-First rule instantiation: unify LHS atom first!
    unless ← isDefEq rLhs hExpr do
      restoreState saved
      continue
    -- Infer unassigned Nat offset parameter (`off` or `k`) from spatial key offset BEFORE unifying payloads.
    if let (some hSpec, some gSpec) := (← getAtomKeySpec reg hExpr, ← getAtomKeySpec reg gExpr) then
      if let (some hAIdx, some gAIdx) := (hSpec.addrArgIdx, gSpec.addrArgIdx) then
        let hArgs := hExpr.getAppArgs
        let gArgs := gExpr.getAppArgs
        if hAIdx < hArgs.size && gAIdx < gArgs.size then
          for mv in mvars do
            if !(← mv.mvarId!.isAssigned) then
              let mvTy ← inferType mv
              if mvTy.isConstOf ``Nat then
                let uName := (← mv.mvarId!.getDecl).userName
                if uName == `off || uName == `k then
                  if let some offExpr ← inferNatOffsetFromAddr? ctx addrCache hArgs[hAIdx]! gArgs[gAIdx]! then
                    let _ ← isDefEq mv offExpr
    -- Guard goal unification so ground `BitVec 64` addresses never call `whnf`/`isDefEq` across
    -- unequal symbolic offsets, while rules written with a shared `p` still match canonical `gAddr`.
    let rGoalInst := (← instantiateMVars rGoal).consumeMData
    let mut gMatchTarget := gExpr
    let mut goalAddrTransport? : Option (Nat × Expr × Expr) := none
    if let some gSpec ← getAtomKeySpec reg gExpr then
      if let some gAIdx := gSpec.addrArgIdx then
        let rArgs := rGoalInst.getAppArgs
        let gArgs := gExpr.getAppArgs
        if atomHeadMatches gExpr rGoalInst gSpec && rArgs.size == gArgs.size && gAIdx < rArgs.size then
          let rAddr := rArgs[gAIdx]!
          let gAddr := gArgs[gAIdx]!
          if !rAddr.hasExprMVar && !gAddr.hasExprMVar && rAddr != gAddr then
            if let some hAddrEq ← tryFastAddrEq? ctx addrCache rAddr gAddr then
              gMatchTarget := mkAppN gExpr.getAppFn (gArgs.set! gAIdx rAddr)
              goalAddrTransport? := some (gAIdx, gAddr, hAddrEq)
            else
              restoreState saved
              continue
    unless ← isDefEq rGoalInst gMatchTarget do
      restoreState saved
      continue
    -- Classify remaining rule mvars: Prop mvars go to Q_addr / Q_pure; data mvars must be ground.
    let mut ok := true
    let mut newAddrs : Array (MVarId × Expr) := #[]
    let mut newPures : Array (MVarId × Expr) := #[]
    for mv in mvars do
      if ← mv.mvarId!.isAssigned then continue
      let mvTy ← instantiateMVars (← inferType mv)
      if ← isProp mvTy then
        if mvTy.isAppOfArity ``Eq 3 && (mvTy.getArg! 0).consumeMData.isAppOfArity ``BitVec 1 then
          let lhs := mvTy.getArg! 1
          let rhs := mvTy.getArg! 2
          if !lhs.hasExprMVar && !rhs.hasExprMVar then
            if let some pFast ← tryFastAddrEq? ctx addrCache lhs rhs then
              mv.mvarId!.assign pFast
              continue
            if ← isDefinitelyUnequalAddr ctx addrCache lhs rhs then
              ok := false
              break
          newAddrs := newAddrs.push (mv.mvarId!, mvTy)
        else
          newPures := newPures.push (mv.mvarId!, mvTy)
      else
        ok := false
        break
    unless ok do
      restoreState saved
      continue
    let rawPrf := mkAppN (mkConst rule.thmName us) mvars
    let stepPrf0 ←
      match rule.kind with
      | .eqSplit =>
        let rFull ← instantiateMVars (concl.getArg! 2)
        pure (mkApp3 (mkConst ``Arm64.Entails.of_eq) hExpr rFull rawPrf)
      | _ => pure rawPrf
    let rGoalOut ← instantiateMVars rGoal
    let (stepPrf, gOut) ←
      match goalAddrTransport? with
      | none => pure (stepPrf0, rGoalOut)
      | some (gAIdx, gAddr, hAddrEq) =>
        let rArgsOut := rGoalOut.getAppArgs
        let gArgsOut := rArgsOut.set! gAIdx gAddr
        let gOut := mkAppN rGoalOut.getAppFn gArgsOut
        let mut argEqs : Array (Option Expr) := Array.replicate rArgsOut.size none
        argEqs := argEqs.set! gAIdx (some hAddrEq)
        let some hGoalCongr ← buildAppCongrEq rGoalOut.getAppFn rArgsOut gArgsOut argEqs
          | pure (stepPrf0, rGoalOut)
        match rRest? with
        | none =>
          let transported := mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right)
            #[hExpr, rGoalOut, gOut, stepPrf0, hGoalCongr]
          pure (transported, gOut)
        | some restE =>
          let restOut ← instantiateMVars restE
          let oldRhs := mkApp2 (mkConst ``Arm64.SepProp.sepConj) rGoalOut restOut
          let newRhs := mkApp2 (mkConst ``Arm64.SepProp.sepConj) gOut restOut
          let hPairCongr ← mkCongrFun (← mkCongrArg (mkConst ``Arm64.SepProp.sepConj) hGoalCongr) restOut
          let transported := mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right)
            #[hExpr, oldRhs, newRhs, stepPrf0, hPairCongr]
          pure (transported, gOut)
    let residuals ← match rRest? with
      | none => pure #[]
      | some restE => flattenSpatialAtoms (← instantiateMVars restE)
    for a in newAddrs do addrQueue.modify (·.push a)
    for p in newPures do pureQueue.modify (·.push p)
    return some (stepPrf, gOut, residuals)
  return none

/-- Convert a single physical atom (`↦₈..↦₁₂₈`, `↦ₛ`, `↦₆₄*`, `memRegion`) into
    `(baseAddr, byteLenExpr, prf : atom ⊢ memRegion baseAddr byteLenExpr)` for Phase 3 multi-atom
    `memRegion` covering. -/
def weakenAtomToMemRegion? (atom0 : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let atom := (← instantiateMVars atom0).consumeMData
  let args := atom.getAppArgs
  match atom.getAppFn.constName? with
  | some ``Arm64.memRegion =>
    if args.size == 2 then
      return some (args[0]!, args[1]!, mkApp (mkConst ``Arm64.Entails.refl) atom)
    return none
  | some ``Arm64.pointsTo8 =>
    if args.size == 2 then
      let len := toExpr (1 : Nat)
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.pointsTo8_entails_memRegion) args[0]! args[1]!)
    return none
  | some ``Arm64.pointsTo16 =>
    if args.size == 2 then
      let len := toExpr (2 : Nat)
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.pointsTo16_entails_memRegion) args[0]! args[1]!)
    return none
  | some ``Arm64.pointsTo32 =>
    if args.size == 2 then
      let len := toExpr (4 : Nat)
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.pointsTo32_entails_memRegion) args[0]! args[1]!)
    return none
  | some ``Arm64.pointsTo64 =>
    if args.size == 2 then
      let len := toExpr (8 : Nat)
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.pointsTo64_entails_memRegion) args[0]! args[1]!)
    return none
  | some ``Arm64.pointsTo128 =>
    if args.size == 2 then
      let len := toExpr (16 : Nat)
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.Sep.pointsTo128_entails_memRegion) args[0]! args[1]!)
    return none
  | some ``Arm64.pointsToBytes =>
    if args.size == 2 then
      let bs := args[1]!
      let bv8 := mkApp (mkConst ``BitVec) (mkRawNatLit 8)
      let len := mkApp2 (mkConst ``List.length [0]) bv8 bs
      return some (args[0]!, len, mkApp2 (mkConst ``ProofLib.pointsToBytes_entails_memRegion) args[0]! bs)
    return none
  | some ``Arm64.pointsToWords64 =>
    if args.size == 2 then
      let ws := args[1]!
      let bv64 := mkApp (mkConst ``BitVec) (mkRawNatLit 64)
      let wLen := mkApp2 (mkConst ``List.length [0]) bv64 ws
      let len := mkApp2 (mkConst ``Nat.mul) (toExpr (8 : Nat)) wLen
      let prf := mkAppN (mkConst ``ProofLib.Sep.biabd_pointsToWords64_memRegion)
        #[args[0]!, args[0]!, ws, len, ← mkEqRefl args[0]!, ← mkEqRefl len]
      return some (args[0]!, len, prf)
    return none
  | _ => return none

/-- Coalesce group describing a many-to-1 spatial step `(A₀ ∗ (A₁ ∗ ...)) ⊢ Gⱼ` applied in
    Phase 4 after the single `SepSolver.eqAC` alignment. -/
structure CoalesceGroup where
  goalIdx     : Nat
  poolIndices : Array Nat
  groupedExpr : Expr
  targetExpr  : Expr
  entailsPrf  : Expr

/-- Try to cover an unmatched `memRegion gBase gLen` goal using 2+ contiguous physical atoms at the
    same canonical base root, simultaneously leaving non-participating atoms free for `?Frame`. -/
partial def tryMultiAtomMemRegionCover? (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (pool : Array PoolAtom) (gIdx : Nat) (gAtom : Expr)
    (pureQueue : IO.Ref (Array (MVarId × Expr))) :
    TacticM (Option CoalesceGroup) := do
  let gAtom := (← instantiateMVars gAtom).consumeMData
  unless gAtom.isAppOfArity ``Arm64.memRegion 2 do return none
  let gBase := gAtom.getArg! 0
  let gLen := gAtom.getArg! 1
  if gBase.hasExprMVar || gLen.hasExprMVar then return none
  let gRoot := peelSymbolicBase ctx gBase
  let mut cands : Array (Nat × Expr × Expr × Expr × Expr) := #[]
  for i in [:pool.size] do
    if !pool[i]!.alive then continue
    let pExpr := (← instantiateMVars pool[i]!.expr).consumeMData
    if let some (aBase, aLen, aPrf) ← weakenAtomToMemRegion? pExpr then
      if peelSymbolicBase ctx aBase == gRoot then
        cands := cands.push (i, pExpr, aBase, aLen, aPrf)
  if cands.size < 2 then return none
  let some (pickedIdxs, groupedE, coverPrf) ← buildChain gBase gLen cands #[] | return none
  if pickedIdxs.size < 2 then return none
  return some {
    goalIdx     := gIdx
    poolIndices := pickedIdxs
    groupedExpr := groupedE
    targetExpr  := gAtom
    entailsPrf  := coverPrf
  }
where
  buildChain (curBase remLen : Expr)
      (cands : Array (Nat × Expr × Expr × Expr × Expr))
      (used : Array Nat) : TacticM (Option (Array Nat × Expr × Expr)) := do
    let mut hit? : Option (Nat × Expr × Expr × Expr × Expr × Expr) := none
    for (pIdx, pExpr, aBase, aLen, aPrf) in cands do
      if used.contains pIdx then continue
      if let some hAddr ← proveAddrEqFull? ctx addrCache aBase curBase then
        hit? := some (pIdx, pExpr, aBase, aLen, aPrf, hAddr)
        break
    let some (pIdx, pExpr, aBase, aLen, aPrf, hAddr) := hit? | return none
    let stepPrf1 ←
      if aBase == curBase then pure aPrf
      else
        let mrOld := mkApp2 (mkConst ``Arm64.memRegion) aBase aLen
        let mrCur := mkApp2 (mkConst ``Arm64.memRegion) curBase aLen
        let hCongr ← mkCongrFun (← mkCongrArg (mkConst ``Arm64.memRegion) hAddr) aLen
        pure (mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right) #[pExpr, mrOld, mrCur, aPrf, hCongr])
    let eqLenTy ← mkEq aLen remLen
    if used.size ≥ 1 then
      let omegaTacs ← ProofLib.omegaDefaultTacs
      if let some hLen ← ProofLib.proveOmegaBoundedTerm? eqLenTy omegaTacs then
        let mrCur := mkApp2 (mkConst ``Arm64.memRegion) curBase aLen
        let mrGoal := mkApp2 (mkConst ``Arm64.memRegion) curBase remLen
        let hCongr ← mkCongrArg (mkApp (mkConst ``Arm64.memRegion) curBase) hLen
        let finalPrf := mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right)
          #[pExpr, mrCur, mrGoal, stepPrf1, hCongr]
        return some (used.push pIdx, pExpr, finalPrf)
      let saved ← saveState
      let gLenM ← mkFreshExprMVar eqLenTy
      let tacLen ← `(tactic| (
        try simp only [_root_.List.length_take, _root_.List.length_drop, _root_.List.length_append,
          _root_.List.length_replicate, _root_.ProofLib.ByteSlice.write8_length,
          _root_.ProofLib.ByteSlice.write64_length] at *
        omega))
      if (← runSilentTacticProbe gLenM.mvarId! tacLen).isSome then
        let hLen ← instantiateMVars gLenM
        let mrCur := mkApp2 (mkConst ``Arm64.memRegion) curBase aLen
        let mrGoal := mkApp2 (mkConst ``Arm64.memRegion) curBase remLen
        let hCongr ← mkCongrArg (mkApp (mkConst ``Arm64.memRegion) curBase) hLen
        let finalPrf := mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right)
          #[pExpr, mrCur, mrGoal, stepPrf1, hCongr]
        return some (used.push pIdx, pExpr, finalPrf)
      else
        restoreState saved
    let offBv := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 64) aLen
    let nextBase ← mkAdd curBase offBv
    let nextRem := mkApp2 (mkConst ``Nat.sub) remLen aLen
    let some (allIdxs, tailExpr, tailPrf) ← buildChain nextBase nextRem cands (used.push pIdx)
      | return none
    let hnTy ← mkEq (mkApp2 (mkConst ``Nat.add) aLen nextRem) remLen
    let hnM ← mkFreshExprMVar hnTy
    pureQueue.modify (·.push (hnM.mvarId!, hnTy))
    let hlePrf ← do
      if let some nVal ← evalClosedNat? remLen then
        if nVal ≤ (1 <<< 64) then
          pure (mkApp2 (mkConst ``ProofLib.Sep.le_two_pow_64_of_ble) remLen rflTrueExpr)
        else
          let twoPow64 : Expr := toExpr ((2 : Nat) ^ 64)
          let hleTy ← mkAppM ``LE.le #[remLen, twoPow64]
          let hleM ← mkFreshExprMVar hleTy
          pureQueue.modify (·.push (hleM.mvarId!, hleTy))
          pure hleM
      else
        let twoPow64 : Expr := toExpr ((2 : Nat) ^ 64)
        let hleTy ← mkAppM ``LE.le #[remLen, twoPow64]
        let hleM ← mkFreshExprMVar hleTy
        pureQueue.modify (·.push (hleM.mvarId!, hleTy))
        pure hleM
    let hbPrf ← mkEqRefl nextBase
    let combExpr := mkApp2 (mkConst ``Arm64.SepProp.sepConj) pExpr tailExpr
    let combPrf := mkAppN (mkConst ``ProofLib.Sep.biabd_entails_memRegion_cons)
      #[pExpr, tailExpr, curBase, nextBase, aLen, nextRem, remLen,
        stepPrf1, hbPrf, hnM, hlePrf, tailPrf]
    return some (allIdxs, combExpr, combPrf)

/-- Try to coalesce 2+ contiguous `↦ₛ` / `↦₈` atoms at the same canonical base root into a single
    `gBase ↦ₛ gBs` goal. -/
partial def tryCoalesceBytesSlices? (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (pool : Array PoolAtom) (gIdx : Nat) (gAtom : Expr)
    (pureQueue : IO.Ref (Array (MVarId × Expr))) :
    TacticM (Option CoalesceGroup) := do
  let gAtom := (← instantiateMVars gAtom).consumeMData
  unless gAtom.isAppOfArity ``Arm64.pointsToBytes 2 do return none
  let gBase := gAtom.getArg! 0
  let gBs := gAtom.getArg! 1
  if gBase.hasExprMVar then return none
  let gRoot := peelSymbolicBase ctx gBase
  let mut cands : Array (Nat × Expr × Expr × Expr × Option Expr) := #[]
  let bv8 := mkApp (mkConst ``BitVec) (mkRawNatLit 8)
  for i in [:pool.size] do
    if !pool[i]!.alive then continue
    let e := (← instantiateMVars pool[i]!.expr).consumeMData
    if e.isAppOfArity ``Arm64.pointsToBytes 2 then
      let a := e.getArg! 0
      if peelSymbolicBase ctx a == gRoot then
        cands := cands.push (i, e, a, e.getArg! 1, none)
    else if e.isAppOfArity ``Arm64.pointsTo8 2 then
      let a := e.getArg! 0
      let v := e.getArg! 1
      if peelSymbolicBase ctx a == gRoot then
        let sing := mkApp3 (mkConst ``List.cons [0]) bv8 v (mkApp (mkConst ``List.nil [0]) bv8)
        let conv := mkApp2 (mkConst ``ProofLib.Sep.pointsTo8_to_bytes) a v
        cands := cands.push (i, e, a, sing, some conv)
  if cands.size < 2 then return none
  let mut start? : Option (Nat × Expr × Expr × Expr × Option Expr × Expr) := none
  for (pIdx, pExpr, a, bs, conv?) in cands do
    if let some hAddr ← proveAddrEqFull? ctx addrCache a gBase then
      start? := some (pIdx, pExpr, a, bs, conv?, hAddr)
      break
  let some (idx0, expr0, a0, bs0, conv0?, hAddr0) := start? | return none
  let target0 := mkApp2 (mkConst ``Arm64.pointsToBytes) gBase bs0
  let mut accPrf : Expr ← do
    let p0 ← match conv0? with
      | some c => pure c
      | none   => pure (mkApp (mkConst ``Arm64.Entails.refl) expr0)
    if a0 == gBase then pure p0
    else
      let src0 := mkApp2 (mkConst ``Arm64.pointsToBytes) a0 bs0
      let hCongr ← mkCongrFun (← mkCongrArg (mkConst ``Arm64.pointsToBytes) hAddr0) bs0
      pure (mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right) #[expr0, src0, target0, p0, hCongr])
  let mut accExpr := expr0
  let mut accBs := bs0
  let mut used : Array Nat := #[idx0]
  let mut progress := true
  while progress do
    progress := false
    let accLen := mkApp2 (mkConst ``List.length [0]) bv8 accBs
    let expNextAddr ← mkAdd gBase (mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 64) accLen)
    for (pIdx, pExpr, aNext, bsNext, convNext?) in cands do
      if used.contains pIdx then continue
      if let some hNext ← proveAddrEqFull? ctx addrCache expNextAddr aNext then
        let stepNextPrf := match convNext? with
          | some c => c
          | none   => mkApp (mkConst ``Arm64.Entails.refl) pExpr
        let pairIn := mkApp2 (mkConst ``Arm64.SepProp.sepConj) accExpr pExpr
        let midL := mkApp2 (mkConst ``Arm64.pointsToBytes) gBase accBs
        let midR := mkApp2 (mkConst ``Arm64.pointsToBytes) aNext bsNext
        let pairMid := mkApp2 (mkConst ``Arm64.SepProp.sepConj) midL midR
        let monoPrf := mkAppN (mkConst ``Arm64.sepConj_mono) #[accExpr, midL, pExpr, midR, accPrf, stepNextPrf]
        let coalPrf := mkAppN (mkConst ``ProofLib.Sep.pointsToBytes_coalesce2) #[gBase, aNext, accBs, bsNext, hNext]
        let newBs ← mkAppM ``HAppend.hAppend #[accBs, bsNext]
        let outSlice := mkApp2 (mkConst ``Arm64.pointsToBytes) gBase newBs
        accPrf := mkAppN (mkConst ``Arm64.Entails.trans) #[pairIn, pairMid, outSlice, monoPrf, coalPrf]
        accExpr := pairIn
        accBs := newBs
        used := used.push pIdx
        progress := true
        break
  if used.size < 2 then return none
  let gBsInst ← instantiateMVars gBs
  let finalPrf ←
    if ← withReducible (isDefEq accBs gBsInst) then
      pure accPrf
    else if (accBs.hasExprMVar || gBsInst.hasExprMVar) && (← isDefEq accBs gBsInst) then
      pure accPrf
    else
      let eqBsTy ← mkEq accBs gBsInst
      let hBs ← mkFreshExprMVar eqBsTy
      pureQueue.modify (·.push (hBs.mvarId!, eqBsTy))
      let curSlice := mkApp2 (mkConst ``Arm64.pointsToBytes) gBase accBs
      let goalSlice := mkApp2 (mkConst ``Arm64.pointsToBytes) gBase gBsInst
      let hCongr ← mkCongrArg (mkApp (mkConst ``Arm64.pointsToBytes) gBase) hBs
      pure (mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right) #[accExpr, curSlice, goalSlice, accPrf, hCongr])
  let gFinal ← instantiateMVars gAtom
  return some {
    goalIdx     := gIdx
    poolIndices := used
    groupedExpr := accExpr
    targetExpr  := gFinal
    entailsPrf  := finalPrf
  }

/-! ### Per-Origin Derivation Tree (1-to-1 & Carves) + Single-AC Spine Builder -/

/-- Tree recording how an initial LHS leaf atom was rewritten/carved in place before the single
    `SepSolver.eqAC` permutation. -/
inductive OriginPlan where
  | leaf (poolIdx : Nat)
  | step (src dst : Expr) (stepPrf : Expr) (children : Array OriginPlan)
  deriving Inhabited

/-- Materialize `(outExpr, prf : origExpr ⊢ outExpr)` for an `OriginPlan` node given final pool. -/
partial def evalOriginPlan (pool : Array PoolAtom) (origExpr : Expr) :
    OriginPlan → MetaM (Expr × Expr)
  | .leaf pIdx => do
    let e := (← instantiateMVars pool[pIdx]!.expr).consumeMData
    return (e, mkApp (mkConst ``Arm64.Entails.refl) e)
  | .step _ dst stepPrf children => do
    if children.isEmpty then
      let dst' := (← instantiateMVars dst).consumeMData
      return (dst', stepPrf)
    let childResults ← children.mapM fun
      | .leaf pIdx => do
        let e := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        pure (e, e, mkApp (mkConst ``Arm64.Entails.refl) e)
      | ch@(.step subSrc _ _ _) => do
        let (outE, p) ← evalOriginPlan pool subSrc ch
        pure ((← instantiateMVars subSrc).consumeMData, outE, p)
    let (midChain, outChain, monoPrf) ← buildRightChainMono childResults 0
    if midChain == outChain then
      return (outChain, stepPrf)
    let fullPrf := mkAppN (mkConst ``Arm64.Entails.trans) #[origExpr, midChain, outChain, stepPrf, monoPrf]
    return (outChain, fullPrf)
where
  buildRightChainMono (items : Array (Expr × Expr × Expr)) (idx : Nat) :
      MetaM (Expr × Expr × Expr) := do
    let (s, o, p) := items[idx]!
    if idx + 1 >= items.size then
      return (s, o, p)
    let (sRest, oRest, pRest) ← buildRightChainMono items (idx + 1)
    let sAll := mkApp2 (mkConst ``Arm64.SepProp.sepConj) s sRest
    let oAll := mkApp2 (mkConst ``Arm64.SepProp.sepConj) o oRest
    if s == o && sRest == oRest then
      return (sAll, oAll, mkApp (mkConst ``Arm64.Entails.refl) sAll)
    let pm := mkAppN (mkConst ``Arm64.sepConj_mono) #[s, o, sRest, oRest, p, pRest]
    return (sAll, oAll, pm)

/-- Walk a clean spatial LHS expression `P_spatial` along its original `∗`-tree structure,
    evaluating each leaf's `OriginPlan` to build `(P_mid, prf : P_spatial ⊢ P_mid)` with zero AC. -/
partial def buildLHSMonoFromPlans (pool : Array PoolAtom)
    (plans : Array OriginPlan) (cursor : IO.Ref Nat) (e0 : Expr) : MetaM (Expr × Expr) := do
  let e := (← instantiateMVars e0).consumeMData.headBeta
  if e.isConstOf ``Arm64.SepProp.emp then
    return (e, mkApp (mkConst ``Arm64.Entails.refl) e)
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let (lOut, lPrf) ← buildLHSMonoFromPlans pool plans cursor (e.getArg! 0)
    let (rOut, rPrf) ← buildLHSMonoFromPlans pool plans cursor (e.getArg! 1)
    let lIn := (← instantiateMVars (e.getArg! 0)).consumeMData
    let rIn := (← instantiateMVars (e.getArg! 1)).consumeMData
    let outE := mkApp2 (mkConst ``Arm64.SepProp.sepConj) lOut rOut
    if lIn == lOut && rIn == rOut then
      return (outE, mkApp (mkConst ``Arm64.Entails.refl) outE)
    return (outE, mkAppN (mkConst ``Arm64.sepConj_mono) #[lIn, lOut, rIn, rOut, lPrf, rPrf])
  let idx ← cursor.get
  cursor.set (idx + 1)
  evalOriginPlan pool e plans[idx]!

/-- Walk `Q_spatial` along its exact `∗`-tree structure, replacing any leaf at `goalIdx` that has a
    `CoalesceGroup` with `(groupedExpr, entailsPrf)` to produce `(P_grouped, P_grouped ⊢ Q_spatial)`
    with zero extra AC calls. -/
partial def buildRHSGroupedMono (coalMap : Std.HashMap Nat CoalesceGroup)
    (frameMVar? : Option MVarId) (cursor : IO.Ref Nat) (e0 : Expr) : MetaM (Expr × Expr) := do
  let e := (← instantiateMVars e0).consumeMData.headBeta
  if e.isConstOf ``Arm64.SepProp.emp then
    return (e, mkApp (mkConst ``Arm64.Entails.refl) e)
  if let .mvar mv := e0.consumeMData then
    if frameMVar? == some mv then
      return (e, mkApp (mkConst ``Arm64.Entails.refl) e)
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let (lGrp, lPrf) ← buildRHSGroupedMono coalMap frameMVar? cursor (e0.consumeMData.getArg! 0)
    let (rGrp, rPrf) ← buildRHSGroupedMono coalMap frameMVar? cursor (e0.consumeMData.getArg! 1)
    let lTgt := (← instantiateMVars (e.getArg! 0)).consumeMData
    let rTgt := (← instantiateMVars (e.getArg! 1)).consumeMData
    let grpE := mkApp2 (mkConst ``Arm64.SepProp.sepConj) lGrp rGrp
    let tgtE := mkApp2 (mkConst ``Arm64.SepProp.sepConj) lTgt rTgt
    if lGrp == lTgt && rGrp == rTgt then
      return (grpE, mkApp (mkConst ``Arm64.Entails.refl) tgtE)
    return (grpE, mkAppN (mkConst ``Arm64.sepConj_mono) #[lGrp, lTgt, rGrp, rTgt, lPrf, rPrf])
  let gIdx ← cursor.get
  cursor.set (gIdx + 1)
  if let some cg := coalMap[gIdx]? then
    return (cg.groupedExpr, cg.entailsPrf)
  return (e, mkApp (mkConst ``Arm64.Entails.refl) e)

/-- Replace leaf `targetPoolIdx` inside an `OriginPlan` tree with a new `.step` node. -/
partial def recordPlanStep (targetPoolIdx : Nat) (newNode : OriginPlan) :
    OriginPlan → OriginPlan
  | .leaf pIdx => if pIdx == targetPoolIdx then newNode else .leaf pIdx
  | .step s d p chs => .step s d p (chs.map (recordPlanStep targetPoolIdx newNode))

/-- Flatten `Q_spatial` into `(rhsGoals, frameMVar?)` while preserving left-to-right leaf order. -/
partial def extractRHSGoalsAndFrame (e0 : Expr) : MetaM (Array Expr × Option MVarId) := do
  let raw ← goRaw e0
  let mut goals : Array Expr := #[]
  let mut frame? : Option MVarId := none
  for item in raw do
    let inst := (← instantiateMVars item).consumeMData
    if let .mvar mv := inst then
      let ty := (← instantiateMVars (← inferType inst)).consumeMData
      if ty.isConstOf ``Arm64.SepProp && frame?.isNone then
        frame? := some mv
      else
        goals := goals.push inst
    else
      goals := goals.push inst
  return (goals, frame?)
where
  goRaw (e0 : Expr) : MetaM (Array Expr) := do
    let e := (← instantiateMVars e0).consumeMData.headBeta
    if e.isConstOf ``Arm64.SepProp.emp then return #[]
    if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      return (← goRaw (e.getArg! 0)) ++ (← goRaw (e.getArg! 1))
    return #[e]

/-- Phases 2, 3, and 4 over clean spatial `P_spatial ⊢ Q_spatial`:
    - Phase 2: Root-bucketed Key-First worklist + unique root-and-head symbolic address deferral +
      unique MVar-key instantiation.
    - Phase 3: `DiscrTree` `BiAbd` subsumption/carve rules + multi-atom `memRegion` cover +
      multi-piece `ByteSlice` coalescing + `?Frame` inference.
    - Phase 4: Single-certificate spine assembly (`SepSolver.eqAC` called at most once). -/
def solveSpatialBiAbd (tacName : String) (reg : BiAbdRegistry) (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (addrQueue : IO.Ref (Array (MVarId × Expr)))
    (pureQueue : IO.Ref (Array (MVarId × Expr)))
    (P_spatial Q_spatial : Expr) : TacticM Expr := do
  let lhsInit ← flattenSpatialAtoms P_spatial
  let (rhsGoalsInit, frameMVar?) ← extractRHSGoalsAndFrame Q_spatial
  let mut pool : Array PoolAtom := lhsInit.map fun e => { expr := e, alive := true }
  let mut plans : Array OriginPlan := (List.range lhsInit.size).toArray.map OriginPlan.leaf
  let mut goalMatched : Array Bool := Array.replicate rhsGoalsInit.size false
  let mut coalMap : Std.HashMap Nat CoalesceGroup := {}

  let apply1To1Eq (pool : Array PoolAtom) (plans : Array OriginPlan)
      (pIdx : Nat) (hCur gFinal : Expr) (heqOpt : Option Expr) :
      Array PoolAtom × Array OriginPlan := Id.run do
    match heqOpt with
    | none =>
      let pool' := pool.set! pIdx { expr := gFinal, alive := false }
      (pool', plans)
    | some heq =>
      let newIdx := pool.size
      let pool' := (pool.set! pIdx { pool[pIdx]! with alive := false }).push { expr := gFinal, alive := false }
      let stepPrf := mkApp3 (mkConst ``Arm64.Entails.of_eq) hCur gFinal heq
      let node := OriginPlan.step hCur gFinal stepPrf #[.leaf newIdx]
      let plans' := plans.map (recordPlanStep pIdx node)
      (pool', plans')

  let mut progress := true
  while progress do
    progress := false

    -- Pass 2.1: Ground-Key Exact / Canonical-Address Match (keys matched BEFORE payloads).
    for gIdx in [:rhsGoalsInit.size] do
      if goalMatched[gIdx]! then continue
      let gAtom := (← instantiateMVars rhsGoalsInit[gIdx]!).consumeMData
      let some gSpec ← getAtomKeySpec reg gAtom | continue
      let gArgs := gAtom.getAppArgs
      if gSpec.keyArgIndices.any (fun k => k < gArgs.size && gArgs[k]!.hasExprMVar) then
        continue
      let gRoot? := match gSpec.addrArgIdx with
        | some aIdx => if aIdx < gArgs.size then some (peelSymbolicBase ctx gArgs[aIdx]!) else none
        | none => none
      let allowRangeEq ← do
        if !isVariableRangeHead gSpec.headName then pure true
        else match gSpec.addrArgIdx, gRoot? with
          | some aIdx, some gR =>
            let mut lCnt := 0
            for p in pool do
              if p.alive then
                let ha := (← instantiateMVars p.expr).consumeMData
                if atomHeadMatches gAtom ha gSpec && aIdx < ha.getAppArgs.size then
                  if peelSymbolicBase ctx ha.getAppArgs[aIdx]! == gR then lCnt := lCnt + 1
            let mut rCnt := 0
            for j in [:rhsGoalsInit.size] do
              if !goalMatched[j]! then
                let ga := (← instantiateMVars rhsGoalsInit[j]!).consumeMData
                if atomHeadMatches gAtom ga gSpec && aIdx < ga.getAppArgs.size then
                  if !(ga.getAppArgs[aIdx]!.hasExprMVar) then
                    if peelSymbolicBase ctx ga.getAppArgs[aIdx]! == gR then rCnt := rCnt + 1
            pure (lCnt == 1 && rCnt == 1)
          | _, _ => pure true
      for pIdx in [:pool.size] do
        if !pool[pIdx]!.alive then continue
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        unless atomHeadMatches gAtom hAtom gSpec do continue
        let hArgs := hAtom.getAppArgs
        if hArgs.size != gArgs.size then continue
        if let (some aIdx, some gR) := (gSpec.addrArgIdx, gRoot?) then
          if peelSymbolicBase ctx hArgs[aIdx]! != gR then continue
        let mut keyOk := true
        let mut keyEqs : Array (Option Expr) := Array.replicate hArgs.size none
        for kIdx in gSpec.keyArgIndices do
          if kIdx >= hArgs.size then keyOk := false; break
          let hk := hArgs[kIdx]!
          let gk := gArgs[kIdx]!
          if hk == gk then continue
          let kTy := (← inferType hk).consumeMData
          let isBvKey ←
            if kTy.isAppOfArity ``BitVec 1 then pure true
            else pure ((← withReducible (whnf kTy)).isAppOfArity ``BitVec 1)
          if isBvKey then
            if let some pEq ← tryFastAddrEq? ctx addrCache hk gk then
              keyEqs := keyEqs.set! kIdx (some pEq)
            else
              keyOk := false; break
          else if ← withReducible (isDefEq hk gk) then
            continue
          else
            keyOk := false; break
        unless keyOk do continue
        let some (newArgs, payEqs) ← unifyPayloadsAfterKeyMatch gSpec.keyArgIndices allowRangeEq hArgs gArgs pureQueue
          | continue
        let mut mergedEqs : Array (Option Expr) := Array.replicate hArgs.size none
        let mut finalArgs := newArgs
        for idx in [:hArgs.size] do
          if let some ke := keyEqs[idx]! then
            mergedEqs := mergedEqs.set! idx (some ke)
            finalArgs := finalArgs.set! idx (← instantiateMVars gArgs[idx]!)
          else if let some pe := payEqs[idx]! then
            mergedEqs := mergedEqs.set! idx (some pe)
        let heqOpt ← buildAppCongrEq hAtom.getAppFn hArgs finalArgs mergedEqs
        let gFinal := (← instantiateMVars gAtom).consumeMData
        let (pool', plans') := apply1To1Eq pool plans pIdx hAtom gFinal heqOpt
        pool := pool'
        plans := plans'
        goalMatched := goalMatched.set! gIdx true
        progress := true
        break

    if progress then continue

    -- Pass 2.1': Unique Root-and-Head Symbolic Address Deferral into `Q_addr`.
    for gIdx in [:rhsGoalsInit.size] do
      if goalMatched[gIdx]! then continue
      let gAtom := (← instantiateMVars rhsGoalsInit[gIdx]!).consumeMData
      let some gSpec ← getAtomKeySpec reg gAtom | continue
      let some aIdx := gSpec.addrArgIdx | continue
      let gArgs := gAtom.getAppArgs
      if aIdx >= gArgs.size then continue
      if gSpec.keyArgIndices.any (fun k => k < gArgs.size && gArgs[k]!.hasExprMVar) then
        continue
      let gRoot := peelSymbolicBase ctx gArgs[aIdx]!
      let mut unmatchedSameRoot := 0
      for j in [:rhsGoalsInit.size] do
        if !goalMatched[j]! then
          let ga := (← instantiateMVars rhsGoalsInit[j]!).consumeMData
          if atomHeadMatches gAtom ga gSpec && aIdx < ga.getAppArgs.size then
            if !(ga.getAppArgs[aIdx]!.hasExprMVar) then
              if peelSymbolicBase ctx ga.getAppArgs[aIdx]! == gRoot then
                unmatchedSameRoot := unmatchedSameRoot + 1
      let mut rootCands : Array Nat := #[]
      for pIdx in [:pool.size] do
        if !pool[pIdx]!.alive then continue
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        unless atomHeadMatches gAtom hAtom gSpec do continue
        let hArgs := hAtom.getAppArgs
        if hArgs.size != gArgs.size then continue
        if peelSymbolicBase ctx hArgs[aIdx]! != gRoot then continue
        let mut nonAddrOk := true
        for kIdx in gSpec.keyArgIndices do
          if kIdx == aIdx then continue
          unless ← withReducible (isDefEq hArgs[kIdx]! gArgs[kIdx]!) do
            nonAddrOk := false; break
        if nonAddrOk then rootCands := rootCands.push pIdx
      if rootCands.size == 1 && (!isVariableRangeHead gSpec.headName || unmatchedSameRoot == 1) then
        let pIdx := rootCands[0]!
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        let hArgs := hAtom.getAppArgs
        if ← isDefinitelyUnequalAddr ctx addrCache hArgs[aIdx]! gArgs[aIdx]! then
          continue
        let some (newArgs, payEqs) ← unifyPayloadsAfterKeyMatch gSpec.keyArgIndices true hArgs gArgs pureQueue
          | continue
        let hk := hArgs[aIdx]!
        let gk ← instantiateMVars gArgs[aIdx]!
        let addrEqTy ← mkEq hk gk
        let addrMVar ← mkFreshExprMVar addrEqTy
        addrQueue.modify (·.push (addrMVar.mvarId!, addrEqTy))
        let mergedEqs := payEqs.set! aIdx (some addrMVar)
        let finalArgs := newArgs.set! aIdx gk
        let heqOpt ← buildAppCongrEq hAtom.getAppFn hArgs finalArgs mergedEqs
        let gFinal := (← instantiateMVars gAtom).consumeMData
        let (pool', plans') := apply1To1Eq pool plans pIdx hAtom gFinal heqOpt
        pool := pool'
        plans := plans'
        goalMatched := goalMatched.set! gIdx true
        progress := true
        break

    if progress then continue

    -- Pass 2.2: Unique Head MVar-Key Instantiation (cascading grounded keys to remaining goals).
    for gIdx in [:rhsGoalsInit.size] do
      if goalMatched[gIdx]! then continue
      let gAtom := (← instantiateMVars rhsGoalsInit[gIdx]!).consumeMData
      let some gSpec ← getAtomKeySpec reg gAtom | continue
      let gArgs := gAtom.getAppArgs
      if !gSpec.keyArgIndices.any (fun k => k < gArgs.size && gArgs[k]!.hasExprMVar) then
        continue
      let mut headCands : Array Nat := #[]
      for pIdx in [:pool.size] do
        if !pool[pIdx]!.alive then continue
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        if atomHeadMatches gAtom hAtom gSpec && hAtom.getAppArgs.size == gArgs.size then
          let hArgs := hAtom.getAppArgs
          let mut groundKeysCompatible := true
          for kIdx in gSpec.keyArgIndices do
            if kIdx < gArgs.size && !gArgs[kIdx]!.hasExprMVar && !hArgs[kIdx]!.hasExprMVar then
              if ← isBV64Expr hArgs[kIdx]! then
                if (← tryFastAddrEq? ctx addrCache hArgs[kIdx]! gArgs[kIdx]!).isNone then
                  groundKeysCompatible := false; break
              else unless ← withReducible (isDefEq hArgs[kIdx]! gArgs[kIdx]!) do
                groundKeysCompatible := false; break
          if groundKeysCompatible then
            headCands := headCands.push pIdx
      if headCands.size == 1 then
        let pIdx := headCands[0]!
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        if ← isDefEq hAtom gAtom then
          let gFinal := (← instantiateMVars gAtom).consumeMData
          pool := pool.set! pIdx { expr := gFinal, alive := false }
          goalMatched := goalMatched.set! gIdx true
          progress := true
          break

    if progress then continue

    -- Pass 3a: `DiscrTree` Bi-Abductive Carve & Subsumption Rules (`H ⊢ G`, `H ⊢ G ∗ Rest`).
    for gIdx in [:rhsGoalsInit.size] do
      if goalMatched[gIdx]! then continue
      let gAtom := (← instantiateMVars rhsGoalsInit[gIdx]!).consumeMData
      let some gSpec ← getAtomKeySpec reg gAtom | continue
      let gArgs := gAtom.getAppArgs
      let gRoot? := match gSpec.addrArgIdx with
        | some aIdx =>
          if aIdx < gArgs.size && !gArgs[aIdx]!.hasExprMVar then
            some (peelSymbolicBase ctx gArgs[aIdx]!)
          else
            none
        | none => none
      let isMemRegGoal := gAtom.isAppOfArity ``Arm64.memRegion 2
      let mut matchedRule := false
      for pIdx in [:pool.size] do
        if !pool[pIdx]!.alive then continue
        let hAtom := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        if let (some hSpec, some gR) := (← getAtomKeySpec reg hAtom, gRoot?) then
          if let some haIdx := hSpec.addrArgIdx then
            let hArgs := hAtom.getAppArgs
            if haIdx < hArgs.size && !hArgs[haIdx]!.hasExprMVar then
              if peelSymbolicBase ctx hArgs[haIdx]! != gR then continue
        if isMemRegGoal && !hAtom.isAppOfArity ``Arm64.memRegion 2 then
          if let some (aBase, aLen, _) ← weakenAtomToMemRegion? hAtom then
            let gBase := gAtom.getArg! 0
            let gLen := gAtom.getArg! 1
            if (← proveAddrEqFull? ctx addrCache aBase gBase).isNone then continue
            let lenEq ← mkEq aLen gLen
            let savedL ← saveState
            let gLM ← mkFreshExprMVar lenEq
            let tacL ← `(tactic| (
              try simp only [_root_.List.length_take, _root_.List.length_drop,
                _root_.List.length_append, _root_.List.length_replicate,
                _root_.ProofLib.ByteSlice.write8_length,
                _root_.ProofLib.ByteSlice.write64_length] at *
              omega))
            let lenOk := (← runSilentTacticProbe gLM.mvarId! tacL).isSome
            restoreState savedL
            if !lenOk then continue
        if let some (stepPrf, gOut, residuals) ←
            tryApplyDiscrTreeRule? reg ctx addrCache addrQueue pureQueue hAtom gAtom then
          let mainIdx := pool.size
          let mut pool' := (pool.set! pIdx { pool[pIdx]! with alive := false }).push
            { expr := gOut.consumeMData, alive := false }
          let mut childPlans : Array OriginPlan := #[.leaf mainIdx]
          for r in residuals do
            let rIdx := pool'.size
            pool' := pool'.push { expr := r.consumeMData, alive := true }
            childPlans := childPlans.push (.leaf rIdx)
          let allOut := mkSepChain (#[gOut] ++ residuals)
          let node := OriginPlan.step hAtom allOut stepPrf childPlans
          plans := plans.map (recordPlanStep pIdx node)
          pool := pool'
          goalMatched := goalMatched.set! gIdx true
          matchedRule := true
          progress := true
          break
      if matchedRule then break

  -- Pass 3b: Multi-atom `memRegion` Cover & Multi-piece `ByteSlice` Coalescing.
  for gIdx in [:rhsGoalsInit.size] do
    if goalMatched[gIdx]! then continue
    let gAtom := (← instantiateMVars rhsGoalsInit[gIdx]!).consumeMData
    if let some cg ← tryMultiAtomMemRegionCover? ctx addrCache pool gIdx gAtom pureQueue then
      for pIdx in cg.poolIndices do
        pool := pool.set! pIdx { pool[pIdx]! with alive := false }
      coalMap := coalMap.insert gIdx cg
      goalMatched := goalMatched.set! gIdx true
    else if let some cg ← tryCoalesceBytesSlices? ctx addrCache pool gIdx gAtom pureQueue then
      for pIdx in cg.poolIndices do
        pool := pool.set! pIdx { pool[pIdx]! with alive := false }
      coalMap := coalMap.insert gIdx cg
      goalMatched := goalMatched.set! gIdx true

  for gIdx in [:rhsGoalsInit.size] do
    if !goalMatched[gIdx]! then
      let gAtom ← instantiateMVars rhsGoalsInit[gIdx]!
      throwError "{tacName}: could not match spatial goal atom:{indentExpr gAtom}"

  let mut freeAtoms : Array Expr := #[]
  match frameMVar? with
  | some fmv =>
    for pIdx in [:pool.size] do
      if pool[pIdx]!.alive then
        let origE := (← instantiateMVars pool[pIdx]!.expr).consumeMData
        let unfoldedE := (← unfoldAddrLets origE).consumeMData
        if unfoldedE != origE then
          let (pool', plans') := apply1To1Eq pool plans pIdx origE unfoldedE (some (← mkEqRefl unfoldedE))
          pool := pool'
          plans := plans'
        else
          pool := pool.set! pIdx { expr := unfoldedE, alive := false }
        freeAtoms := freeAtoms.push unfoldedE
    fmv.assign (mkSepChain freeAtoms)
  | none =>
    for p in pool do
      if p.alive then
        freeAtoms := freeAtoms.push (← instantiateMVars p.expr)
    if !freeAtoms.isEmpty then
      throwError "{tacName}: linear `SepProp` has unmatched LHS spatial atoms and no `?Frame` metavariable:{indentExpr (mkSepChain freeAtoms)}"

  -- Phase 4: Single-Certificate Spine Assembly (`SepSolver.eqAC` called AT MOST ONCE).
  let lhsCursor ← IO.mkRef 0
  let (pMid, h1to1) ← buildLHSMonoFromPlans pool plans lhsCursor P_spatial
  let rhsCursor ← IO.mkRef 0
  let (pGrouped, hCoal) ← buildRHSGroupedMono coalMap frameMVar? rhsCursor Q_spatial
  let pSpatialInst := (← instantiateMVars P_spatial).consumeMData
  let qSpatialInst := (← instantiateMVars Q_spatial).consumeMData
  let hToGrouped ←
    if pMid == pGrouped then
      pure h1to1
    else
      let heqAC ← ProofLib.SepSolver.eqAC pMid pGrouped
      if pSpatialInst == pMid then
        pure (mkApp3 (mkConst ``Arm64.Entails.of_eq) pMid pGrouped heqAC)
      else
        pure (mkAppN (mkConst ``ProofLib.SepFrameInfer.entails_congr_right)
          #[pSpatialInst, pMid, pGrouped, h1to1, heqAC])
  if pGrouped == qSpatialInst then
    return hToGrouped
  else if pSpatialInst == pGrouped then
    return hCoal
  else
    return mkAppN (mkConst ``Arm64.Entails.trans) #[pSpatialInst, pGrouped, qSpatialInst, hToGrouped, hCoal]

/-! ### Phase 5: Scheduled Side-Condition Discharge -/

/-- Flatten any `∧`-conjuncts in `Q_pure` into individual atomic `MVarId` goals using `And.intro`
    so witness-grounding equations fire before sibling pure goals are checked. -/
partial def flattenPureGoalConjuncts (g : MVarId) : MetaM (Array (MVarId × Expr)) := do
  if ← g.isAssigned then return #[]
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  if ty.isAppOfArity ``And 2 then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let g1 ← mkFreshExprMVar a
    let g2 ← mkFreshExprMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b g1 g2)
    return (← flattenPureGoalConjuncts g1.mvarId!) ++ (← flattenPureGoalConjuncts g2.mvarId!)
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return #[]
  return #[(g, ty)]

/-- Targeted reducer for `ByteSlice.readLE`, `List.getD`, and `List.length` over nested
    `ByteSlice.write8` / `ByteSlice.write64` chains (discharging bounds/disjointness side goals
    via length-aware `omega`), used before MVar unification so `ByteSlice.readLE outBs off 8 = ?w`
    reduces to `val = ?w` and grounds `?w := val`. -/
def reduceByteSliceGoalIfPossible (g : MVarId) : TacticM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.find? (fun sub =>
    sub.isConstOf ``ProofLib.ByteSlice.write8 || sub.isConstOf ``ProofLib.ByteSlice.write16 ||
    sub.isConstOf ``ProofLib.ByteSlice.write32 || sub.isConstOf ``ProofLib.ByteSlice.write64 ||
    sub.isConstOf ``ProofLib.ByteSlice.readLE || sub.isConstOf ``List.getD ||
    sub.isConstOf ``List.length) |>.isSome do
    return g
  let tac ← `(tactic|
    simp (disch := (first
      | byte_region_len
      | (try simp only [
          _root_.List.length_take, _root_.List.length_drop,
          _root_.List.length_append, _root_.List.length_replicate
        ] at *; omega))) only [
      _root_.ProofLib.ByteSlice.write8_length, _root_.ProofLib.ByteSlice.write16_length,
      _root_.ProofLib.ByteSlice.write32_length, _root_.ProofLib.ByteSlice.write64_length,
      _root_.ProofLib.ByteSlice.readLE_write64_self,
      _root_.ProofLib.Sep.readLE_write64_of_disjoint,
      _root_.ProofLib.ByteSlice.readLE_write8_of_disjoint,
      _root_.ProofLib.Sep.getD_write8_self, _root_.ProofLib.Sep.getD_write8_ne,
      _root_.ProofLib.Sep.getD_write64_ne, _root_.ProofLib.Sep.write8_len_one
    ])
  if let some rem ← runSilentTacticProbe g tac (fun r => r.length ≤ 1) then
    if rem.isEmpty then return g
    return rem.head!
  return g

/-- Unfold top-level user helper `def`s (not `List.*` or `ProofLib.ByteSlice.*`) on the sides of a
    `List` equality so `List.append_assoc` normalizes both sides uniformly. -/
def unfoldUserListEqSides (g : MVarId) : MetaM MVarId := do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).isAppOfArity ``List 1 do
    return g
  let elemTy := ty.getArg! 0
  let unfoldSide (s : Expr) : MetaM Expr := do
    if let .const cName _ := s.getAppFn then
      if !(`List).isPrefixOf cName && !(`ProofLib.ByteSlice).isPrefixOf cName then
        if let some s' ← unfoldDefinition? s then
          return s'.headBeta
    return s
  let l' ← unfoldSide (ty.getArg! 1)
  let r' ← unfoldSide (ty.getArg! 2)
  if l' == ty.getArg! 1 && r' == ty.getArg! 2 then
    return g
  let newTy := mkApp3 (mkConst ``Eq [1]) elemTy l' r'
  if ← isDefEq ty newTy then
    let gNew ← mkFreshExprMVar newTy
    g.assign gNew
    return gNew.mvarId!
  return g

/-- Discharge a single ground pure obligation in Phase 5.3. -/
def dischargeSinglePureGoal (tacName : String) (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64)) (g0 : MVarId) : TacticM Unit := do
  if ← g0.isAssigned then return
  let g1 ← reduceByteSliceGoalIfPossible g0
  if ← g1.isAssigned then return
  let ty := (← instantiateMVars (← g1.getType)).consumeMData
  if ty.isAppOfArity ``Eq 3 then
    let lhs := ty.getArg! 1
    let rhs := ty.getArg! 2
    if ← withReducible (isDefEq lhs rhs) then
      let lhs' ← instantiateMVars lhs
      g1.assign (← mkEqRefl lhs')
      return
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← withReducible (isDefEq decl.type ty) then
      g1.assign decl.toExpr
      return
  if ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).consumeMData.isAppOfArity ``BitVec 1 then
    if let some prf ← proveAddrEqFull? ctx addrCache (ty.getArg! 1) (ty.getArg! 2) then
      g1.assign prf
      return
    if ← isDefinitelyUnequalAddr ctx addrCache (ty.getArg! 1) (ty.getArg! 2) then
      throwError "{tacName} (Phase 5): failed to discharge pure side condition:{indentExpr ty}"
  let omegaTacs ← ProofLib.omegaDefaultTacs
  if let some prf ← ProofLib.proveOmegaBoundedTerm? ty omegaTacs then
    g1.assign prf
    return
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if let some p ← findStructProjMatching? decl.toExpr decl.type ty 3 then
      g1.assign p
      return
  let g ← unfoldUserListEqSides g1
  let tac ← `(tactic| first
    | rfl
    | assumption
    | decide
    | omega
    | bv_omega
    | (simp (disch := (first
        | byte_region_len
        | (try simp only [
            _root_.List.length_take, _root_.List.length_drop,
            _root_.List.length_append, _root_.List.length_replicate
          ] at *; omega))) only [
        _root_.ProofLib.ByteSlice.write8_length, _root_.ProofLib.ByteSlice.write64_length,
        _root_.ProofLib.ByteSlice.readLE_write64_self,
        _root_.ProofLib.Sep.readLE_write64_of_disjoint,
        _root_.ProofLib.ByteSlice.readLE_write8_of_disjoint,
        _root_.ProofLib.Sep.getD_write8_self, _root_.ProofLib.Sep.getD_write8_ne,
        _root_.ProofLib.Sep.getD_write64_ne, _root_.ProofLib.Sep.write8_len_one,
        _root_.List.append_assoc, _root_.List.length_take,
        _root_.List.length_drop, _root_.List.length_replicate,
        _root_.List.length_append, _root_.List.drop_drop
      ]; try byte_region_len; try omega; try rfl)
    | (solve_by_elim (maxDepth := 4)))
  if (← runSilentTacticProbe g tac).isSome then return
  throwError "{tacName} (Phase 5): failed to discharge pure side condition:{indentExpr ty}"

/-- Phase 5: Scheduled Side-Condition Discharge:
    5.1 Flatten pure conjuncts, reduce nested `ByteSlice.readLE`/`getD`/`length`, and fire
        `rfl`/unification equations to ground any remaining witness MVars (`?wᵢ`, `?off`, `?len`).
    5.2 Discharge `Q_addr` (`proveAddrEqFull?`).
    5.3 Discharge `Q_pure` last when metavariables are ground. -/
def runPhase5Discharge (tacName : String) (ctx : CtxFacts)
    (addrCache : IO.Ref (Std.HashMap Expr LinAddr64))
    (addrQueue : IO.Ref (Array (MVarId × Expr)))
    (pureQueue : IO.Ref (Array (MVarId × Expr))) : TacticM Unit := do
  let rawPures ← pureQueue.get
  let mut flatPures : Array MVarId := #[]
  for (g, _) in rawPures do
    let items ← flattenPureGoalConjuncts g
    for (gi, _) in items do
      flatPures := flatPures.push gi
  let mut groundingProgress := true
  while groundingProgress do
    groundingProgress := false
    for idx in [:flatPures.size] do
      let g := flatPures[idx]!
      if ← g.isAssigned then continue
      let g' ← reduceByteSliceGoalIfPossible g
      flatPures := flatPures.set! idx g'
      if ← g'.isAssigned then
        groundingProgress := true
        continue
      let ty := (← instantiateMVars (← g'.getType)).consumeMData
      if ty.isAppOfArity ``Eq 3 then
        let lhs := ty.getArg! 1
        let rhs := ty.getArg! 2
        if lhs.hasExprMVar || rhs.hasExprMVar then
          if ← withReducible (isDefEq lhs rhs) then
            let lhs' ← instantiateMVars lhs
            g'.assign (← mkEqRefl lhs')
            groundingProgress := true

  for (ag, aTy0) in (← addrQueue.get) do
    if ← ag.isAssigned then continue
    let aTy := (← instantiateMVars aTy0).consumeMData
    if aTy.isAppOfArity ``Eq 3 then
      if let some prf ← proveAddrEqFull? ctx addrCache (aTy.getArg! 1) (aTy.getArg! 2) then
        ag.assign prf
        continue
    throwError "{tacName} (Phase 5 `Q_addr`): failed to prove deferred address equality:{indentExpr aTy}"

  for g in flatPures do
    dischargeSinglePureGoal tacName ctx addrCache g

/-- Master 5-Phase `P ⊢ Q` prover returning a kernel proof term of `P ⊢ Q`. -/
def proveBiEntailExpr (tacName : String) (P Q : Expr) : TacticM Expr := do
  let reg ← buildBiAbdRegistry
  let P ← instantiateMVars P
  let Q ← instantiateMVars Q
  let rhsHeads ← collectSurfaceHeads Q
  let addrQueue ← IO.mkRef #[]
  let pureQueue ← IO.mkRef #[]
  let prf ← reduceLHS reg rhsHeads P Q fun pSpatial => do
    let ctx ← ProofLib.Sep.collectCtxFacts
    let addrCache ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
    let actualLhsHeads ← collectSurfaceHeads pSpatial
    reduceRHS reg actualLhsHeads pureQueue pSpatial Q fun qSpatial => do
      let spPrf ← solveSpatialBiAbd tacName reg ctx addrCache addrQueue pureQueue pSpatial qSpatial
      runPhase5Discharge tacName ctx addrCache addrQueue pureQueue
      instantiateMVars spPrf
  instantiateMVars prf

/-- Tactic front-end supporting `P ⊢ Q`, `m ⊨ Q`, and `SepWP prog pc s P post oom` (via a local
    `SepWP prog pc s Q post oom` hypothesis and `SepWP.weaken_pre`), automatically introducing any
    leading `let`-bindings into `LocalContext`. -/
def evalBiEntailCore (tacName : String) : TacticM Unit := do
  while (← instantiateMVars (← (← getMainGoal).getType)).consumeMData.isLet do
    let (_, g') ← (← getMainGoal).intro1P
    replaceMainGoal [g']
  withMainContext do
    let g ← getMainGoal
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    -- Case 1: `P ⊢ Q`
    if tgt.isAppOfArity ``Arm64.SepProp.Entails 2 then
      let prf ← proveBiEntailExpr tacName (tgt.getArg! 0) (tgt.getArg! 1)
      g.assign prf
      replaceMainGoal []
      return
    -- Case 2: `m ⊨ Q`
    if tgt.isAppOfArity ``Arm64.SepProp.Satisfies 2 then
      let Q := tgt.getArg! 0
      let m := tgt.getArg! 1
      let (_, existingFrame?) ← extractRHSGoalsAndFrame Q
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let dty := (← instantiateMVars decl.type).consumeMData
        if dty.isAppOfArity ``Arm64.SepProp.Satisfies 2 && dty.getArg! 1 == m then
          let P := dty.getArg! 0
          if existingFrame?.isSome then
            let hent ← proveBiEntailExpr tacName P Q
            let qInst ← instantiateMVars Q
            g.assign (mkAppN (mkConst ``ProofLib.Sep.satisfies_of_entails) #[m, P, qInst, decl.toExpr, hent])
          else
            let frameM ← mkFreshExprMVar (mkConst ``Arm64.SepProp) (userName := `Frame)
            let qFramed := mkApp2 (mkConst ``Arm64.SepProp.sepConj) Q frameM
            let hent ← proveBiEntailExpr tacName P qFramed
            let fInst ← instantiateMVars frameM
            g.assign (mkAppN (mkConst ``ProofLib.Sep.satisfies_of_bi_frame) #[m, P, Q, fInst, decl.toExpr, hent])
          replaceMainGoal []
          return
      throwError "{tacName}: no `m ⊨ P` hypothesis found in local context for:{indentExpr tgt}"
    -- Case 3: `SepWP prog pc s P post oom`
    if tgt.isAppOfArity ``ProofLib.SepWP 6 then
      let args := tgt.getAppArgs
      let prog := args[0]!; let pc := args[1]!; let st := args[2]!
      let P := args[3]!; let post := args[4]!; let oom := args[5]!
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let dty := (← instantiateMVars decl.type).consumeMData
        if dty.isAppOfArity ``ProofLib.SepWP 6 then
          let dArgs := dty.getAppArgs
          if (← withReducible (isDefEq dArgs[0]! prog)) &&
             (← withReducible (isDefEq dArgs[1]! pc)) &&
             (← withReducible (isDefEq dArgs[2]! st)) &&
             (← withReducible (isDefEq dArgs[4]! post)) &&
             (← withReducible (isDefEq dArgs[5]! oom)) then
            let Q := dArgs[3]!
            let hent ← proveBiEntailExpr tacName P Q
            let prf ← mkAppM ``ProofLib.SepWP.weaken_pre #[hent, decl.toExpr]
            g.assign prf
            replaceMainGoal []
            return
      throwError "{tacName}: no matching `SepWP` continuation hypothesis found in local context"
    throwError "{tacName}: expected `P ⊢ Q`, `m ⊨ Q`, or `SepWP ...`, got:{indentExpr tgt}"

/-- Deterministic 5-Phase bi-abductive separation-logic entailment solver. -/
elab "bi_entail" : tactic => _root_.ProofLib.Sep.evalBiEntailCore "bi_entail"

/-- Deterministic 5-Phase bi-abductive separation-logic frame-inference solver. -/
elab "bi_frame" : tactic => _root_.ProofLib.Sep.evalBiEntailCore "bi_frame"

end

end ProofLib.Sep
