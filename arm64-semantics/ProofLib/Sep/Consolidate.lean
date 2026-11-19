/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Addr
public import ProofLib.SepLogic.FreshRO
public meta import Lean

/-!
# Footprint Disjointness Oracle, Named Spatial Context, and Diamond Branch Joins

Provides three separation-logic automation layers over `Arm64.SepProp` and `SepWP`:
1. **Reflected `FpTree` Spatial Footprint & Disjointness Oracle (`HasFootprint`, `SepFootprintRule`,
   `@[sep_footprint]`, `register_sep_footprint`, `FpTree`, `sep_disjoint`, `wp_disjoint`)**:
   on-demand derivation of pointer inequalities (`p ≠ q`), `OutsideRegion`, `DisjointRegions`,
   parameterized container membership exclusion (`hd ∉ cs`), read-write vs. read-only separation,
   and total 64-bit address-space pigeonhole bounds (`∑ lenᵢ ≤ 2 ^ 64`) in $O(\log N)$ balanced-tree
   LCA depth with zero `ac_rfl`.
2. **Named Dual Spatial Context (`sepHyp`, `SepDup`, `sintro`, `sname`, `sframe`, `sep_accu`)**:
   semireducible named hypothesis tags (`□ "ro_hdr" : P` persistent in `Γ_□` and `∗ "stk_buf" : P`
   linear in `Σ_∗`) with InfoView delaboration, duplicable persistent `Γ_□` retention across
   framing, and automatic frame accumulation into `?Frame : SepProp`.
3. **Diamond Branch-Join Spatial LUB Reconciler (`SepJoinLub`, `sep_join_lub`, `wp_if_join_auto`,
   `wp_join_auto`)**: factors out unchanged spatial frames in $O(N)$ associative steps and computes
   the spatial least upper bound of diverged branch atoms (value differences → `∃∗ v`, split-vs-whole
   `memRegion` coalescing, and custom `SepJoinLub` predicate re-folding) with zero restated frame
   atoms.
-/

namespace ProofLib.Sep

open Arm64 ProofLib

public section

universe u

/-! ## 1. Extensible Spatial Footprint Witness (`HasFootprint`) & `FpTree` Oracle -/

/-- Extensible spatial footprint witness: every partial heap satisfying `P` owns each byte in
    `[base, base + len)` (`InRegion base len x`) as read-write (`isRW = true`, `OwnsRW`) or
    read-only (`isRW = false`, `OwnsRO`). -/
class HasFootprint (P : SepProp) (isRW : outParam Bool)
    (base : outParam (BitVec 64)) (len : outParam Nat) : Prop where
  owns_at : ∀ x : BitVec 64, InRegion base len x →
    if isRW then OwnsRW P x else OwnsRO P x

theorem HasFootprint.ownsRW {P : SepProp} {base : BitVec 64} {len : Nat}
    (h : HasFootprint P true base len) {x : BitVec 64} (hx : InRegion base len x) :
    OwnsRW P x := by
  simpa using h.owns_at x hx

theorem HasFootprint.ownsRO {P : SepProp} {base : BitVec 64} {len : Nat}
    (h : HasFootprint P false base len) {x : BitVec 64} (hx : InRegion base len x) :
    OwnsRO P x := by
  simpa using h.owns_at x hx

/-- Instance-backed registry for custom `@[sep_footprint]` theorems (including parameterized
    container-membership rules such as `c ∈ cs → HasFootprint (FreeListInv cs) true c 16`),
    usable both inside the defining module and across imports. -/
class SepFootprintRule (declName : Lean.Name) : Prop where
  ready : True := True.intro

/-! ### Built-in `HasFootprint` Instances -/

instance instHasFootprintMemRegion (b : BitVec 64) (n : Nat) :
    HasFootprint (memRegion b n) true b n where
  owns_at x hx := by simpa using ownsRW_memRegion b n x hx

instance instHasFootprintPointsTo8 (a : BitVec 64) (v : BitVec 8) :
    HasFootprint (a ↦₈ v) true a 1 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsTo8_entails_memRegion a v) (ownsRW_memRegion a 1 x hx)

instance instHasFootprintPointsTo16 (a : BitVec 64) (v : BitVec 16) :
    HasFootprint (a ↦₁₆ v) true a 2 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsTo16_entails_memRegion a v) (ownsRW_memRegion a 2 x hx)

instance instHasFootprintPointsTo32 (a : BitVec 64) (v : BitVec 32) :
    HasFootprint (a ↦₃₂ v) true a 4 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsTo32_entails_memRegion a v) (ownsRW_memRegion a 4 x hx)

instance instHasFootprintPointsTo64 (a : BitVec 64) (v : BitVec 64) :
    HasFootprint (a ↦₆₄ v) true a 8 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsTo64_entails_memRegion a v) (ownsRW_memRegion a 8 x hx)

instance instHasFootprintPointsTo128 (a : BitVec 64) (v : BitVec 128) :
    HasFootprint (a ↦₁₂₈ v) true a 16 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsTo128_entails_memRegion a v) (ownsRW_memRegion a 16 x hx)

instance instHasFootprintPointsToBytes (b : BitVec 64) (bs : List (BitVec 8)) :
    HasFootprint (b ↦ₛ bs) true b bs.length where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (pointsToBytes_entails_memRegion b bs)
      (ownsRW_memRegion b bs.length x hx)

theorem ownsRO_pointsToBytesRO_unbounded (b : BitVec 64) (bs : List (BitVec 8)) (x : BitVec 64)
    (hx : InRegion b bs.length x) : OwnsRO (b ↦ᵣ bs) x := by
  let k := (x - b).toNat
  have hk_lt : k < bs.length := hx
  have hk_64 : k + 1 ≤ 2 ^ 64 := by
    have := (x - b).isLt
    omega
  have hsplit : bs = bs.take (k + 1) ++ bs.drop (k + 1) := (List.take_append_drop (k + 1) bs).symm
  rw [hsplit, pointsToBytesRO_append]
  have hlen : (bs.take (k + 1)).length = k + 1 := List.length_take_of_le (by omega)
  refine ownsRO_sepConj_left (ownsRO_pointsToBytesRO_at (by rw [hlen]; exact hk_64) ?_)
  unfold InRegion
  rw [hlen]
  change k < k + 1
  omega

instance instHasFootprintPointsToBytesRO (b : BitVec 64) (bs : List (BitVec 8)) :
    HasFootprint (b ↦ᵣ bs) false b bs.length where
  owns_at x hx := by simpa using ownsRO_pointsToBytesRO_unbounded b bs x hx

instance instHasFootprintPointsTo8RO (a : BitVec 64) (v : BitVec 8) :
    HasFootprint (a ↦₈ᵣ v) false a 1 where
  owns_at x hx := by
    have heq : x = a := by
      unfold InRegion at hx
      bv_omega
    subst heq
    simpa using ownsRO_pointsTo8RO x v

instance instHasFootprintPointsTo16RO (a : BitVec 64) (v : BitVec 16) :
    HasFootprint (a ↦₁₆ᵣ v) false a 2 where
  owns_at x hx := by
    rw [pointsTo16RO_eq_pointsToBytesRO]
    have hl : (unpack16 v).length = 2 := by simp [unpack16]
    exact ownsRO_pointsToBytesRO_unbounded a (unpack16 v) x (hl ▸ hx)

instance instHasFootprintPointsTo32RO (a : BitVec 64) (v : BitVec 32) :
    HasFootprint (a ↦₃₂ᵣ v) false a 4 where
  owns_at x hx := by
    rw [pointsTo32RO_eq_pointsToBytesRO]
    have hl : (unpack32 v).length = 4 := by simp [unpack32]
    exact ownsRO_pointsToBytesRO_unbounded a (unpack32 v) x (hl ▸ hx)

theorem ownsRO_of_isBlockRO {P : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop}
    (hb : IsBlockRO P b n Φ) (hn : n ≤ 2 ^ 64) {x : BitVec 64} (hx : InRegion b n x) :
    OwnsRO P x := by
  intro h hh
  obtain ⟨m₀, _, rfl⟩ := (hb.iff h).mp hh
  have hlen : ∀ (m : Memory) (a : BitVec 64) (k : Nat), (m.readBytes a k).length = k := by
    intro m a k
    induction k generalizing a with
    | zero => simp [Memory.readBytes]
    | succ k ih => simp [Memory.readBytes, ih]
  let bs := m₀.readBytes b n
  have hbs_len : bs.length = n := hlen m₀ b n
  have hh_bs : (b ↦ᵣ bs).holds (regionHeapRO b n m₀) :=
    ((IsBlockRO.pointsToBytesRO b bs (by omega)).iff _).mpr ⟨m₀, by simp [bs, hbs_len], by rw [hbs_len]⟩
  have hx' : InRegion b bs.length x := by rwa [hbs_len]
  exact ownsRO_pointsToBytesRO_unbounded b bs x hx' _ hh_bs

instance instHasFootprintPointsTo64RO (a : BitVec 64) (v : BitVec 64) :
    HasFootprint (a ↦₆₄ᵣ v) false a 8 where
  owns_at x hx := by
    simpa using ownsRO_of_isBlockRO (IsBlockRO.pointsTo64RO a v) (by decide) hx

instance instHasFootprintPointsTo128RO (a : BitVec 64) (v : BitVec 128) :
    HasFootprint (a ↦₁₂₈ᵣ v) false a 16 where
  owns_at x hx := by
    simpa using ownsRO_of_isBlockRO (IsBlockRO.pointsTo128RO a v) (by decide) hx

theorem ownsRO_pointsToWords64RO :
    ∀ (ws : List (BitVec 64)) (a x : BitVec 64),
      InRegion a (8 * ws.length) x → OwnsRO (a ↦₆₄ᵣ* ws) x
  | [], _, _, hx => absurd hx (by simp [InRegion])
  | w :: ws, a, x, hx => by
    rw [pointsToWords64RO_cons]
    by_cases hlo : (x - a).toNat < 8
    · exact ownsRO_sepConj_left ((instHasFootprintPointsTo64RO a w).ownsRO hlo)
    · refine ownsRO_sepConj_right (ownsRO_pointsToWords64RO ws (a + 8#64) x ?_)
      unfold InRegion at hx ⊢
      simp only [List.length_cons] at hx
      bv_omega

instance instHasFootprintPointsToWords64RO (a : BitVec 64) (ws : List (BitVec 64)) :
    HasFootprint (a ↦₆₄ᵣ* ws) false a (8 * ws.length) where
  owns_at x hx := by simpa using ownsRO_pointsToWords64RO ws a x hx

instance instHasFootprintCells (a : BitVec 64) (k : Nat) :
    HasFootprint (ProofLib.cells a k) true a (8 * k) where
  owns_at x hx := by
    change OwnsRW (ProofLib.cells a k) x
    by_cases hb : 8 * k ≤ 2 ^ 64
    · rw [← memRegion_cells a k hb]
      exact ownsRW_memRegion a (8 * k) x hx
    · have hk : k = 2 ^ 61 + (k - 2 ^ 61) := by omega
      rw [hk, cells_split a (2 ^ 61) (k - 2 ^ 61), ← memRegion_cells a (2 ^ 61) (by decide)]
      refine ownsRW_sepConj_left (ownsRW_memRegion a (8 * 2 ^ 61) x ?_)
      unfold InRegion
      have := (x - a).isLt
      omega

instance instHasFootprintPointsToWords64 (a : BitVec 64) (ws : List (BitVec 64)) :
    HasFootprint (a ↦₆₄* ws) true a (8 * ws.length) where
  owns_at x hx := by
    change OwnsRW (a ↦₆₄* ws) x
    let idx := (x - a).toNat / 8
    have hidx_lt : idx < ws.length := by
      unfold InRegion at hx
      omega
    have hidx_64 : 8 * (idx + 1) ≤ 2 ^ 64 := by
      have := (x - a).isLt
      omega
    have hsplit : ws = ws.take (idx + 1) ++ ws.drop (idx + 1) :=
      (List.take_append_drop (idx + 1) ws).symm
    rw [hsplit, pointsToWords64_append]
    have hlen : (ws.take (idx + 1)).length = idx + 1 := List.length_take_of_le (by omega)
    refine ownsRW_sepConj_left
      (OwnsRW.of_entails (pointsToWords64_entails_memRegion _ a (by rw [hlen]; exact hidx_64)) ?_)
    refine ownsRW_memRegion a (8 * (ws.take (idx + 1)).length) x ?_
    unfold InRegion
    rw [hlen]
    omega

private theorem stackFrameSlotsCont_left (sp : BitVec 64) (k : Nat) :
    ∀ (n : Nat) (X : SepProp),
      stackFrameSlotsCont sp k n (fun rest => X ∗ rest) = X ∗ stackFrameSlotsFrom sp k n
  | 0, X => by simp [stackFrameSlotsCont, stackFrameSlotsFrom]
  | 1, X => by
    simp [stackFrameSlotsCont, stackFrameSlotsFrom, sepExists_sepConj_right]
  | n + 2, X => by
    have hfun : ∀ v : BitVec 64,
        (fun rest => X ∗ (((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗ rest)) =
        (fun rest => (X ∗ ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v)) ∗ rest) :=
      fun v => funext fun rest => (sepConj_assoc _ _ _).symm
    have h1 := fun v => stackFrameSlotsCont_left sp k (n + 1)
      (X ∗ ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v))
    have h2 := fun v => stackFrameSlotsCont_left sp k (n + 1)
      ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v)
    conv => lhs; unfold stackFrameSlotsCont; simp only [hfun, h1]
    conv => rhs; arg 2; unfold stackFrameSlotsFrom stackFrameSlotsCont; simp only [h2]
    simp only [sepConj_assoc, sepExists_sepConj_right]

private theorem stackFrameSlotsFrom_succ_local (sp : BitVec 64) (k n : Nat) :
    stackFrameSlotsFrom sp k (n + 1) =
      ∃∗ v : BitVec 64,
        ((sp - BitVec.ofNat 64 ((k + n + 1) * 8)) ↦₆₄ v) ∗ stackFrameSlotsFrom sp k n := by
  cases n with
  | zero => simp [stackFrameSlotsFrom, stackFrameSlotsCont]
  | succ m =>
    conv => lhs; unfold stackFrameSlotsFrom stackFrameSlotsCont
    have h := fun v => stackFrameSlotsCont_left sp k (m + 1)
      ((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v)
    have heq : k + (m + 1) + 1 = k + m + 2 := by omega
    simp only [heq, h]

private theorem ownsRW_stackFrameSlotsFrom_ge (sp : BitVec 64) :
    ∀ (d : Nat) (x : BitVec 64), OwnsRW (stackFrameSlotsFrom sp 0 (2 ^ 61 + d)) x
  | 0, x => by
    have heq : stackFrameSlotsFrom sp 0 (2 ^ 61) =
        memRegion (sp - BitVec.ofNat 64 (2 ^ 64)) (2 ^ 64) := by
      have h := stackFrameAt_eq_memRegion sp (2 ^ 64) (Nat.le_refl _)
      unfold stackFrameAt at h
      simpa using h
    rw [Nat.add_zero, heq]
    exact ownsRW_memRegion _ (2 ^ 64) x (by unfold InRegion; exact (x - _).isLt)
  | d + 1, x => by
    rw [show 2 ^ 61 + (d + 1) = (2 ^ 61 + d) + 1 by omega, stackFrameSlotsFrom_succ_local]
    exact OwnsRW.sepExists fun _ => ownsRW_sepConj_right (ownsRW_stackFrameSlotsFrom_ge sp d x)

instance instHasFootprintStackFrameAt (sp : BitVec 64) (n : Nat) :
    HasFootprint (stackFrameAt sp n) true (sp - BitVec.ofNat 64 n) n where
  owns_at x hx := by
    change OwnsRW (stackFrameAt sp n) x
    by_cases hn : n ≤ 2 ^ 64
    · rw [stackFrameAt_eq_memRegion sp n hn]
      exact ownsRW_memRegion _ n x hx
    · unfold stackFrameAt
      have h0 : (n == 0) = false := beq_false_of_ne (by omega)
      rw [h0]
      by_cases h8 : n % 8 = 0
      · simp only [Bool.false_eq_true, ↓reduceIte, h8, beq_self_eq_true]
        have hs : n / 8 = 2 ^ 61 + (n / 8 - 2 ^ 61) := by omega
        rw [hs]
        exact ownsRW_stackFrameSlotsFrom_ge sp (n / 8 - 2 ^ 61) x
      · have h8f : (n % 8 == 0) = false := beq_false_of_ne h8
        simp only [Bool.false_eq_true, ↓reduceIte, h8f]
        exact ownsRW_memRegion _ n x hx

instance instHasFootprintStackFrame16At (sp : BitVec 64) :
    HasFootprint (stackFrame16At sp) true (sp - 16#64) 16 where
  owns_at x hx := by
    change OwnsRW (stackFrame16At sp) x
    rw [stackFrame16At_def]
    refine OwnsRW.sepExists fun v0 => OwnsRW.sepExists fun v1 => ?_
    have hent : ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1) ⊢ memRegion (sp - 16#64) 16 := by
      refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)) ?_
      rw [← memRegion_split_sub sp 16 8 8]
      exact Entails.refl _
    exact OwnsRW.of_entails hent (ownsRW_memRegion _ 16 x hx)

instance instHasFootprintStackFrame32At (sp : BitVec 64) :
    HasFootprint (stackFrame32At sp) true (sp - 32#64) 32 where
  owns_at x hx := by
    change OwnsRW (stackFrame32At sp) x
    rw [stackFrame32At_def]
    refine OwnsRW.sepExists fun v0 => OwnsRW.sepExists fun v1 =>
      OwnsRW.sepExists fun v2 => OwnsRW.sepExists fun v3 => ?_
    have hent :
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
        memRegion (sp - 32#64) 32 := by
      refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo64_entails_memRegion _ _)))) ?_
      have hs1 := memRegion_split_sub sp 32 16 16
      have hs2 := memRegion_split_sub sp 16 8 8
      have hs3 := memRegion_split_le (sp - 32#64) 8 16 (by decide) (by decide)
      have ha24 : sp - 32#64 + BitVec.ofNat 64 8 = sp - 24#64 := by bv_arith
      rw [ha24] at hs3
      change memRegion (sp - 32#64) 8 ∗ (memRegion (sp - 24#64) 8 ∗
        (memRegion (sp - 16#64) 8 ∗ memRegion (sp - 8#64) 8)) ⊢ memRegion (sp - 32#64) 32
      rw [← sepConj_assoc (memRegion (sp - 32#64) 8), ← hs3, ← hs2, ← hs1]
      exact Entails.refl _
    exact OwnsRW.of_entails hent (ownsRW_memRegion _ 32 x hx)

theorem ownsRO_sepExists {α : Sort u} {P : α → SepProp} {x : BitVec 64}
    (hP : ∀ v, OwnsRO (P v) x) : OwnsRO (∃∗ v, P v) x := by
  intro h hh
  obtain ⟨v, hhv⟩ := SepProp.holds_sepExists hh
  exact hP v h hhv

instance instHasFootprintSepExists {α : Sort u} (P : α → SepProp)
    (isRW : Bool) (b : BitVec 64) (n : Nat) [h : ∀ v : α, HasFootprint (P v) isRW b n] :
    HasFootprint (∃∗ v : α, P v) isRW b n where
  owns_at x hx := by
    cases isRW
    · exact ownsRO_sepExists fun v => (h v).ownsRO hx
    · exact OwnsRW.sepExists fun v => (h v).ownsRW hx

/-! ### Balanced Binary Footprint Tree (`FpTree`) & $O(\log N)$ LCA Disjointness -/

/-- Binary tree over `SepProp` atoms annotated with RW/RO footprints at selected leaves and
    `.opaqueAtom` for untouched off-path subtrees, enabling $O(\log N)$ LCA extraction. -/
inductive FpTree where
  | rw (P : SepProp) (base : BitVec 64) (len : Nat)
  | ro (P : SepProp) (base : BitVec 64) (len : Nat)
  | opaqueAtom (P : SepProp)
  | node (l r : FpTree)

/-- Spatial interpretation of an `FpTree`. -/
@[expose] def FpTree.interp : FpTree → SepProp
  | .rw P _ _ => P
  | .ro P _ _ => P
  | .opaqueAtom P => P
  | .node l r => l.interp ∗ r.interp

/-- Footprint validity predicate for all annotated leaves in `FpTree`. -/
@[expose] def FpTree.Valid : FpTree → Prop
  | .rw P b n => HasFootprint P true b n
  | .ro P b n => HasFootprint P false b n
  | .opaqueAtom _ => True
  | .node l r => l.Valid ∧ r.Valid

/-- Binary tree path (`false` = left, `true` = right). -/
abbrev FpPath := List Bool

/-- Lookup `(isRW, base, len)` at path `p`. -/
@[expose] def FpTree.leafAt : FpTree → FpPath → Option (Bool × BitVec 64 × Nat)
  | .rw _ b n, [] => some (true, b, n)
  | .ro _ b n, [] => some (false, b, n)
  | .node l _, false :: ps => l.leafAt ps
  | .node _ r, true :: ps => r.leafAt ps
  | _, _ => none

/-- Two paths diverge at some lowest common ancestor node. -/
@[expose] def FpPath.Disjoint : FpPath → FpPath → Bool
  | false :: _, true :: _ => true
  | true :: _, false :: _ => true
  | false :: p1, false :: p2 => FpPath.Disjoint p1 p2
  | true :: p1, true :: p2 => FpPath.Disjoint p1 p2
  | _, _ => false

theorem FpTree.ownsAt_of_leafAt
    {t : FpTree} {p : FpPath} {isRW : Bool} {b : BitVec 64} {n : Nat} {x : BitVec 64}
    (hv : t.Valid) (hleaf : t.leafAt p = some (isRW, b, n)) (hx : InRegion b n x) :
    (if isRW then OwnsRW t.interp x else OwnsRO t.interp x) := by
  induction t generalizing p with
  | rw P b' n' =>
    cases p with
    | nil =>
      dsimp only [FpTree.leafAt] at hleaf
      injection hleaf with h; injection h with hrw hb; injection hb with hb hn
      subst hrw; subst hb; subst hn
      exact hv.owns_at x hx
    | cons _ _ => cases hleaf
  | ro P b' n' =>
    cases p with
    | nil =>
      dsimp only [FpTree.leafAt] at hleaf
      injection hleaf with h; injection h with hrw hb; injection hb with hb hn
      subst hrw; subst hb; subst hn
      exact hv.owns_at x hx
    | cons _ _ => cases hleaf
  | opaqueAtom _ => cases p <;> cases hleaf
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    cases p with
    | nil => cases hleaf
    | cons c ps =>
      dsimp only [FpTree.interp]
      cases c
      · have ih := ihl hvl hleaf
        cases isRW
        · exact ownsRO_sepConj_left ih
        · exact ownsRW_sepConj_left ih
      · have ih := ihr hvr hleaf
        cases isRW
        · exact ownsRO_sepConj_right ih
        · exact ownsRW_sepConj_right ih

/-- Universal $O(\log N)$ LCA byte-disjointness theorem over `FpTree` (RW-RW, RW-RO, RO-RW). -/
theorem FpTree.disjoint_inRegion_heap
    {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool} {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    {h : Heap} {x : BitVec 64}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hh : t.interp.holds h) (hx₁ : InRegion b₁ n₁ x) (hx₂ : InRegion b₂ n₂ x) : False := by
  induction t generalizing p₁ p₂ h with
  | rw _ _ _ => cases p₁ <;> cases p₂ <;> first | cases hdisj | cases hl₁
  | ro _ _ _ => cases p₁ <;> cases p₂ <;> first | cases hdisj | cases hl₁
  | opaqueAtom _ => cases p₁ <;> cases hl₁
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    revert hdisj hl₁ hl₂
    rcases p₁ with _ | ⟨c₁, q₁⟩
    · intro hdisj; cases hdisj
    rcases p₂ with _ | ⟨c₂, q₂⟩
    · intro hdisj; cases c₁ <;> cases hdisj
    intro hdisj hl₁ hl₂
    dsimp only [FpTree.interp] at hh
    cases c₁ <;> cases c₂
    · dsimp only [FpPath.Disjoint, FpTree.leafAt] at hdisj hl₁ hl₂
      obtain ⟨h₁, hh₁⟩ := SepProp.holds_sepConj_left hh
      exact ihl hvl hdisj hl₁ hl₂ hh₁
    · dsimp only [FpTree.leafAt] at hl₁ hl₂
      have ho₁ := FpTree.ownsAt_of_leafAt hvl hl₁ hx₁
      have ho₂ := FpTree.ownsAt_of_leafAt hvr hl₂ hx₂
      cases rw₁ <;> cases rw₂
      · cases hrw
      · exact ownsRO_ownsRW_disjoint_sepConj ho₁ ho₂ hh
      · exact ownsRW_ownsRO_disjoint_sepConj ho₁ ho₂ hh
      · exact ownsRW_disjoint_sepConj ho₁ ho₂ hh
    · dsimp only [FpTree.leafAt] at hl₁ hl₂
      have ho₁ := FpTree.ownsAt_of_leafAt hvr hl₁ hx₁
      have ho₂ := FpTree.ownsAt_of_leafAt hvl hl₂ hx₂
      cases rw₁ <;> cases rw₂
      · cases hrw
      · exact ownsRW_ownsRO_disjoint_sepConj ho₂ ho₁ hh
      · exact ownsRO_ownsRW_disjoint_sepConj ho₂ ho₁ hh
      · exact ownsRW_disjoint_sepConj ho₂ ho₁ hh
    · dsimp only [FpPath.Disjoint, FpTree.leafAt] at hdisj hl₁ hl₂
      have hh' : (r.interp ∗ l.interp).holds h := sepConj_comm l.interp r.interp ▸ hh
      obtain ⟨h₂, hh₂⟩ := SepProp.holds_sepConj_left hh'
      exact ihr hvr hdisj hl₁ hl₂ hh₂

theorem FpTree.outsideRegion_of_inRegion_heap {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool}
    {b₁ b₂ pt : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hpt : InRegion b₁ n₁ pt) (hh : t.interp.holds h) :
    OutsideRegion b₂ n₂ pt := by
  rw [outsideRegion_iff_not_inRegion]
  intro hin₂
  exact FpTree.disjoint_inRegion_heap hv hdisj hrw hl₁ hl₂ hh hpt hin₂

theorem FpTree.outsideRegion_heap {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool}
    {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hn₁ : 0 < n₁) (hh : t.interp.holds h) :
    OutsideRegion b₂ n₂ b₁ :=
  FpTree.outsideRegion_of_inRegion_heap hv hdisj hrw hl₁ hl₂
    (by unfold InRegion; rw [BitVec.sub_self]; exact hn₁) hh

theorem FpTree.disjointRegions_heap {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool}
    {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hh : t.interp.holds h) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj' : FpPath.Disjoint p₂ p₁ = true := by
    clear hv hl₁ hl₂ hh
    induction p₁ generalizing p₂ with
    | nil => cases p₂ <;> cases hdisj
    | cons c₁ q₁ ih =>
      rcases p₂ with _ | ⟨c₂, q₂⟩
      · cases c₁ <;> cases hdisj
      · cases c₁ <;> cases c₂ <;> simp_all [FpPath.Disjoint]
  have hrw' : (rw₂ || rw₁) = true := by cases rw₁ <;> cases rw₂ <;> simp_all
  exact ⟨FpTree.outsideRegion_heap hv hdisj' hrw' hl₂ hl₁ hn₂ hh,
    FpTree.outsideRegion_heap hv hdisj hrw hl₁ hl₂ hn₁ hh⟩

theorem FpTree.ne_heap {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool}
    {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hn₁ : 0 < n₁) (hh : t.interp.holds h) (hn₂ : 0 < n₂) :
    b₁ ≠ b₂ := by
  intro heq
  subst heq
  have hout := FpTree.outsideRegion_heap hv hdisj hrw hl₁ hl₂ hn₁ hh
  simp only [OutsideRegion, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod] at hout
  omega

theorem FpTree.nonWrap_or_heap {t : FpTree} {p₁ p₂ : FpPath} {rw₁ rw₂ : Bool}
    {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true) (hrw : (rw₁ || rw₂) = true)
    (hl₁ : t.leafAt p₁ = some (rw₁, b₁, n₁)) (hl₂ : t.leafAt p₂ = some (rw₂, b₂, n₂))
    (hn₁ : 0 < n₁) (_hb₁ : b₁.toNat + n₁ ≤ 2 ^ 64) (hn₂ : 0 < n₂) (hh : t.interp.holds h) :
    b₁.toNat + n₁ ≤ b₂.toNat ∨ b₂.toNat + n₂ ≤ b₁.toNat := by
  refine Classical.byContradiction fun hno => ?_
  by_cases hle : b₁.toNat ≤ b₂.toNat
  · have hx₁ : InRegion b₁ n₁ b₂ := by unfold InRegion; bv_omega
    have hx₂ : InRegion b₂ n₂ b₂ := by unfold InRegion; rw [BitVec.sub_self]; exact hn₂
    exact FpTree.disjoint_inRegion_heap hv hdisj hrw hl₁ hl₂ hh hx₁ hx₂
  · have hx₁ : InRegion b₁ n₁ b₁ := by unfold InRegion; rw [BitVec.sub_self]; exact hn₁
    have hx₂ : InRegion b₂ n₂ b₁ := by unfold InRegion; bv_omega
    exact FpTree.disjoint_inRegion_heap hv hdisj hrw hl₁ hl₂ hh hx₁ hx₂

/-! ### Total 64-Bit Address-Space Pigeonhole Bound (`∑ lenᵢ ≤ 2 ^ 64`) -/

private def countNat : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => countNat n p + if p n then 1 else 0

private theorem countNat_le : ∀ (K : Nat) (p : Nat → Bool), countNat K p ≤ K
  | 0, _ => Nat.le_refl 0
  | n + 1, p => by
    have ih := countNat_le n p
    unfold countNat
    split <;> omega

private theorem countNat_congr :
    ∀ {K : Nat} {p q : Nat → Bool}, (∀ u, u < K → p u = q u) → countNat K p = countNat K q
  | 0, _, _, _ => rfl
  | n + 1, p, q, h => by
    unfold countNat
    rw [countNat_congr (fun u hu => h u (by omega)), h n (by omega)]

private theorem countNat_zero_pred : ∀ K : Nat, countNat K (fun _ => false) = 0
  | 0 => rfl
  | n + 1 => by unfold countNat; simp [countNat_zero_pred n]

private theorem countNat_or_disjoint :
    ∀ {K : Nat} {p q : Nat → Bool},
      (∀ u, u < K → p u = true → q u = true → False) →
      countNat K (fun u => p u || q u) = countNat K p + countNat K q
  | 0, _, _, _ => rfl
  | n + 1, p, q, hd => by
    unfold countNat
    rw [countNat_or_disjoint (fun u hu => hd u (by omega))]
    cases hp : p n <;> cases hq : q n
    · simp [hp, hq]
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega
    · exact False.elim (hd n (by omega) hp hq)

private theorem countNat_singleton :
    ∀ {K x : Nat}, x < K → countNat K (fun u => decide (u = x)) = 1
  | 0, _, hx => absurd hx (by omega)
  | n + 1, x, hx => by
    unfold countNat
    by_cases heq : n = x
    · subst heq
      have h0 : countNat n (fun u => decide (u = n)) = 0 := by
        rw [countNat_congr (q := fun _ => false)]
        · exact countNat_zero_pred n
        · intro u hu; simp [Nat.ne_of_lt hu]
      simp [h0]
    · have ih := countNat_singleton (K := n) (x := x) (by omega)
      simp [heq, ih]

private theorem countNat_interval (K a : Nat) :
    ∀ (len : Nat), a + len ≤ K → countNat K (fun u => decide (a ≤ u ∧ u < a + len)) = len
  | 0, _ => by
    rw [countNat_congr (q := fun _ => false)]
    · exact countNat_zero_pred K
    · intro u _; simp
  | len + 1, hb => by
    have hsplit : ∀ u < K,
        decide (a ≤ u ∧ u < a + (len + 1)) =
          (decide (a ≤ u ∧ u < a + len) || decide (u = a + len)) := by
      intro u _
      by_cases h1 : a ≤ u ∧ u < a + len
      · have hne : u ≠ a + len := by omega
        simp [h1, hne]; omega
      · by_cases h2 : u = a + len
        · subst h2; simp
        · have h3 : ¬ (a ≤ u ∧ u < a + (len + 1)) := by omega
          simp [h1, h2, h3]
    rw [countNat_congr hsplit, countNat_or_disjoint]
    · rw [countNat_interval K a len (by omega), countNat_singleton (by omega)]
    · intro u _ h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      omega

private theorem inRegion_ofNat_lt_iff (b : BitVec 64) (len u : Nat) (hu : u < 2 ^ 64) :
    InRegion b len (BitVec.ofNat 64 u) ↔
      (if b.toNat ≤ u then u - b.toNat else 2 ^ 64 + u - b.toNat) < len := by
  unfold InRegion
  have hb := b.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  by_cases hle : b.toNat ≤ u
  · have hmod : (2 ^ 64 - b.toNat + u) % 2 ^ 64 = u - b.toNat := by
      have heq : 2 ^ 64 - b.toNat + u = (u - b.toNat) + 1 * 2 ^ 64 := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp [hle, hmod]
  · have hmod : (2 ^ 64 - b.toNat + u) % 2 ^ 64 = 2 ^ 64 + u - b.toNat := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [hle, hmod]

private theorem countNat_inRegion (b : BitVec 64) (len : Nat) (hlen : len ≤ 2 ^ 64) :
    countNat (2 ^ 64) (fun u => decide (InRegion b len (BitVec.ofNat 64 u))) = len := by
  have hb := b.isLt
  by_cases hnw : b.toNat + len ≤ 2 ^ 64
  · rw [countNat_congr (q := fun u => decide (b.toNat ≤ u ∧ u < b.toNat + len))]
    · exact countNat_interval (2 ^ 64) b.toNat len hnw
    · intro u hu
      have hiff := inRegion_ofNat_lt_iff b len u hu
      by_cases hle : b.toNat ≤ u
      · simp only [hle, ↓reduceIte] at hiff
        exact decide_eq_decide.mpr (hiff.trans ⟨fun h => ⟨hle, by omega⟩, fun ⟨_, h⟩ => by omega⟩)
      · simp only [hle, ↓reduceIte] at hiff
        exact decide_eq_decide.mpr (hiff.trans ⟨fun h => by omega, fun ⟨h, _⟩ => absurd h hle⟩)
  · rw [countNat_congr (q := fun u =>
        decide (b.toNat ≤ u ∧ u < b.toNat + (2 ^ 64 - b.toNat)) ||
          decide (0 ≤ u ∧ u < 0 + (b.toNat + len - 2 ^ 64)))]
    · rw [countNat_or_disjoint,
          countNat_interval (2 ^ 64) b.toNat (2 ^ 64 - b.toNat) (by omega),
          countNat_interval (2 ^ 64) 0 (b.toNat + len - 2 ^ 64) (by omega)]
      · omega
      · intro u _ h1 h2
        simp only [decide_eq_true_eq] at h1 h2
        omega
    · intro u hu
      have hiff := inRegion_ofNat_lt_iff b len u hu
      rw [← Bool.decide_or]
      by_cases hle : b.toNat ≤ u
      · simp only [hle, ↓reduceIte] at hiff
        exact decide_eq_decide.mpr (hiff.trans (by omega))
      · simp only [hle, ↓reduceIte] at hiff
        exact decide_eq_decide.mpr (hiff.trans (by omega))

/-- Sum of RW byte lengths across all `.rw` leaves in `FpTree`. -/
@[expose] def FpTree.rwSum : FpTree → Nat
  | .rw _ _ n => n
  | .ro _ _ _ => 0
  | .opaqueAtom _ => 0
  | .node l r => l.rwSum + r.rwSum

/-- Heap-conditional `≤ 2 ^ 64` witness for each `.rw` leaf in `FpTree`. -/
@[expose] def FpTree.HoldsBounded : FpTree → Prop
  | .rw P _ n => ∀ h : Heap, P.holds h → n ≤ 2 ^ 64
  | .ro _ _ _ => True
  | .opaqueAtom _ => True
  | .node l r => l.HoldsBounded ∧ r.HoldsBounded

private def FpTree.AllRWBounded : FpTree → Prop
  | .rw _ _ n => n ≤ 2 ^ 64
  | .ro _ _ _ => True
  | .opaqueAtom _ => True
  | .node l r => l.AllRWBounded ∧ r.AllRWBounded

private def FpTree.inAnyRW : FpTree → Nat → Bool
  | .rw _ b n, u => decide (InRegion b n (BitVec.ofNat 64 u))
  | .ro _ _ _, _ => false
  | .opaqueAtom _, _ => false
  | .node l r, u => l.inAnyRW u || r.inAnyRW u

private theorem FpTree.ownsRW_of_inAnyRW {t : FpTree} {u : Nat}
    (hv : t.Valid) (hin : t.inAnyRW u = true) :
    OwnsRW t.interp (BitVec.ofNat 64 u) := by
  induction t with
  | rw _ _ _ => exact hv.ownsRW (of_decide_eq_true hin)
  | ro _ _ _ => cases hin
  | opaqueAtom _ => cases hin
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    unfold FpTree.inAnyRW at hin
    dsimp only [FpTree.interp]
    rcases Bool.or_eq_true_iff.mp hin with hl | hr
    · exact ownsRW_sepConj_left (ihl hvl hl)
    · exact ownsRW_sepConj_right (ihr hvr hr)

private theorem FpTree.countNat_eq_rwSum {t : FpTree} {h : Heap}
    (hv : t.Valid) (hb : t.AllRWBounded) (hh : t.interp.holds h) :
    countNat (2 ^ 64) t.inAnyRW = t.rwSum := by
  induction t generalizing h with
  | rw _ b n => exact countNat_inRegion b n hb
  | ro _ _ _ => exact countNat_zero_pred (2 ^ 64)
  | opaqueAtom _ => exact countNat_zero_pred (2 ^ 64)
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    rcases hb with ⟨hbl, hbr⟩
    dsimp only [FpTree.interp] at hh
    obtain ⟨h₁, hh₁⟩ := SepProp.holds_sepConj_left hh
    have hh' : (r.interp ∗ l.interp).holds h := sepConj_comm l.interp r.interp ▸ hh
    obtain ⟨h₂, hh₂⟩ := SepProp.holds_sepConj_left hh'
    have hin_eq : (FpTree.node l r).inAnyRW = fun u => l.inAnyRW u || r.inAnyRW u := rfl
    rw [hin_eq]
    dsimp only [FpTree.rwSum]
    rw [countNat_or_disjoint, ihl hvl hbl hh₁, ihr hvr hbr hh₂]
    intro u _ hl hr
    exact ownsRW_disjoint_sepConj
      (FpTree.ownsRW_of_inAnyRW hvl hl) (FpTree.ownsRW_of_inAnyRW hvr hr) hh

private theorem FpTree.rwSum_le_of_allBounded_heap {t : FpTree} {h : Heap}
    (hv : t.Valid) (hbnd : t.AllRWBounded) (hh : t.interp.holds h) :
    t.rwSum ≤ 2 ^ 64 := by
  rw [← FpTree.countNat_eq_rwSum hv hbnd hh]
  exact countNat_le (2 ^ 64) t.inAnyRW

private theorem FpTree.allRWBounded_of_holdsBounded {t : FpTree} {h : Heap}
    (hb : t.HoldsBounded) (hh : t.interp.holds h) :
    t.AllRWBounded := by
  induction t generalizing h with
  | rw _ _ _ => exact hb h hh
  | ro _ _ _ => trivial
  | opaqueAtom _ => trivial
  | node l r ihl ihr =>
    rcases hb with ⟨hbl, hbr⟩
    dsimp only [FpTree.interp] at hh
    obtain ⟨h₁, hh₁⟩ := SepProp.holds_sepConj_left hh
    have hh' : (r.interp ∗ l.interp).holds h := sepConj_comm l.interp r.interp ▸ hh
    obtain ⟨h₂, hh₂⟩ := SepProp.holds_sepConj_left hh'
    exact ⟨ihl hbl hh₁, ihr hbr hh₂⟩

theorem FpTree.rwSum_le_of_holdsBounded_heap {t : FpTree} {h : Heap}
    (hv : t.Valid) (hb : t.HoldsBounded) (hh : t.interp.holds h) :
    t.rwSum ≤ 2 ^ 64 :=
  FpTree.rwSum_le_of_allBounded_heap hv (FpTree.allRWBounded_of_holdsBounded hb hh) hh

private theorem FpTree.allRWBounded_of_sep_ownsRW {t : FpTree} {Q : SepProp} {h : Heap}
    {x : BitVec 64} (hv : t.Valid) (hQ : OwnsRW Q x) (hh : (t.interp ∗ Q).holds h) :
    t.AllRWBounded := by
  induction t generalizing Q h with
  | rw P b n =>
    dsimp only [FpTree.AllRWBounded]
    refine Classical.byContradiction fun hgt => ?_
    have hx : InRegion b n x := by unfold InRegion; have := (x - b).isLt; omega
    exact ownsRW_disjoint_sepConj (hv.ownsRW hx) hQ hh
  | ro _ _ _ => trivial
  | opaqueAtom _ => trivial
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    dsimp only [FpTree.interp] at hh
    have hh_l : (l.interp ∗ (r.interp ∗ Q)).holds h := sepConj_assoc l.interp r.interp Q ▸ hh
    have hh_r : (r.interp ∗ (l.interp ∗ Q)).holds h := by
      have h1 : l.interp ∗ r.interp = r.interp ∗ l.interp := sepConj_comm _ _
      have h2 : (l.interp ∗ r.interp) ∗ Q = r.interp ∗ (l.interp ∗ Q) := by
        rw [h1, sepConj_assoc]
      exact h2 ▸ hh
    exact ⟨ihl hvl (ownsRW_sepConj_right hQ) hh_l, ihr hvr (ownsRW_sepConj_right hQ) hh_r⟩

private theorem FpTree.allRWBounded_of_anchor
    {t : FpTree} {p₀ : FpPath} {b₀ : BitVec 64} {n₀ : Nat} {h : Heap}
    (hv : t.Valid) (hl : t.leafAt p₀ = some (true, b₀, n₀))
    (hn₀_pos : 0 < n₀) (hn₀_le : n₀ ≤ 2 ^ 64) (hh : t.interp.holds h) :
    t.AllRWBounded := by
  induction t generalizing p₀ h with
  | rw _ _ _ =>
    cases p₀ with
    | nil =>
      dsimp only [FpTree.leafAt, FpTree.AllRWBounded] at hl ⊢
      injection hl with h; injection h with _ hb; injection hb with _ hn
      subst hn; exact hn₀_le
    | cons _ _ => cases hl
  | ro _ _ _ => trivial
  | opaqueAtom _ => trivial
  | node l r ihl ihr =>
    rcases hv with ⟨hvl, hvr⟩
    rcases p₀ with _ | ⟨c, q⟩
    · cases hl
    dsimp only [FpTree.interp] at hh
    cases c
    · dsimp only [FpTree.leafAt] at hl
      obtain ⟨h₁, hh₁⟩ := SepProp.holds_sepConj_left hh
      have hb₀_in : InRegion b₀ n₀ b₀ := by unfold InRegion; rw [BitVec.sub_self]; exact hn₀_pos
      have hown_l : OwnsRW l.interp b₀ := FpTree.ownsAt_of_leafAt hvl hl hb₀_in
      have hh' : (r.interp ∗ l.interp).holds h := sepConj_comm l.interp r.interp ▸ hh
      exact ⟨ihl hvl hl hh₁, FpTree.allRWBounded_of_sep_ownsRW hvr hown_l hh'⟩
    · dsimp only [FpTree.leafAt] at hl
      have hh' : (r.interp ∗ l.interp).holds h := sepConj_comm l.interp r.interp ▸ hh
      obtain ⟨h₂, hh₂⟩ := SepProp.holds_sepConj_left hh'
      have hb₀_in : InRegion b₀ n₀ b₀ := by unfold InRegion; rw [BitVec.sub_self]; exact hn₀_pos
      have hown_r : OwnsRW r.interp b₀ := FpTree.ownsAt_of_leafAt hvr hl hb₀_in
      exact ⟨FpTree.allRWBounded_of_sep_ownsRW hvl hown_r hh, ihr hvr hl hh₂⟩

theorem FpTree.rwSum_le_of_pos_anchor_heap {t : FpTree} {p₀ : FpPath}
    {b₀ : BitVec 64} {n₀ : Nat} {h : Heap}
    (hv : t.Valid) (hl : t.leafAt p₀ = some (true, b₀, n₀))
    (hn₀_pos : 0 < n₀) (hn₀_le : n₀ ≤ 2 ^ 64) (hh : t.interp.holds h) :
    t.rwSum ≤ 2 ^ 64 :=
  FpTree.rwSum_le_of_allBounded_heap hv
    (FpTree.allRWBounded_of_anchor hv hl hn₀_pos hn₀_le hh) hh

theorem FpTree.rwSum_le_of_two_pos_heap {t : FpTree} {p₁ p₂ : FpPath}
    {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {h : Heap}
    (hv : t.Valid) (hdisj : FpPath.Disjoint p₁ p₂ = true)
    (hl₁ : t.leafAt p₁ = some (true, b₁, n₁))
    (hl₂ : t.leafAt p₂ = some (true, b₂, n₂))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hh : t.interp.holds h) :
    t.rwSum ≤ 2 ^ 64 := by
  have hn₁_le : n₁ ≤ 2 ^ 64 := by
    refine Classical.byContradiction fun hgt => ?_
    have hx₁ : InRegion b₁ n₁ b₂ := by unfold InRegion; have := (b₂ - b₁).isLt; omega
    have hx₂ : InRegion b₂ n₂ b₂ := by unfold InRegion; rw [BitVec.sub_self]; exact hn₂
    exact FpTree.disjoint_inRegion_heap hv hdisj rfl hl₁ hl₂ hh hx₁ hx₂
  exact FpTree.rwSum_le_of_pos_anchor_heap hv hl₁ hn₁ hn₁_le hh

theorem pointsToBytes_len_le_heap (b : BitVec 64) (bs : List (BitVec 8)) (h : Heap)
    (hh : (b ↦ₛ bs).holds h) : bs.length ≤ 2 ^ 64 := by
  cases bs with
  | nil => simp
  | cons w rest =>
    rw [pointsToBytes_cons] at hh
    refine Classical.byContradiction fun hgt => ?_
    have hrest : InRegion (b + 1#64) rest.length b := by
      unfold InRegion
      have := (b - (b + 1#64)).isLt
      simp only [List.length_cons] at hgt
      omega
    have hin1 : InRegion b 1 b := by unfold InRegion; rw [BitVec.sub_self]; decide
    exact ownsRW_disjoint_sepConj
      ((instHasFootprintPointsTo8 b w).ownsRW hin1)
      ((instHasFootprintPointsToBytes (b + 1#64) rest).ownsRW hrest) hh

theorem pointsToWords64_len_le_heap (a : BitVec 64) (ws : List (BitVec 64)) (h : Heap)
    (hh : (a ↦₆₄* ws).holds h) : 8 * ws.length ≤ 2 ^ 64 := by
  cases ws with
  | nil => simp
  | cons w rest =>
    rw [pointsToWords64_cons] at hh
    refine Classical.byContradiction fun hgt => ?_
    have hrest : InRegion (a + 8#64) (8 * rest.length) (a + 7#64) := by
      unfold InRegion
      have hlt : (a + 7#64 - (a + 8#64)).toNat = 2 ^ 64 - 1 := by bv_omega
      simp only [List.length_cons] at hgt
      omega
    have hin8 : InRegion a 8 (a + 7#64) := by
      unfold InRegion
      have hlt : (a + 7#64 - a).toNat = 7 := by bv_omega
      omega
    exact ownsRW_disjoint_sepConj
      ((instHasFootprintPointsTo64 a w).ownsRW hin8)
      ((instHasFootprintPointsToWords64 (a + 8#64) rest).ownsRW hrest) hh

/-! ### `Satisfies`, `Entails`, and `SepWP` Extraction Bridges -/

theorem FpTree.extract_of_satisfies {P : SepProp} {t : FpTree} {m : Memory} {φ : Prop}
    (heq : P = t.interp) (hm : m ⊨ P) (h : ∀ hp : Heap, t.interp.holds hp → φ) : φ := by
  rw [heq] at hm
  obtain ⟨hp, hhp, _⟩ := Satisfies.elim hm
  exact h hp hhp

theorem FpTree.extract_of_entails {P : SepProp} {t : FpTree} {φ : Prop}
    (heq : P = t.interp) (h : ∀ hp : Heap, t.interp.holds hp → φ) :
    P ⊢ ⌜φ⌝ ∗ P := by
  refine Entails.extract_heap_fact fun hp hhp => h hp ?_
  rwa [← heq]

theorem SepWP.extract_fact {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    {φ : Prop} (hφ : ∀ m : Memory, m ⊨ P → φ)
    (hk : φ → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.with_pre fun _ hm => hk (hφ s.mem (Satisfies.of_sep_left hm))

theorem holds_of_eq {P Q : SepProp} {hp : Heap} (heq : P = Q) (hh : P.holds hp) : Q.holds hp :=
  heq ▸ hh

theorem extract_holds_of_satisfies {P Q : SepProp} {m : Memory} {φ : Prop}
    (heq : P = Q) (hm : m ⊨ P) (hk : ∀ hp : Heap, Q.holds hp → φ) : φ := by
  rw [heq] at hm
  obtain ⟨hp, hhp, _⟩ := Satisfies.elim hm
  exact hk hp hhp

/-! ## 2. Named Dual Spatial Context (`Γ_□`, `Σ_∗`) & `SepDup` -/

/-- Semireducible named hypothesis tag: `isPers = true` marks a persistent duplicable hypothesis
    in `Γ_□` (`□ "name" : P`), and `isPers = false` marks a linear spatial hypothesis in `Σ_∗`
    (`∗ "name" : P`). Kept semireducible (not `@[reducible]`) so `simp` preserves labels while
    default-transparency `isDefEq` and kernel `rfl` see `sepHyp name isPers P ≡ P`. -/
@[expose] def sepHyp (_name : String) (_isPers : Bool) (P : SepProp) : SepProp := P

instance instHasFootprintSepHyp (nm : String) (isPers : Bool) (P : SepProp)
    (isRW : Bool) (b : BitVec 64) (n : Nat) [h : HasFootprint P isRW b n] :
    HasFootprint (sepHyp nm isPers P) isRW b n where
  owns_at := h.owns_at

/-- Duplicable persistent `SepProp` witness (`(P ∗ P) = P`), characterizing hypotheses eligible
    for `Γ_□` retention across framing without linear consumption. -/
class SepDup (P : SepProp) : Prop where
  dup_eq : (P ∗ P) = P

instance instSepDupEmp : SepDup emp where
  dup_eq := sepConj_emp emp

instance instSepDupPure (φ : Prop) : SepDup ⌜φ⌝ where
  dup_eq := by rw [pure_sepConj_pure, and_self]

instance instSepDupPointsTo8RO (a : BitVec 64) (v : BitVec 8) : SepDup (a ↦₈ᵣ v) where
  dup_eq := pointsTo8RO_dup a v

instance instSepDupPointsTo16RO (a : BitVec 64) (v : BitVec 16) : SepDup (a ↦₁₆ᵣ v) where
  dup_eq := pointsTo16RO_dup a v

instance instSepDupPointsTo32RO (a : BitVec 64) (v : BitVec 32) : SepDup (a ↦₃₂ᵣ v) where
  dup_eq := pointsTo32RO_dup a v

instance instSepDupPointsTo64RO (a : BitVec 64) (v : BitVec 64) : SepDup (a ↦₆₄ᵣ v) where
  dup_eq := pointsTo64RO_dup a v

instance instSepDupPointsTo128RO (a : BitVec 64) (v : BitVec 128) : SepDup (a ↦₁₂₈ᵣ v) where
  dup_eq := pointsTo128RO_dup a v

instance instSepDupPointsToBytesRO (a : BitVec 64) (bs : List (BitVec 8)) : SepDup (a ↦ᵣ bs) where
  dup_eq := pointsToBytesRO_dup a bs

instance instSepDupPointsToWords64RO (a : BitVec 64) (ws : List (BitVec 64)) :
    SepDup (a ↦₆₄ᵣ* ws) where
  dup_eq := pointsToWords64RO_dup a ws

instance instSepDupRegionBlockRO (b : BitVec 64) (n : Nat) (m : Memory) :
    SepDup (regionBlockRO b n m) where
  dup_eq := regionBlockRO_dup b n m

instance instSepDupSepConj (P Q : SepProp) [hP : SepDup P] [hQ : SepDup Q] : SepDup (P ∗ Q) where
  dup_eq := sepConj_dup hP.dup_eq hQ.dup_eq

instance instSepDupSepHyp (nm : String) (isPers : Bool) (P : SepProp) [h : SepDup P] :
    SepDup (sepHyp nm isPers P) where
  dup_eq := h.dup_eq

theorem sep_pull_next (A X R : SepProp) : A ∗ (X ∗ R) = X ∗ (A ∗ R) := by
  rw [← sepConj_assoc, sepConj_comm A X, sepConj_assoc]

theorem sep_pull_last (A X : SepProp) : A ∗ X = X ∗ A :=
  sepConj_comm A X

theorem sep_dup_head {P : SepProp} (h : SepDup P) (R : SepProp) : P ∗ R = P ∗ (P ∗ R) := by
  rw [← sepConj_assoc, h.dup_eq]

theorem sep_dup_single {P : SepProp} (h : SepDup P) : P = P ∗ P :=
  h.dup_eq.symm

theorem sep_emp_right_inv (P : SepProp) : P = P ∗ emp :=
  (sepConj_emp P).symm

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

theorem entails_cancel_head {P Q A₁ A₂ R S : SepProp}
    (hL : P = A₁ ∗ R) (hR : Q = A₂ ∗ S) (hEq : A₁ = A₂) (hSub : R ⊢ S) : P ⊢ Q := by
  rw [hL, hR, hEq]; exact sepConj_mono_right hSub

theorem entails_cancel_last {P Q A₁ A₂ : SepProp}
    (hL : P = A₁) (hR : Q = A₂) (hEq : A₁ = A₂) : P ⊢ Q := by
  rw [hL, hR, hEq]; exact Entails.refl A₂

theorem entails_cancel_emp_frame {P Q A₁ A₂ S : SepProp}
    (hL : P = A₁) (hR : Q = A₂ ∗ S) (hEq : A₁ = A₂) (hSub : emp ⊢ S) : P ⊢ Q := by
  have h1 : A₂ ⊢ A₂ ∗ S := by simpa [sepConj_emp] using sepConj_mono_right (P := A₂) hSub
  rwa [hL, hR, hEq]

/-! ## 3. Extensible Spatial LUB (`SepJoinLub`) & Diamond Branch-Join Combinators -/

/-- Extensible spatial least upper bound: witnesses that `P_join` reconciles `P_then`
    (under `cond = true`) and `P_else` (under `cond = false`). -/
class SepJoinLub (cond : Bool) (P_then P_else : SepProp) (P_join : outParam SepProp) : Prop where
  entails_then : cond = true → P_then ⊢ P_join
  entails_else : cond = false → P_else ⊢ P_join

theorem SepJoinLub.of_eq {cond : Bool} {P_then P_else P_then' P_else' P_join : SepProp}
    (hT : P_then = P_then') (hE : P_else = P_else')
    (h : SepJoinLub cond P_then' P_else' P_join) :
    SepJoinLub cond P_then P_else P_join where
  entails_then hc := hT ▸ h.entails_then hc
  entails_else hc := hE ▸ h.entails_else hc

theorem SepJoinLub.refl (cond : Bool) (P : SepProp) : SepJoinLub cond P P P where
  entails_then _ := Entails.refl P
  entails_else _ := Entails.refl P

theorem SepJoinLub.frame_right {cond : Bool} {D_t D_e D_j F : SepProp}
    (hD : SepJoinLub cond D_t D_e D_j) :
    SepJoinLub cond (D_t ∗ F) (D_e ∗ F) (D_j ∗ F) where
  entails_then hc := sepConj_mono_left (hD.entails_then hc)
  entails_else hc := sepConj_mono_left (hD.entails_else hc)

theorem SepJoinLub.sep {cond : Bool} {A_t A_e A_j B_t B_e B_j : SepProp}
    (hA : SepJoinLub cond A_t A_e A_j) (hB : SepJoinLub cond B_t B_e B_j) :
    SepJoinLub cond (A_t ∗ B_t) (A_e ∗ B_e) (A_j ∗ B_j) where
  entails_then hc := sepConj_mono (hA.entails_then hc) (hB.entails_then hc)
  entails_else hc := sepConj_mono (hA.entails_else hc) (hB.entails_else hc)

theorem SepJoinLub.emp_left_then {cond : Bool} {A_e A_j B_t B_e B_j : SepProp}
    (hA_t : cond = true → emp ⊢ A_j) (hA_e : cond = false → A_e ⊢ A_j)
    (hB : SepJoinLub cond B_t B_e B_j) :
    SepJoinLub cond B_t (A_e ∗ B_e) (A_j ∗ B_j) where
  entails_then hc := by
    rw [← emp_sepConj B_t]
    exact sepConj_mono (hA_t hc) (hB.entails_then hc)
  entails_else hc := sepConj_mono (hA_e hc) (hB.entails_else hc)

theorem SepJoinLub.emp_left_else {cond : Bool} {A_t A_j B_t B_e B_j : SepProp}
    (hA_t : cond = true → A_t ⊢ A_j) (hA_e : cond = false → emp ⊢ A_j)
    (hB : SepJoinLub cond B_t B_e B_j) :
    SepJoinLub cond (A_t ∗ B_t) B_e (A_j ∗ B_j) where
  entails_then hc := sepConj_mono (hA_t hc) (hB.entails_then hc)
  entails_else hc := by
    rw [← emp_sepConj B_e]
    exact sepConj_mono (hA_e hc) (hB.entails_else hc)

theorem SepJoinLub.mono_join {cond : Bool} {P_then P_else J₁ J₂ : SepProp}
    (h : SepJoinLub cond P_then P_else J₁) (hJ : J₁ ⊢ J₂) :
    SepJoinLub cond P_then P_else J₂ where
  entails_then hc := Entails.trans (h.entails_then hc) hJ
  entails_else hc := Entails.trans (h.entails_else hc) hJ

theorem sepJoinLub_and_pair {cond : Bool} {P_then P_else P_join : SepProp}
    (h : SepJoinLub cond P_then P_else P_join) :
    (cond = true → P_then ⊢ P_join) ∧ (cond = false → P_else ⊢ P_join) :=
  ⟨h.entails_then, h.entails_else⟩

/-- Existential value LUB across `f v₁` and `f v₂` (`∃∗ v, f v`). -/
theorem SepJoinLub.val_exists {α : Sort u} (cond : Bool) (f : α → SepProp) (v₁ v₂ : α) :
    SepJoinLub cond (f v₁) (f v₂) (∃∗ v : α, f v) where
  entails_then _ := Entails.sepExists_intro v₁
  entails_else _ := Entails.sepExists_intro v₂

theorem SepJoinLub.val_exists_left {α : Sort u} (cond : Bool) (f : α → SepProp) (v₁ : α) :
    SepJoinLub cond (f v₁) (∃∗ v : α, f v) (∃∗ v : α, f v) where
  entails_then _ := Entails.sepExists_intro v₁
  entails_else _ := Entails.refl _

theorem SepJoinLub.val_exists_right {α : Sort u} (cond : Bool) (f : α → SepProp) (v₂ : α) :
    SepJoinLub cond (∃∗ v : α, f v) (f v₂) (∃∗ v : α, f v) where
  entails_then _ := Entails.refl _
  entails_else _ := Entails.sepExists_intro v₂

/-- Conditional `ite` value LUB across `f v₁` and `f v₂` (`f (if cond then v₁ else v₂)`). -/
theorem SepJoinLub.val_ite {α : Type u} (cond : Bool) (f : α → SepProp) (v₁ v₂ : α) :
    SepJoinLub cond (f v₁) (f v₂) (f (if cond then v₁ else v₂)) where
  entails_then hc := by rw [hc]; simp only [↓reduceIte]; exact Entails.refl (f v₁)
  entails_else hc := by rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]; exact Entails.refl (f v₂)

/-! ### Built-in `SepJoinLub` Value-Existential Instances -/

instance instSepJoinLubPointsTo8 (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    SepJoinLub cond (a ↦₈ v₁) (a ↦₈ v₂) (∃∗ v : BitVec 8, a ↦₈ v) :=
  SepJoinLub.val_exists cond (a ↦₈ ·) v₁ v₂

instance instSepJoinLubPointsTo8ExR (cond : Bool) (a : BitVec 64) (v₁ : BitVec 8) :
    SepJoinLub cond (a ↦₈ v₁) (∃∗ v : BitVec 8, a ↦₈ v) (∃∗ v : BitVec 8, a ↦₈ v) :=
  SepJoinLub.val_exists_left cond (a ↦₈ ·) v₁

instance instSepJoinLubPointsTo8ExL (cond : Bool) (a : BitVec 64) (v₂ : BitVec 8) :
    SepJoinLub cond (∃∗ v : BitVec 8, a ↦₈ v) (a ↦₈ v₂) (∃∗ v : BitVec 8, a ↦₈ v) :=
  SepJoinLub.val_exists_right cond (a ↦₈ ·) v₂

instance instSepJoinLubPointsTo16 (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 16) :
    SepJoinLub cond (a ↦₁₆ v₁) (a ↦₁₆ v₂) (∃∗ v : BitVec 16, a ↦₁₆ v) :=
  SepJoinLub.val_exists cond (a ↦₁₆ ·) v₁ v₂

instance instSepJoinLubPointsTo16ExR (cond : Bool) (a : BitVec 64) (v₁ : BitVec 16) :
    SepJoinLub cond (a ↦₁₆ v₁) (∃∗ v : BitVec 16, a ↦₁₆ v) (∃∗ v : BitVec 16, a ↦₁₆ v) :=
  SepJoinLub.val_exists_left cond (a ↦₁₆ ·) v₁

instance instSepJoinLubPointsTo16ExL (cond : Bool) (a : BitVec 64) (v₂ : BitVec 16) :
    SepJoinLub cond (∃∗ v : BitVec 16, a ↦₁₆ v) (a ↦₁₆ v₂) (∃∗ v : BitVec 16, a ↦₁₆ v) :=
  SepJoinLub.val_exists_right cond (a ↦₁₆ ·) v₂

instance instSepJoinLubPointsTo32 (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 32) :
    SepJoinLub cond (a ↦₃₂ v₁) (a ↦₃₂ v₂) (∃∗ v : BitVec 32, a ↦₃₂ v) :=
  SepJoinLub.val_exists cond (a ↦₃₂ ·) v₁ v₂

instance instSepJoinLubPointsTo32ExR (cond : Bool) (a : BitVec 64) (v₁ : BitVec 32) :
    SepJoinLub cond (a ↦₃₂ v₁) (∃∗ v : BitVec 32, a ↦₃₂ v) (∃∗ v : BitVec 32, a ↦₃₂ v) :=
  SepJoinLub.val_exists_left cond (a ↦₃₂ ·) v₁

instance instSepJoinLubPointsTo32ExL (cond : Bool) (a : BitVec 64) (v₂ : BitVec 32) :
    SepJoinLub cond (∃∗ v : BitVec 32, a ↦₃₂ v) (a ↦₃₂ v₂) (∃∗ v : BitVec 32, a ↦₃₂ v) :=
  SepJoinLub.val_exists_right cond (a ↦₃₂ ·) v₂

instance instSepJoinLubPointsTo64 (cond : Bool) (a v₁ v₂ : BitVec 64) :
    SepJoinLub cond (a ↦₆₄ v₁) (a ↦₆₄ v₂) (∃∗ v : BitVec 64, a ↦₆₄ v) :=
  SepJoinLub.val_exists cond (a ↦₆₄ ·) v₁ v₂

instance instSepJoinLubPointsTo64ExR (cond : Bool) (a v₁ : BitVec 64) :
    SepJoinLub cond (a ↦₆₄ v₁) (∃∗ v : BitVec 64, a ↦₆₄ v) (∃∗ v : BitVec 64, a ↦₆₄ v) :=
  SepJoinLub.val_exists_left cond (a ↦₆₄ ·) v₁

instance instSepJoinLubPointsTo64ExL (cond : Bool) (a v₂ : BitVec 64) :
    SepJoinLub cond (∃∗ v : BitVec 64, a ↦₆₄ v) (a ↦₆₄ v₂) (∃∗ v : BitVec 64, a ↦₆₄ v) :=
  SepJoinLub.val_exists_right cond (a ↦₆₄ ·) v₂

instance instSepJoinLubPointsTo128 (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 128) :
    SepJoinLub cond (a ↦₁₂₈ v₁) (a ↦₁₂₈ v₂) (∃∗ v : BitVec 128, a ↦₁₂₈ v) :=
  SepJoinLub.val_exists cond (a ↦₁₂₈ ·) v₁ v₂

instance instSepJoinLubPointsTo128ExR (cond : Bool) (a : BitVec 64) (v₁ : BitVec 128) :
    SepJoinLub cond (a ↦₁₂₈ v₁) (∃∗ v : BitVec 128, a ↦₁₂₈ v) (∃∗ v : BitVec 128, a ↦₁₂₈ v) :=
  SepJoinLub.val_exists_left cond (a ↦₁₂₈ ·) v₁

instance instSepJoinLubPointsTo128ExL (cond : Bool) (a : BitVec 64) (v₂ : BitVec 128) :
    SepJoinLub cond (∃∗ v : BitVec 128, a ↦₁₂₈ v) (a ↦₁₂₈ v₂) (∃∗ v : BitVec 128, a ↦₁₂₈ v) :=
  SepJoinLub.val_exists_right cond (a ↦₁₂₈ ·) v₂

instance instSepJoinLubPointsTo8RO (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    SepJoinLub cond (a ↦₈ᵣ v₁) (a ↦₈ᵣ v₂) (∃∗ v : BitVec 8, a ↦₈ᵣ v) :=
  SepJoinLub.val_exists cond (a ↦₈ᵣ ·) v₁ v₂

instance instSepJoinLubPointsTo16RO (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 16) :
    SepJoinLub cond (a ↦₁₆ᵣ v₁) (a ↦₁₆ᵣ v₂) (∃∗ v : BitVec 16, a ↦₁₆ᵣ v) :=
  SepJoinLub.val_exists cond (a ↦₁₆ᵣ ·) v₁ v₂

instance instSepJoinLubPointsTo32RO (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 32) :
    SepJoinLub cond (a ↦₃₂ᵣ v₁) (a ↦₃₂ᵣ v₂) (∃∗ v : BitVec 32, a ↦₃₂ᵣ v) :=
  SepJoinLub.val_exists cond (a ↦₃₂ᵣ ·) v₁ v₂

instance instSepJoinLubPointsTo64RO (cond : Bool) (a v₁ v₂ : BitVec 64) :
    SepJoinLub cond (a ↦₆₄ᵣ v₁) (a ↦₆₄ᵣ v₂) (∃∗ v : BitVec 64, a ↦₆₄ᵣ v) :=
  SepJoinLub.val_exists cond (a ↦₆₄ᵣ ·) v₁ v₂

instance instSepJoinLubPointsTo128RO (cond : Bool) (a : BitVec 64) (v₁ v₂ : BitVec 128) :
    SepJoinLub cond (a ↦₁₂₈ᵣ v₁) (a ↦₁₂₈ᵣ v₂) (∃∗ v : BitVec 128, a ↦₁₂₈ᵣ v) :=
  SepJoinLub.val_exists cond (a ↦₁₂₈ᵣ ·) v₁ v₂

theorem lub_coalesce_then (cond : Bool) {C R : SepProp} (hC : C ⊢ R) :
    SepJoinLub cond C R R where
  entails_then _ := hC
  entails_else _ := Entails.refl R

theorem lub_coalesce_else (cond : Bool) {R C : SepProp} (hC : C ⊢ R) :
    SepJoinLub cond R C R where
  entails_then _ := Entails.refl R
  entails_else _ := hC

theorem lub_coalesce_both (cond : Bool) {C₁ C₂ R : SepProp} (h₁ : C₁ ⊢ R) (h₂ : C₂ ⊢ R) :
    SepJoinLub cond C₁ C₂ R where
  entails_then _ := h₁
  entails_else _ := h₂

theorem memRegion_coalesce {b₁ b₂ : BitVec 64} {n₁ n₂ N : Nat} {P₁ P₂ : SepProp}
    (h₁ : P₁ ⊢ memRegion b₁ n₁) (h₂ : P₂ ⊢ memRegion b₂ n₂)
    (hb : b₂ = b₁ + BitVec.ofNat 64 n₁) (hN : N = n₁ + n₂) (hle : N ≤ 2 ^ 64) :
    P₁ ∗ P₂ ⊢ memRegion b₁ N := by
  rw [ProofLib.memRegion_split' hN hb hle]
  exact sepConj_mono h₁ h₂

theorem pointsToWords64_entails_memRegion_of_len {a : BitVec 64} {ws : List (BitVec 64)}
    {n : Nat} (hlen : 8 * ws.length = n) (hle : n ≤ 2 ^ 64) :
    (a ↦₆₄* ws) ⊢ memRegion a n := by
  subst hlen
  exact pointsToWords64_entails_memRegion ws a hle

theorem cells_entails_memRegion (a : BitVec 64) (k : Nat) (hk : 8 * k ≤ 2 ^ 64) :
    ProofLib.cells a k ⊢ memRegion a (8 * k) := by
  rw [← memRegion_cells a k hk]; exact Entails.refl _

theorem stackFrameAt_entails_memRegion (sp : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    stackFrameAt sp n ⊢ memRegion (sp - BitVec.ofNat 64 n) n := by
  rw [stackFrameAt_eq_memRegion sp n hn]; exact Entails.refl _

theorem stackFrame16At_entails_memRegion (sp : BitVec 64) :
    stackFrame16At sp ⊢ memRegion (sp - 16#64) 16 := by
  have h := stackFrameAt_entails_memRegion sp 16 (by decide)
  have heq : stackFrame16At sp = stackFrameAt sp 16 := by
    rw [stackFrame16At_def]
    unfold stackFrameAt stackFrameSlotsFrom stackFrameSlotsCont
    rfl
  rwa [heq]

theorem stackFrame32At_entails_memRegion (sp : BitVec 64) :
    stackFrame32At sp ⊢ memRegion (sp - 32#64) 32 := by
  have h := stackFrameAt_entails_memRegion sp 32 (by decide)
  have heq : stackFrame32At sp = stackFrameAt sp 32 := by
    rw [stackFrame32At_def]
    unfold stackFrameAt stackFrameSlotsFrom stackFrameSlotsCont
    simp only [↓reduceIte, beq_iff_eq, Nat.reduceBEq, Bool.false_eq_true]
    rfl
  rwa [heq]

theorem cells_entails_memRegion_of_len {a : BitVec 64} {k n : Nat}
    (hn : 8 * k = n) (hle : n ≤ 2 ^ 64) :
    ProofLib.cells a k ⊢ memRegion a n := by
  subst hn; exact cells_entails_memRegion a k hle

/-- `SepWP` diamond branch-and-join combinator backed by `SepJoinLub`: neither branch nor the
    caller restates untouched frame atoms (`P_join` is synthesized automatically by `sep_join_lub`). -/
theorem SepWP.ite_join_lub {prog : Program} {pc_join target_pc : BitVec 64}
    (J : Arm64.State → Prop) {P_then P_else P_join : SepProp}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    {cond : Bool} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = if cond then pc1 else pc2)
    (hthen : cond = true → SepWP prog pc_join (s.setPC pc1) P (sepPost J P_then) oom)
    (helse : cond = false → SepWP prog pc_join (s.setPC pc2) P (sepPost J P_else) oom)
    (hlub : SepJoinLub cond P_then P_else P_join)
    (hjoin : ∀ sj : Arm64.State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj P_join post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.ite_join J P_join hpc
    (fun hc => SepWP.mono (hthen hc)
      (fun sf P_f _ _ h => sepPost_mono (fun _ hJ => hJ) (hlub.entails_then hc) sf P_f h))
    (fun hnc => SepWP.mono (helse (Bool.eq_false_iff.mpr hnc))
      (fun sf P_f _ _ h =>
        sepPost_mono (fun _ hJ => hJ) (hlub.entails_else (Bool.eq_false_iff.mpr hnc)) sf P_f h))
    hjoin

end

public meta section

open Lean Elab Tactic Term Command Meta PrettyPrinter Delaborator SubExpr

/-! ## 1B. Global `@[sep_footprint]` Elaborators & Balanced `FpTree` Disjointness Tactic -/

/-- Register one or more `HasFootprint` theorems for discovery by `sep_disjoint` and `wp_disjoint`. -/
elab "register_sep_footprint " ids:(ppSpace ident)+ : command => do
  for id in ids do
    let declName ← Elab.Command.liftCoreM (Elab.realizeGlobalConstNoOverloadWithInfo id)
    let instId := mkIdent (Name.mkSimple s!"_sepFootprintRule_{declName.mangle}")
    let qName : Term := quote declName
    Elab.Command.elabCommand (← `(command|
      instance $instId:ident : _root_.ProofLib.Sep.SepFootprintRule $qName := ⟨True.intro⟩))

/-- Declare and register a parameterized `HasFootprint` theorem in one step. -/
elab "@[sep_footprint]" "theorem " id:ident sig:declSig val:declVal : command => do
  Elab.Command.elabCommand (← `(command| theorem $id $sig $val))
  Elab.Command.elabCommand (← `(command| register_sep_footprint $id))

/-- Balanced `∗` tree node tracking leaf index, sub-expression, and binary `FpPath`. -/
inductive BalNode where
  | leaf (idx : Nat) (atom : Expr) (path : FpPath)
  | node (expr : Expr) (l r : BalNode)

def BalNode.expr : BalNode → Expr
  | .leaf _ atom _ => atom
  | .node expr _ _ => expr

partial def BalNode.collectLeaves (b : BalNode) (acc : Array (Nat × Expr × FpPath) := #[]) :
    Array (Nat × Expr × FpPath) :=
  match b with
  | .leaf idx atom path => acc.push (idx, atom, path)
  | .node _ l r => r.collectLeaves (l.collectLeaves acc)

def mkSepExpr (a b : Expr) : Expr :=
  mkApp2 (mkConst ``SepProp.sepConj) a b

def mkEqTransOpt (p1? p2? : Option Expr) : MetaM (Option Expr) := do
  match p1?, p2? with
  | none, none => return none
  | some p1, none => return some p1
  | none, some p2 => return some p2
  | some p1, some p2 => return some (← mkEqTrans p1 p2)

/-- Unpacks `sepHyp name isPers inner` if `e` is a named hypothesis. -/
def unpackSepHyp? (e : Expr) : Option (String × Bool × Expr) :=
  let ec := e.consumeMData
  if ec.isAppOfArity ``sepHyp 3 then
    let nm? := match ec.getArg! 0 with
      | .lit (.strVal s) => some s
      | _ => none
    let pers? :=
      let p := (ec.getArg! 1).consumeMData
      if p.isConstOf ``Bool.true then some true
      else if p.isConstOf ``Bool.false then some false
      else none
    match nm?, pers? with
    | some nm, some isPers => some (nm, isPers, ec.getArg! 2)
    | _, _ => none
  else none

partial def stripSepHyp (e : Expr) : Expr :=
  match unpackSepHyp? e with
  | some (_, _, inner) => stripSepHyp inner
  | none => e

/-- Right-associates `lhs ∗ rhs` using only `Arm64.sepConj_assoc` in $O(|lhs|)$ steps. -/
partial def prependRightSpine (lhs rhs : Expr) : MetaM (Expr × Option Expr × Nat) := do
  let lc0 := lhs.consumeMData
  let lc ← if lc0.isAppOfArity ``SepProp.sepConj 2 then pure lc0 else do
    let lw ← withReducible (whnf lc0)
    pure (if lw.isAppOfArity ``SepProp.sepConj 2 then lw else lc0)
  if lc.isAppOfArity ``SepProp.sepConj 2 then
    let a := lc.getArg! 0
    let b := lc.getArg! 1
    let assocPrf := mkApp3 (mkConst ``Arm64.sepConj_assoc) a b rhs
    let (br, pBR?, cB) ← prependRightSpine b rhs
    let p1 ← match pBR? with
      | none => pure assocPrf
      | some pBR => mkEqTrans assocPrf (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) a) pBR)
    let (abr, pABR?, cA) ← prependRightSpine a br
    let pTot ← match pABR? with
      | none => pure p1
      | some pABR => mkEqTrans p1 pABR
    return (abr, some pTot, cA + cB)
  else
    return (mkSepExpr lhs rhs, none, 1)

/-- Converts an arbitrary `∗` tree `e` into a right-nested spine in $O(N)$ associative steps. -/
partial def toRightSpine (e : Expr) : MetaM (Expr × Option Expr × Nat) := do
  let ec0 := e.consumeMData
  let ec ← if ec0.isAppOfArity ``SepProp.sepConj 2 then pure ec0 else do
    let ew ← withReducible (whnf ec0)
    pure (if ew.isAppOfArity ``SepProp.sepConj 2 then ew else ec0)
  if ec.isAppOfArity ``SepProp.sepConj 2 then
    let l := ec.getArg! 0
    let r := ec.getArg! 1
    let (rSpine, pR?, cR) ← toRightSpine r
    let pStep1? ← match pR? with
      | none => pure none
      | some pR => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) l) pR))
    let (fullSpine, pLR?, cL) ← prependRightSpine l rSpine
    let pTot? ← mkEqTransOpt pStep1? pLR?
    return (fullSpine, pTot?, cL + cR)
  else
    return (e, none, 1)

/-- Splits the first `k ≥ 1` atoms off a right spine `s` into a balanced tree `t` and remainder `rem`
    with proof `s = t.expr ∗ rem` via `sepConj_assoc.symm`. -/
partial def splitSpineBalanced (startIdx : Nat) (pfxRev : FpPath) (k : Nat) (s : Expr) :
    MetaM (BalNode × Expr × Option Expr) := do
  if k ≤ 1 then
    let sc := s.consumeMData
    return (.leaf startIdx (sc.getArg! 0) pfxRev.reverse, sc.getArg! 1, none)
  else
    let k1 := k / 2
    let k2 := k - k1
    let (t1, s1, p1?) ← splitSpineBalanced startIdx (false :: pfxRev) k1 s
    let (t2, rem, p2?) ← splitSpineBalanced (startIdx + k1) (true :: pfxRev) k2 s1
    let pStep2? ← match p2? with
      | none => pure none
      | some p2 => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) t1.expr) p2))
    let p12? ← mkEqTransOpt p1? pStep2?
    let assocSymm ← mkEqSymm (mkApp3 (mkConst ``Arm64.sepConj_assoc) t1.expr t2.expr rem)
    let pTot ← match p12? with
      | none => pure assocSymm
      | some p12 => mkEqTrans p12 assocSymm
    let nodeE := mkSepExpr t1.expr t2.expr
    return (.node nodeE t1 t2, rem, some pTot)

/-- Balances a right spine `s` of `k ≥ 1` atoms into a height-$\lceil \log_2 k \rceil$ `BalNode`. -/
partial def buildFullBalanced (startIdx : Nat) (pfxRev : FpPath) (k : Nat) (s : Expr) :
    MetaM (BalNode × Option Expr) := do
  if k ≤ 1 then
    return (.leaf startIdx s pfxRev.reverse, none)
  else
    let k1 := k / 2
    let k2 := k - k1
    let (t1, s1, p1?) ← splitSpineBalanced startIdx (false :: pfxRev) k1 s
    let (t2, p2?) ← buildFullBalanced (startIdx + k1) (true :: pfxRev) k2 s1
    let pStep2? ← match p2? with
      | none => pure none
      | some p2 => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) t1.expr) p2))
    let pTot? ← mkEqTransOpt p1? pStep2?
    let nodeE := mkSepExpr t1.expr t2.expr
    return (.node nodeE t1 t2, pTot?)

/-- Rebalances any `SepProp` expression `e` into `(balTree, prf : e = balTree.expr)` using
    at most $2N$ applications of `sepConj_assoc` and zero `ac_rfl`. -/
def rebalanceSepExpr (e : Expr) : MetaM (BalNode × Expr) := do
  let (spine, pSpine?, count) ← toRightSpine e
  let (bal, pBal?) ← buildFullBalanced 0 [] count spine
  let pTot? ← mkEqTransOpt pSpine? pBal?
  let prf ← match pTot? with
    | some p => pure p
    | none => mkEqRefl e
  return (bal, prf)

/-- Resolved spatial footprint of a leaf atom in `BalNode`. -/
structure LeafFootprint where
  leafIdx : Nat
  path    : FpPath
  atom    : Expr
  isRW    : Bool
  base    : Expr
  len     : Expr
  instPrf : Expr
  deriving Inhabited

/-- Attempts to discharge a pure side-condition (`0 < n`, `n ≤ 2 ^ 64`, `InRegion ...`) with minimal
    kernel proof size (`of_decide_eq_true rfl` / `le_two_pow_64_of_ble` first, then `omega` / `bv_omega`). -/
def proveSideProp (ty : Expr) : TacticM (Option Expr) := do
  let tyC := (← instantiateMVars ty).consumeMData
  if tyC.isAppOfArity ``LE.le 4 then
    let lhs := tyC.getArg! 2
    let rhs := (tyC.getArg! 3).consumeMData
    if rhs.isAppOfArity ``HPow.hPow 6 then
      if (← evalClosedNat? (rhs.getArg! 4)) == some 2 &&
         (← evalClosedNat? (rhs.getArg! 5)) == some 64 then
        if let some n ← evalClosedNat? lhs then
          if n ≤ (1 <<< 64) then
            let p := mkApp2 (mkConst ``le_two_pow_64_of_ble) lhs rflTrueExpr
            return some (← mkExpectedTypeHint p tyC)
  let saved ← saveState
  try
    let m ← mkFreshExprMVar tyC
    let rem ← evalTacticAt
      (← `(tactic| first | exact of_decide_eq_true rfl | omega | bv_omega | (unfold InRegion; bv_omega)))
      m.mvarId!
    if rem.isEmpty then
      return some (← instantiateMVars m)
    restoreState saved
    return none
  catch _ =>
    restoreState saved
    return none

private partial def extractNameExpr? (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e.consumeMData
  if e.isConstOf ``Name.anonymous then return some .anonymous
  else if e.isAppOfArity ``Name.str 2 then
    match ← extractNameExpr? (e.getArg! 0), (← whnf (e.getArg! 1)).consumeMData with
    | some p, .lit (.strVal s) => return some (.str p s)
    | _, _ => return none
  else if e.isAppOfArity ``Name.num 2 then
    match ← extractNameExpr? (e.getArg! 0), (← whnf (e.getArg! 1)).consumeMData.rawNatLit? with
    | some p, some n => return some (.num p n)
    | _, _ => return none
  else return none

private def extractBoolConst? (e : Expr) : MetaM (Option Bool) := do
  let ew ← whnf (← instantiateMVars e)
  if ew.isConstOf ``Bool.true then return some true
  if ew.isConstOf ``Bool.false then return some false
  return none

/-- Resolves all `HasFootprint` witnesses for `atom` via typeclass synthesis and `@[sep_footprint]`
    lemmas (including parameterized membership rules matched against local hypotheses). -/
def resolveLeafFootprints (idx : Nat) (path : FpPath) (atom : Expr) :
    TacticM (Array LeafFootprint) := do
  let mut out : Array LeafFootprint := #[]
  -- 1. Typeclass synthesis (`HasFootprint atom ?rw ?b ?n`)
  let savedTc ← saveState
  let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
  let rwM ← mkFreshExprMVar (mkConst ``Bool)
  let bM ← mkFreshExprMVar bv64Ty
  let nM ← mkFreshExprMVar (mkConst ``Nat)
  let cls := mkApp4 (mkConst ``HasFootprint) atom rwM bM nM
  if let .some inst ← trySynthInstance cls then
    if let some isRW ← extractBoolConst? rwM then
      out := out.push {
        leafIdx := idx, path, atom, isRW
        base := ← instantiateMVars bM
        len := ← instantiateMVars nM
        instPrf := ← instantiateMVars inst
      }
    else
      restoreState savedTc
  else
    restoreState savedTc
  -- 2. Registered `[sep_footprint]` lemmas (queried via `SepFootprintRule` instances)
  let insts ← getGlobalInstancesIndex
  let nmPat ← mkFreshExprMVar (mkConst ``Name)
  let ruleEntries ← insts.getUnify (mkApp (mkConst ``SepFootprintRule) nmPat)
  let mut entries : Array Name := #[]
  for entry in ruleEntries do
    let ity ← inferType entry.val
    if ity.isAppOfArity ``SepFootprintRule 1 then
      if let some nm ← extractNameExpr? (ity.getArg! 0) then
        entries := entries.push nm
  let lctx ← getLCtx
  let rawAtom := stripSepHyp atom
  for declName in entries do
    let savedEntry ← saveState
    try
      let fn ← mkConstWithFreshMVarLevels declName
      let (mvars, bis, concl) ← forallMetaTelescopeReducing (← inferType fn)
      if concl.isAppOfArity ``HasFootprint 4 then
        let pat := concl.getArg! 0
        if ← isDefEq pat rawAtom then
          for i in [:mvars.size] do
            if bis[i]! == .instImplicit && !(← mvars[i]!.mvarId!.isAssigned) then
              if let .some tc ← trySynthInstance (← inferType mvars[i]!) then
                mvars[i]!.mvarId!.assign tc
          let mut unassigned : Array Expr := #[]
          for mv in mvars do
            if !(← mv.mvarId!.isAssigned) then
              unassigned := unassigned.push mv
          if unassigned.isEmpty then
            if let some isRW ← extractBoolConst? (concl.getArg! 1) then
              out := out.push {
                leafIdx := idx, path, atom, isRW
                base := ← instantiateMVars (concl.getArg! 2)
                len := ← instantiateMVars (concl.getArg! 3)
                instPrf := ← instantiateMVars (mkAppN fn mvars)
              }
          else
            let mut propMVar? : Option Expr := none
            for mv in unassigned do
              if propMVar?.isNone then
                if ← Meta.isProp (← instantiateMVars (← inferType mv)) then
                  propMVar? := some mv
            let m0 := propMVar?.getD unassigned[0]!
            let m0Ty ← instantiateMVars (← inferType m0)
            for ldecl in lctx do
              if !ldecl.isImplementationDetail && !ldecl.isAuxDecl then
                let sHyp ← saveState
                if ← isDefEq m0Ty ldecl.type then
                  m0.mvarId!.assign ldecl.toExpr
                  let mut allClosed := true
                  for mk in unassigned do
                    if !(← mk.mvarId!.isAssigned) then
                      if let some p ← proveSideProp (← instantiateMVars (← inferType mk)) then
                        mk.mvarId!.assign p
                      else
                        allClosed := false
                  if allClosed then
                    if let some isRW ← extractBoolConst? (concl.getArg! 1) then
                      let prf ← instantiateMVars (mkAppN fn mvars)
                      if !prf.hasMVar then
                        out := out.push {
                          leafIdx := idx, path, atom, isRW
                          base := ← instantiateMVars (concl.getArg! 2)
                          len := ← instantiateMVars (concl.getArg! 3)
                          instPrf := prf
                        }
                restoreState sHyp
    catch _ => pure ()
    restoreState savedEntry
  return out

def resolveAllFootprints (bal : BalNode) : TacticM (Array LeafFootprint) := do
  let mut acc : Array LeafFootprint := #[]
  for (idx, atom, path) in bal.collectLeaves do
    let fps ← resolveLeafFootprints idx path atom
    acc := acc ++ fps
  return acc

partial def BalNode.hasSelected (b : BalNode) (sel : Nat → Option LeafFootprint) : Bool :=
  match b with
  | .leaf idx _ _ => (sel idx).isSome
  | .node _ l r => l.hasSelected sel || r.hasSelected sel

/-- Builds a pruned `FpTree` expanding ONLY paths to `sel` leaves and wrapping untouched subtrees
    in `FpTree.opaqueAtom` so `t.interp` is definitionally equal (`rfl`) to `b.expr` with $O(\log N)$ size. -/
partial def buildPrunedFpTree (b : BalNode) (sel : Nat → Option LeafFootprint) :
    MetaM (Expr × Expr × Expr) := do
  if !b.hasSelected sel then
    return (mkApp (mkConst ``FpTree.opaqueAtom) b.expr, mkConst ``True.intro, toExpr (0 : Nat))
  match b with
  | .leaf idx _ _ =>
    let some fp := sel idx | unreachable!
    if fp.isRW then
      return (mkApp3 (mkConst ``FpTree.rw) fp.atom fp.base fp.len, fp.instPrf, fp.len)
    else
      return (mkApp3 (mkConst ``FpTree.ro) fp.atom fp.base fp.len, fp.instPrf, toExpr (0 : Nat))
  | .node _ l r =>
    let (tl, vl, sl) ← buildPrunedFpTree l sel
    let (tr, vr, sr) ← buildPrunedFpTree r sel
    let tE := mkApp2 (mkConst ``FpTree.node) tl tr
    let vP := mkApp4 (mkConst ``And.intro)
      (mkApp (mkConst ``FpTree.Valid) tl) (mkApp (mkConst ``FpTree.Valid) tr) vl vr
    let sE ← mkAppM ``HAdd.hAdd #[sl, sr]
    return (tE, vP, sE)

/-- Builds a proof of `t.HoldsBounded` when every `.rw` leaf in `t` has an unconditional or
    heap-conditional `len ≤ 2 ^ 64` proof. -/
private partial def buildHoldsBoundedPrf? (b : BalNode) (sel : Nat → Option LeafFootprint)
    (twoPow64 : Expr) : TacticM (Option Expr) := do
  if !b.hasSelected sel then
    return some (mkConst ``True.intro)
  match b with
  | .leaf idx _ _ =>
    let some fp := sel idx | return none
    if !fp.isRW then
      return some (mkConst ``True.intro)
    let raw := (stripSepHyp fp.atom).consumeMData
    if raw.isAppOfArity ``Arm64.pointsToBytes 2 then
      return some (mkApp2 (mkConst ``pointsToBytes_len_le_heap) (raw.getArg! 0) (raw.getArg! 1))
    if raw.isAppOfArity ``Arm64.pointsToWords64 2 then
      return some (mkApp2 (mkConst ``pointsToWords64_len_le_heap) (raw.getArg! 0) (raw.getArg! 1))
    let bndTy ← mkAppM ``LE.le #[fp.len, twoPow64]
    let some hnLe ← proveSideProp bndTy | return none
    let hpTy : Expr := Lean.mkConst ``Heap
    let holdsTy := mkApp2 (Lean.mkConst ``SepProp.holds) fp.atom (.bvar 0)
    return some (mkLambda `hp .default hpTy (mkLambda `hh .default holdsTy hnLe))
  | .node _ l r =>
    let some pl ← buildHoldsBoundedPrf? l sel twoPow64 | return none
    let some pr ← buildHoldsBoundedPrf? r sel twoPow64 | return none
    let (tl, _, _) ← buildPrunedFpTree l sel
    let (tr, _, _) ← buildPrunedFpTree r sel
    return some (mkApp4 (mkConst ``And.intro)
      (mkApp (mkConst ``FpTree.HoldsBounded) tl) (mkApp (mkConst ``FpTree.HoldsBounded) tr) pl pr)

private def mkLeafSomeRfl (rwE bE nE : Expr) : MetaM Expr := do
  let inner ← mkAppM ``Prod.mk #[bE, nE]
  let tup ← mkAppM ``Prod.mk #[rwE, inner]
  let someE ← mkAppM ``Option.some #[tup]
  mkEqRefl someE

private def mkPairPruned (bal : BalNode) (fp1 fp2 : LeafFootprint) :
    MetaM (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) := do
  let sel (i : Nat) : Option LeafFootprint :=
    if i == fp1.leafIdx then some fp1 else if i == fp2.leafIdx then some fp2 else none
  let (tE, hvPrf, _) ← buildPrunedFpTree bal sel
  let p1E := toExpr fp1.path
  let p2E := toExpr fp2.path
  let rw1E := toExpr fp1.isRW
  let rw2E := toExpr fp2.isRW
  let hl1Rfl ← mkLeafSomeRfl rw1E fp1.base fp1.len
  let hl2Rfl ← mkLeafSomeRfl rw2E fp2.base fp2.len
  return (tE, p1E, p2E, rw1E, rw2E, hvPrf, rflTrueExpr, hl1Rfl, hl2Rfl)

private def defEqMatch (e1 e2 : Expr) : MetaM Bool := do
  if e1 == e2 then return true
  let s ← saveState
  let ok ← withReducibleAndInstances (isDefEq e1 e2)
  if !ok then restoreState s
  return ok

/-- Discharges a pure disjointness, region-exclusion, membership-exclusion, or address-space
    pigeonhole goal from an already-rebalanced spatial tree `bal` (`hhpBal : bal.expr.holds hp`). -/
partial def provePureGoalWithBal (bal : BalNode) (hhpBal : Expr) (goalMVar : MVarId) :
    TacticM Bool := goalMVar.withContext do
  let goalTy := (← instantiateMVars (← goalMVar.getType)).consumeMData
  -- 1. Conjunction `φ₁ ∧ φ₂` (reusing the same balanced tree `bal`)
  if goalTy.isAppOfArity ``And 2 then
    let saved ← saveState
    let [g1, g2] ← goalMVar.apply (mkConst ``And.intro) | do restoreState saved; return false
    if (← provePureGoalWithBal bal hhpBal g1) && (← provePureGoalWithBal bal hhpBal g2) then
      return true
    restoreState saved
    return false
  let fps ← resolveAllFootprints bal
  let ctx ← collectCtxFacts
  let addrCacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
  let zeroE := toExpr (0 : Nat)
  let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
  -- 2. Pointer inequality `a ≠ b` (or `a = b → False`)
  let neArgs? : Option (Expr × Expr) ← do
    if goalTy.isAppOfArity ``Ne 3 then
      if ← defEqMatch (goalTy.getArg! 0) bv64Ty then
        pure (some (goalTy.getArg! 1, goalTy.getArg! 2))
      else pure none
    else if goalTy.isAppOfArity ``Not 1 && (goalTy.getArg! 0).consumeMData.isAppOfArity ``Eq 3 then
      let eqE := (goalTy.getArg! 0).consumeMData
      if ← defEqMatch (eqE.getArg! 0) bv64Ty then
        pure (some (eqE.getArg! 1, eqE.getArg! 2))
      else pure none
    else pure none
  if let some (a, b) := neArgs? then
    -- Fast path 2A: exact defeq base match
    for fp1 in fps do
      if ← defEqMatch fp1.base a then
        for fp2 in fps do
          if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
            if ← defEqMatch fp2.base b then
              if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp1.len]) then
                if let some hn2 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp2.len]) then
                  let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                    mkPairPruned bal fp1 fp2
                  let prf ← mkAppOptM ``FpTree.ne_heap #[
                    some tE, some p1E, some p2E, some rw1E, some rw2E,
                    some a, some b, some fp1.len, some fp2.len, none,
                    some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                    some hn1, some hhpBal, some hn2]
                  goalMVar.assign prf
                  return true
    -- Fast path 2B: canonicalized address base match (`proveAddrEqFast?`)
    for fp1 in fps do
      if let some hEqA ← proveAddrEqFast? ctx addrCacheRef fp1.base a then
        for fp2 in fps do
          if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
            if let some hEqB ← proveAddrEqFast? ctx addrCacheRef fp2.base b then
              if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp1.len]) then
                if let some hn2 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp2.len]) then
                  let (heqFVar, gFalse) ← goalMVar.intro1P
                  gFalse.withContext do
                    let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                      mkPairPruned bal fp1 fp2
                    let hne ← mkAppOptM ``FpTree.ne_heap #[
                      some tE, some p1E, some p2E, some rw1E, some rw2E,
                      some fp1.base, some fp2.base, some fp1.len, some fp2.len, none,
                      some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                      some hn1, some hhpBal, some hn2]
                    let pChain ← mkEqTrans (← mkEqTrans hEqA (mkFVar heqFVar)) (← mkEqSymm hEqB)
                    gFalse.assign (mkApp hne pChain)
                  return true
    -- Path 2C: interior-offset path (`InRegion b₁ n₁ a` and `InRegion b₂ n₂ b`)
    let (rootA, _) := peelAddrRoot ctx.letVals a
    let (rootB, _) := peelAddrRoot ctx.letVals b
    for fp1 in fps do
      let (r1, _) := peelAddrRoot ctx.letVals fp1.base
      if r1 == rootA || !r1.isFVar || !rootA.isFVar || !ctx.bvEqs.isEmpty then
        if let some hx1 ← proveSideProp (mkApp3 (mkConst ``InRegion) fp1.base fp1.len a) then
          for fp2 in fps do
            if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
              let (r2, _) := peelAddrRoot ctx.letVals fp2.base
              if r2 == rootB || !r2.isFVar || !rootB.isFVar || !ctx.bvEqs.isEmpty then
                if let some hx2 ← proveSideProp (mkApp3 (mkConst ``InRegion) fp2.base fp2.len b) then
                  let (heqFVar, gFalse) ← goalMVar.intro1P
                  gFalse.withContext do
                    let inRegFn := mkApp2 (mkConst ``InRegion) fp1.base fp1.len
                    let hx1b ← mkEqMP (← mkCongrArg inRegFn (mkFVar heqFVar)) hx1
                    let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                      mkPairPruned bal fp1 fp2
                    let prf ← mkAppOptM ``FpTree.disjoint_inRegion_heap #[
                      some tE, some p1E, some p2E, some rw1E, some rw2E,
                      some fp1.base, some fp2.base, some fp1.len, some fp2.len, none, some b,
                      some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                      some hhpBal, some hx1b, some hx2]
                    gFalse.assign prf
                  return true
  -- 3. `OutsideRegion regBase regLen pt`
  if goalTy.isAppOfArity ``OutsideRegion 3 then
    let regBase := goalTy.getArg! 0
    let regLen := goalTy.getArg! 1
    let pt := goalTy.getArg! 2
    for fp1 in fps do
      if ← defEqMatch fp1.base pt then
        for fp2 in fps do
          if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
            if (← defEqMatch fp2.base regBase) && (← defEqMatch fp2.len regLen) then
              if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp1.len]) then
                let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                  mkPairPruned bal fp1 fp2
                let prf ← mkAppOptM ``FpTree.outsideRegion_heap #[
                  some tE, some p1E, some p2E, some rw1E, some rw2E,
                  some pt, some regBase, some fp1.len, some regLen, none,
                  some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                  some hn1, some hhpBal]
                goalMVar.assign prf
                return true
    for fp2 in fps do
      if (← defEqMatch fp2.base regBase) && (← defEqMatch fp2.len regLen) then
        for fp1 in fps do
          if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
            if let some hpt ← proveSideProp (mkApp3 (mkConst ``InRegion) fp1.base fp1.len pt) then
              let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                mkPairPruned bal fp1 fp2
              let prf ← mkAppOptM ``FpTree.outsideRegion_of_inRegion_heap #[
                some tE, some p1E, some p2E, some rw1E, some rw2E,
                some fp1.base, some regBase, some pt, some fp1.len, some regLen, none,
                some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                some hpt, some hhpBal]
              goalMVar.assign prf
              return true
  -- 4. `DisjointRegions b1 n1 b2 n2`
  if goalTy.isAppOfArity ``DisjointRegions 4 then
    let b1 := goalTy.getArg! 0
    let n1 := goalTy.getArg! 1
    let b2 := goalTy.getArg! 2
    let n2 := goalTy.getArg! 3
    for fp1 in fps do
      if (← defEqMatch fp1.base b1) && (← defEqMatch fp1.len n1) then
        for fp2 in fps do
          if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
            if (← defEqMatch fp2.base b2) && (← defEqMatch fp2.len n2) then
              if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, n1]) then
                if let some hn2 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, n2]) then
                  let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                    mkPairPruned bal fp1 fp2
                  let prf ← mkAppOptM ``FpTree.disjointRegions_heap #[
                    some tE, some p1E, some p2E, some rw1E, some rw2E,
                    some b1, some b2, some n1, some n2, none,
                    some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                    some hn1, some hn2, some hhpBal]
                  goalMVar.assign prf
                  return true
  -- 5. Interval non-wrapping disjunction `b1.toNat + n1 ≤ b2.toNat ∨ b2.toNat + n2 ≤ b1.toNat`
  if goalTy.isAppOfArity ``Or 2 then
    for fp1 in fps do
      for fp2 in fps do
        if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
          let candTy ← mkAppM ``Or #[
            ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[fp1.base], fp1.len],
              ← mkAppM ``BitVec.toNat #[fp2.base]],
            ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[fp2.base], fp2.len],
              ← mkAppM ``BitVec.toNat #[fp1.base]]]
          if ← defEqMatch candTy goalTy then
            let twoPow64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
            let bnd1Ty ← mkAppM ``LE.le #[
              ← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[fp1.base], fp1.len], twoPow64]
            if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp1.len]) then
              if let some hb1 ← proveSideProp bnd1Ty then
                if let some hn2 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp2.len]) then
                  let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                    mkPairPruned bal fp1 fp2
                  let prf ← mkAppOptM ``FpTree.nonWrap_or_heap #[
                    some tE, some p1E, some p2E, some rw1E, some rw2E,
                    some fp1.base, some fp2.base, some fp1.len, some fp2.len, none,
                    some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                    some hn1, some hb1, some hn2, some hhpBal]
                  goalMVar.assign prf
                  return true
  -- 6. Negation / membership exclusion (`hd ∉ cs`, `hd ∉ S`, `¬ InRegion b n x`, `ψ → False`)
  if goalTy.isAppOfArity ``Not 1 || (goalTy.isForall && goalTy.bindingBody!.isConstOf ``False) then
    let savedNeg ← saveState
    let (_, gFalse) ← goalMVar.intro1P
    if ← provePureGoalWithBal bal hhpBal gFalse then
      return true
    restoreState savedNeg
  -- 7. `False` via colliding footprints (after `intro hmem` on `hd ∉ cs` or contradictory `InRegion`)
  if goalTy.isConstOf ``False then
    for fp1 in fps do
      for fp2 in fps do
        if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
          if ← defEqMatch fp1.base fp2.base then
            if let some hn1 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp1.len]) then
              if let some hn2 ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fp2.len]) then
                let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                  mkPairPruned bal fp1 fp2
                let hne ← mkAppOptM ``FpTree.ne_heap #[
                  some tE, some p1E, some p2E, some rw1E, some rw2E,
                  some fp1.base, some fp1.base, some fp1.len, some fp2.len, none,
                  some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                  some hn1, some hhpBal, some hn2]
                goalMVar.assign (mkApp hne (← mkEqRefl fp1.base))
                return true
          let (r1, _) := peelAddrRoot ctx.letVals fp1.base
          let (r2, _) := peelAddrRoot ctx.letVals fp2.base
          if r1 == r2 then
            if let some hx1 ← proveSideProp (mkApp3 (mkConst ``InRegion) fp1.base fp1.len fp1.base) then
              if let some hx2 ← proveSideProp (mkApp3 (mkConst ``InRegion) fp2.base fp2.len fp1.base) then
                let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                  mkPairPruned bal fp1 fp2
                let prf ← mkAppOptM ``FpTree.disjoint_inRegion_heap #[
                  some tE, some p1E, some p2E, some rw1E, some rw2E,
                  some fp1.base, some fp2.base, some fp1.len, some fp2.len, none, some fp1.base,
                  some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                  some hhpBal, some hx1, some hx2]
                goalMVar.assign prf
                return true
    for ldecl in (← getLCtx) do
      if !ldecl.isImplementationDetail && !ldecl.isAuxDecl then
        let lty := (← instantiateMVars ldecl.type).consumeMData
        if lty.isAppOfArity ``InRegion 3 then
          let b2 := lty.getArg! 0
          let n2 := lty.getArg! 1
          let x := lty.getArg! 2
          for fp2 in fps do
            if (← defEqMatch fp2.base b2) && (← defEqMatch fp2.len n2) then
              for fp1 in fps do
                if fp1.leafIdx != fp2.leafIdx && (fp1.isRW || fp2.isRW) then
                  if let some hx1 ← proveSideProp (mkApp3 (mkConst ``InRegion) fp1.base fp1.len x) then
                    let (tE, p1E, p2E, rw1E, rw2E, hvPrf, trueRfl, hl1Rfl, hl2Rfl) ←
                      mkPairPruned bal fp1 fp2
                    let prf ← mkAppOptM ``FpTree.disjoint_inRegion_heap #[
                      some tE, some p1E, some p2E, some rw1E, some rw2E,
                      some fp1.base, some b2, some fp1.len, some n2, none, some x,
                      some hvPrf, some trueRfl, some trueRfl, some hl1Rfl, some hl2Rfl,
                      some hhpBal, some hx1, some ldecl.toExpr]
                    goalMVar.assign prf
                    return true
  -- 8. Total Address-Space Pigeonhole Bound (`∑ lenᵢ ≤ 2 ^ 64` → `omega` / `bv_omega`)
  let mut rwMap : Std.HashMap Nat LeafFootprint := {}
  for fp in fps do
    if fp.isRW && !rwMap.contains fp.leafIdx then
      rwMap := rwMap.insert fp.leafIdx fp
  if !rwMap.isEmpty then
    let selRW (i : Nat) : Option LeafFootprint := rwMap[i]?
    let (tAll, hvAll, rwSumExpr) ← buildPrunedFpTree bal selRW
    let twoPow64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
    let rwArr := rwMap.toArray
    let mut hSumPrf? : Option Expr := none
    -- 8A. Single bounded positive RW anchor (`0 < n₀` and `n₀ ≤ 2 ^ 64`)
    let mut posLeaves : Array (LeafFootprint × Expr) := #[]
    for (_, fpCand) in rwArr do
      if hSumPrf?.isNone then
        if let some hnPos ← proveSideProp (← mkAppM ``LT.lt #[zeroE, fpCand.len]) then
          posLeaves := posLeaves.push (fpCand, hnPos)
          if let some hnLe ← proveSideProp (← mkAppM ``LE.le #[fpCand.len, twoPow64]) then
            let hlAnchorRfl ← mkLeafSomeRfl (toExpr true) fpCand.base fpCand.len
            hSumPrf? := some (← mkAppOptM ``FpTree.rwSum_le_of_pos_anchor_heap #[
              some tAll, some (toExpr fpCand.path), some fpCand.base, some fpCand.len, none,
              some hvAll, some hlAnchorRfl, some hnPos, some hnLe, some hhpBal])
    -- 8B. Two positive RW anchors (`0 < n₁` and `0 < n₂`, no upper bounds needed!)
    if hSumPrf?.isNone && posLeaves.size ≥ 2 then
      let (fpA, hnPosA) := posLeaves[0]!
      let (fpB, hnPosB) := posLeaves[1]!
      let hlARfl ← mkLeafSomeRfl (toExpr true) fpA.base fpA.len
      let hlBRfl ← mkLeafSomeRfl (toExpr true) fpB.base fpB.len
      hSumPrf? := some (← mkAppOptM ``FpTree.rwSum_le_of_two_pos_heap #[
        some tAll, some (toExpr fpA.path), some (toExpr fpB.path),
        some fpA.base, some fpB.base, some fpA.len, some fpB.len, none,
        some hvAll, some rflTrueExpr, some hlARfl, some hlBRfl,
        some hnPosA, some hnPosB, some hhpBal])
    -- 8C. All RW leaves bounded on heap (`↦ₛ`, `↦₆₄*`, or `len ≤ 2 ^ 64`)
    if hSumPrf?.isNone then
      if let some hbPrf ← buildHoldsBoundedPrf? bal selRW twoPow64 then
        hSumPrf? := some (← mkAppOptM ``FpTree.rwSum_le_of_holdsBounded_heap #[
          some tAll, none, some hvAll, some hbPrf, some hhpBal])
    if let some hSumPrf := hSumPrf? then
      let hSumTy ← mkAppM ``LE.le #[rwSumExpr, twoPow64]
      let savedPig ← saveState
      try
        let gAssert ← goalMVar.assert `h_rw_pigeonhole hSumTy hSumPrf
        let (_, gAfter) ← gAssert.intro1P
        let rem ← evalTacticAt (← `(tactic| first | omega | bv_omega)) gAfter
        if rem.isEmpty then
          return true
        restoreState savedPig
      catch _ =>
        restoreState savedPig
  return false

/-- Inspects `P ⊢ ⌜φ⌝ ∗ P`, `hm : m ⊨ P`, or `hh : P.holds h`, rebalances `P` once in $O(N)$
    associative steps, and proves pure disjointness, container membership exclusion, RW-RO
    separation, or 64-bit address-space pigeonhole bounds in $O(\log N)$ LCA depth. -/
elab "sep_disjoint" : tactic => withMainContext do
  let goalMVar ← getMainGoal
  let goalTy := (← instantiateMVars (← goalMVar.getType)).consumeMData
  if goalTy.isAppOfArity ``SepProp.Entails 2 then
    let lhs := goalTy.getArg! 0
    let rhs := (goalTy.getArg! 1).consumeMData
    if rhs.isAppOfArity ``SepProp.sepConj 2 && (rhs.getArg! 0).consumeMData.isAppOfArity ``SepProp.pure 1 then
      let saved ← saveState
      let (bal, heq) ← rebalanceSepExpr lhs
      let [gAll] ← goalMVar.apply (mkConst ``Entails.extract_heap_fact)
        | throwError "sep_disjoint: Entails.extract_heap_fact failed"
      let (fvars, gPhi) ← gAll.introNP 2
      let hpFVar := fvars[0]!
      let hhpFVar := fvars[1]!
      let hhpBal := mkApp5 (mkConst ``holds_of_eq) lhs bal.expr (mkFVar hpFVar) heq (mkFVar hhpFVar)
      if ← provePureGoalWithBal bal hhpBal gPhi then
        replaceMainGoal []
        return
      restoreState saved
  let decls := (← getLCtx).decls.toArray.filterMap id
  for i in [:decls.size] do
    let ldecl := decls[decls.size - 1 - i]!
    if !ldecl.isImplementationDetail && !ldecl.isAuxDecl then
      let lty := (← instantiateMVars ldecl.type).consumeMData
      if lty.isAppOfArity ``SepProp.Satisfies 2 then
        let P := lty.getArg! 0
        let m := lty.getArg! 1
        let saved ← saveState
        let (bal, heq) ← rebalanceSepExpr P
        let fn ← mkAppOptM ``extract_holds_of_satisfies #[
          some P, some bal.expr, some m, some goalTy, some heq, some ldecl.toExpr]
        let [gHk] ← goalMVar.apply fn | do restoreState saved; continue
        let (fvars, gPhi) ← gHk.introNP 2
        let hhpBal := mkFVar fvars[1]!
        if ← provePureGoalWithBal bal hhpBal gPhi then
          replaceMainGoal []
          return
        restoreState saved
      else if lty.isAppOfArity ``SepProp.holds 2 then
        let P := lty.getArg! 0
        let hp := lty.getArg! 1
        let saved ← saveState
        let (bal, heq) ← rebalanceSepExpr P
        let hhpBal := mkApp5 (mkConst ``holds_of_eq) P bal.expr hp heq ldecl.toExpr
        if ← provePureGoalWithBal bal hhpBal goalMVar then
          replaceMainGoal []
          return
        restoreState saved
  throwError "sep_disjoint: could not derive `{goalTy}` from any spatial hypothesis in context"

/-- Extracts pure disjointness/pigeonhole fact `h : φ` from a `SepWP` precondition in $O(\log N)$. -/
elab "wp_disjoint " hId:ident " : " propStx:term : tactic => do
  evalTactic (← `(tactic|
    refine _root_.ProofLib.Sep.SepWP.extract_fact (φ := $propStx)
      (fun _m_disj _hm_disj => by sep_disjoint) (fun $hId => ?_)))

/-! ## 2B. Named Dual Context Syntax, Delaborator, `sintro`, `sname`, `sframe`, and `sep_accu` -/

syntax:62 "□ " str " : " term:62 : term
syntax:62 "∗ " str " : " term:62 : term

macro_rules
  | `(□ $nm:str : $p:term) => `(_root_.ProofLib.Sep.sepHyp $nm true $p)
  | `(∗ $nm:str : $p:term) => `(_root_.ProofLib.Sep.sepHyp $nm false $p)

/-- InfoView delaborator rendering `sepHyp "ro_hdr" true P` as `□ "ro_hdr" : P`
    and `sepHyp "stk_buf" false P` as `∗ "stk_buf" : P`. -/
@[delab app.ProofLib.Sep.sepHyp]
def delabSepHyp : PrettyPrinter.Delaborator.Delab := do
  let e ← SubExpr.getExpr
  if e.getAppNumArgs != 3 then failure
  let nmStx ← SubExpr.withAppFn (SubExpr.withAppFn (SubExpr.withAppArg PrettyPrinter.Delaborator.delab))
  let isPersE := (e.getArg! 1).consumeMData
  let pStx ← SubExpr.withAppArg PrettyPrinter.Delaborator.delab
  match nmStx with
  | `($s:str) =>
    if isPersE.isConstOf ``Bool.true then
      `(□ $s:str : $pStx)
    else if isPersE.isConstOf ``Bool.false then
      `(∗ $s:str : $pStx)
    else
      failure
  | _ => failure

/-- Collects right-spine atoms from a right-nested `∗` spine. -/
partial def spineAtoms (s : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let sc := s.consumeMData
  if sc.isAppOfArity ``SepProp.sepConj 2 then
    spineAtoms (sc.getArg! 1) (acc.push (sc.getArg! 0))
  else
    acc.push s

/-- Pulls the `idx`-th atom to the head of right-nested spine `s` in $O(\text{idx})$ steps using
    only `sep_pull_next` and `sep_pull_last`. -/
partial def pullSpineIdxLinear (idx : Nat) (s : Expr) :
    MetaM (Expr × Option Expr × Option Expr) := do
  let sc := s.consumeMData
  if !sc.isAppOfArity ``SepProp.sepConj 2 then
    return (s, none, none)
  let head := sc.getArg! 0
  let tail := sc.getArg! 1
  if idx == 0 then
    return (head, some tail, none)
  else
    let (target, rem?, pTail?) ← pullSpineIdxLinear (idx - 1) tail
    match rem? with
    | none =>
      let pStep1? ← match pTail? with
        | none => pure none
        | some pT => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) head) pT))
      let pSwap := mkApp2 (mkConst ``sep_pull_last) head target
      let pTot ← match pStep1? with
        | none => pure pSwap
        | some p1 => mkEqTrans p1 pSwap
      return (target, some head, some pTot)
    | some rem =>
      let pStep1? ← match pTail? with
        | none => pure none
        | some pT => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) head) pT))
      let pPull := mkApp3 (mkConst ``sep_pull_next) head target rem
      let pTot ← match pStep1? with
        | none => pure pPull
        | some p1 => mkEqTrans p1 pPull
      return (target, some (mkSepExpr head rem), some pTot)

/-- Extracts the `idx`-th atom from right spine `s`; when `dupInst? = some dupInst` (`SepDup atom`),
    duplicates `atom` so it remains in `rem?` (`Γ_□` persistent retention). -/
def extractSpineAtom (idx : Nat) (dupInst? : Option Expr) (s : Expr) :
    MetaM (Expr × Option Expr × Option Expr) := do
  let (atom, rem?, pLin?) ← pullSpineIdxLinear idx s
  match dupInst? with
  | none => return (atom, rem?, pLin?)
  | some dupInst =>
    match rem? with
    | none =>
      let pDup := mkApp2 (mkConst ``sep_dup_single) atom dupInst
      let pTot? ← mkEqTransOpt pLin? (some pDup)
      return (atom, some atom, pTot?)
    | some rem =>
      let pDup := mkApp3 (mkConst ``sep_dup_head) atom dupInst rem
      let pTot? ← mkEqTransOpt pLin? (some pDup)
      return (atom, some (mkSepExpr atom rem), pTot?)

/-- Tags untagged atoms in `e` with `sepHyp` names (`□` if `SepDup`, else `∗`). -/
partial def tagSepExprNames (e : Expr) (names : Array String) (idxRef : IO.Ref Nat) :
    MetaM Expr := do
  let ec := e.consumeMData
  if ec.isAppOfArity ``SepProp.sepConj 2 then
    let l' ← tagSepExprNames (ec.getArg! 0) names idxRef
    let r' ← tagSepExprNames (ec.getArg! 1) names idxRef
    return mkSepExpr l' r'
  else if (unpackSepHyp? ec).isSome || ec.isConstOf ``SepProp.emp then
    return e
  else
    let i ← idxRef.get
    idxRef.set (i + 1)
    let isPers : Bool ← match ← trySynthInstance (mkApp (mkConst ``SepDup) ec) with
      | .some _ => pure true
      | _ => pure false
    let nm := if h : i < names.size then names[i]
              else if isPers then s!"ro_{i}" else s!"sp_{i}"
    return mkApp3 (mkConst ``sepHyp) (toExpr nm) (toExpr isPers) e

/-- `sintro "h1" "h2" ...`: names spatial (`∗`) and persistent (`□`) precondition atoms in
    `P ⊢ Q` or `SepWP` at zero proof-term cost (`replaceTargetDefEq`). -/
elab "sintro" nms:(ppSpace str)* : tactic => withMainContext do
  let names := nms.map (·.getString)
  let goal ← getMainGoal
  let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
  let idxRef ← IO.mkRef 0
  if goalTy.isAppOfArity ``SepProp.Entails 2 then
    let lhs' ← tagSepExprNames (goalTy.getArg! 0) names idxRef
    let newTy := mkApp2 (mkConst ``SepProp.Entails) lhs' (goalTy.getArg! 1)
    replaceMainGoal [← goal.replaceTargetDefEq newTy]
  else if goalTy.isAppOfArity ``SepWP 6 then
    let args := goalTy.getAppArgs
    let pre' ← tagSepExprNames args[3]! names idxRef
    let newTy := mkAppN (mkConst ``SepWP) (args.set! 3 pre')
    replaceMainGoal [← goal.replaceTargetDefEq newTy]
  else
    throwError "sintro: expected `P ⊢ Q` or `SepWP` goal"

private partial def tagSepMatchAtom (nm : String) (pat e : Expr) : MetaM (Expr × Bool) := do
  let ec := e.consumeMData
  if ec.isAppOfArity ``SepProp.sepConj 2 then
    let (l', okL) ← tagSepMatchAtom nm pat (ec.getArg! 0)
    if okL then return (mkSepExpr l' (ec.getArg! 1), true)
    let (r', okR) ← tagSepMatchAtom nm pat (ec.getArg! 1)
    return (mkSepExpr (ec.getArg! 0) r', okR)
  else
    let raw := stripSepHyp ec
    let s ← saveState
    if ← isDefEq raw pat then
      let isPers : Bool ← match ← trySynthInstance (mkApp (mkConst ``SepDup) raw) with
        | .some _ => pure true
        | _ => pure false
      return (mkApp3 (mkConst ``sepHyp) (toExpr nm) (toExpr isPers) raw, true)
    else
      restoreState s
      return (e, false)

/-- `sname "buf" : pat`: names the first matching atom in precondition `P` with `"buf"`. -/
elab "sname " nm:str " : " patStx:term : tactic => withMainContext do
  let goal ← getMainGoal
  let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
  let pat ← Tactic.elabTerm patStx (some (mkConst ``SepProp))
  if goalTy.isAppOfArity ``SepProp.Entails 2 then
    let (lhs', ok) ← tagSepMatchAtom nm.getString pat (goalTy.getArg! 0)
    unless ok do throwError "sname: no atom matching `{pat}` found"
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp2 (mkConst ``SepProp.Entails) lhs' (goalTy.getArg! 1))]
  else if goalTy.isAppOfArity ``SepWP 6 then
    let args := goalTy.getAppArgs
    let (pre', ok) ← tagSepMatchAtom nm.getString pat args[3]!
    unless ok do throwError "sname: no atom matching `{pat}` found"
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN (mkConst ``SepWP) (args.set! 3 pre'))]
  else
    throwError "sname: expected `P ⊢ Q` or `SepWP` goal"

private def isUnassignedSepMVar (e : Expr) : MetaM Bool := do
  let ec := e.consumeMData
  if !ec.isMVar then return false
  return !(← ec.mvarId!.isAssigned)

/-- Matches concrete atoms without accidentally instantiating unassigned `?Frame` metavariables. -/
private def matchConcreteSepAtom (a b : Expr) : MetaM Bool := do
  if (← isUnassignedSepMVar a) || (← isUnassignedSepMVar b) then return false
  let rawA := stripSepHyp a
  let rawB := stripSepHyp b
  if rawA == rawB then return true
  let s ← saveState
  let ok ← withReducibleAndInstances (isDefEq rawA rawB)
  if !ok then restoreState s
  return ok

/-- Core framing and `sep_accu` engine:
    - Cancels concrete RHS obligations against LHS context atoms in $O(N)$ associative/commuting steps,
    - Retains `□`-tagged persistent hypotheses and `⌜φ⌝` pure facts via `SepDup` whenever residual
      obligations or an `?Frame` metavariable remain on the RHS,
    - When `allowAccu = true` and the remaining RHS is an unassigned `?Frame : SepProp` metavariable,
      binds `?Frame` to all unconsumed linear + retained persistent atoms and closes the goal. -/
partial def runFrameAccu (allowAccu : Bool) (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
    unless goalTy.isAppOfArity ``SepProp.Entails 2 do
      throwError "sframe/sep_accu: expected `P ⊢ Q` entailment goal, got `{goalTy}`"
    let lhs := goalTy.getArg! 0
    let rhs := goalTy.getArg! 1
    if allowAccu && (← isUnassignedSepMVar rhs) then
      rhs.consumeMData.mvarId!.assign lhs
      goal.assign (mkApp (mkConst ``Entails.refl) lhs)
      return []
    let (lSpine, pL0?, _) ← toRightSpine lhs
    let (rSpine, pR0?, _) ← toRightSpine rhs
    let lAtoms := spineAtoms lSpine
    let rAtoms := spineAtoms rSpine
    let mut found? : Option (Nat × Nat × Option Expr) := none
    for j in [:rAtoms.size] do
      if found?.isNone then
        let b := rAtoms[j]!
        if !(← isUnassignedSepMVar b) then
          for i in [:lAtoms.size] do
            if found?.isNone then
              let a := lAtoms[i]!
              if ← matchConcreteSepAtom a b then
                let isMarkedPers := match unpackSepHyp? a with
                  | some (_, true, _) => true
                  | _ => (stripSepHyp a).consumeMData.isAppOfArity ``SepProp.pure 1
                let mut hasRhsMVar := false
                for rAt in rAtoms do
                  if ← isUnassignedSepMVar rAt then hasRhsMVar := true
                let mut neededAgain := false
                for j2 in [j + 1 : rAtoms.size] do
                  if ← matchConcreteSepAtom a rAtoms[j2]! then
                    neededAgain := true
                let shouldRetain :=
                  (isMarkedPers && hasRhsMVar) || neededAgain
                let dupInst? ← if shouldRetain then
                    match ← trySynthInstance (mkApp (mkConst ``SepDup) a) with
                    | .some inst => pure (some (← instantiateMVars inst))
                    | _ => pure none
                  else pure none
                let wouldStrandLhs := (rAtoms.size == 1) && (lAtoms.size > 1 || dupInst?.isSome)
                if !wouldStrandLhs then
                  found? := some (i, j, dupInst?)
    match found? with
    | none =>
      return [goal]
    | some (i, j, dupInst?) =>
      let (aAtom, remL?, pPullL?) ← extractSpineAtom i dupInst? lSpine
      let (bAtom, remR?, pPullR?) ← pullSpineIdxLinear j rSpine
      let pLTot? ← mkEqTransOpt pL0? pPullL?
      let pRTot? ← mkEqTransOpt pR0? pPullR?
      let hL ← match pLTot? with | some p => pure p | none => mkEqRefl lhs
      let hR ← match pRTot? with | some p => pure p | none => mkEqRefl rhs
      let hAB ← mkExpectedTypeHint (← mkEqRefl bAtom) (← mkEq aAtom bAtom)
      match remL?, remR? with
      | none, none =>
        let prf := mkApp7 (mkConst ``entails_cancel_last) lhs rhs aAtom bAtom hL hR hAB
        goal.assign prf
        return []
      | none, some rR =>
        let subGoal ← mkFreshExprMVar (mkApp2 (mkConst ``SepProp.Entails) (mkConst ``SepProp.emp) rR)
        let prf := mkApp9 (mkConst ``entails_cancel_emp_frame)
          lhs rhs aAtom bAtom rR hL hR hAB subGoal
        goal.assign prf
        runFrameAccu allowAccu subGoal.mvarId!
      | some rL, some rR =>
        let subGoal ← mkFreshExprMVar (mkApp2 (mkConst ``SepProp.Entails) rL rR)
        let prf := mkApp10 (mkConst ``entails_cancel_head)
          lhs rhs aAtom bAtom rL rR hL hR hAB subGoal
        goal.assign prf
        runFrameAccu allowAccu subGoal.mvarId!
      | some _, none =>
        return [goal]

/-- `sframe`: cancels matching spatial obligations while retaining persistent (`□` / `⌜φ⌝`)
    hypotheses in `Γ_□` without consuming them; binds `?Frame` if the residual RHS is a frame mvar. -/
elab "sframe" : tactic => do
  let g ← getMainGoal
  let rem ← runFrameAccu true g
  replaceMainGoal rem

/-- `sep_accu`: automatic frame accumulator — cancels any explicit prefix obligations and binds
    all unconsumed linear (`∗`) + retained persistent (`□`) hypotheses into an unassigned
    `?Frame : SepProp` metavariable, closing the entailment. -/
elab "sep_accu" : tactic => do
  let g ← getMainGoal
  let rem ← runFrameAccu true g
  unless rem.isEmpty do
    throwError "sep_accu: residual goal was not an assignable `?Frame` metavariable"
  replaceMainGoal []

/-! ## 3B. `MetaM` Spatial LUB Reconciler & `sep_join_lub` / `wp_if_join_auto` / `wp_join_auto` -/

private partial def evalListLen? (e : Expr) : Option Nat :=
  let ec := e.consumeMData
  if ec.isAppOfArity ``List.nil 1 then some 0
  else if ec.isAppOfArity ``List.cons 3 then (evalListLen? (ec.getArg! 2)).map (· + 1)
  else none

structure CarvedAtomInfo where
  rawAtom    : Expr
  base       : Expr
  root       : Expr
  offset     : Int
  len        : Nat
  entailsPrf : Expr
  deriving Inhabited

def atomMemRegionInfo? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (atom : Expr) : MetaM (Option CarvedAtomInfo) := do
  let raw := (stripSepHyp atom).consumeMData
  let mkInfo (base : Expr) (len : Nat) (prf : Expr) : MetaM (Option CarvedAtomInfo) := do
    let (root, offset) ← do
      try
        let la ← canonAddr64 ctx cacheRef base
        pure (la.root, la.byteOff)
      catch _ =>
        pure (peelAddrRoot ctx.letVals base)
    return some { rawAtom := raw, base, root, offset, len, entailsPrf := prf }
  if raw.isAppOfArity ``Arm64.memRegion 2 then
    let b := raw.getArg! 0
    let some len ← evalClosedNat? (raw.getArg! 1) | return none
    let regE := mkApp2 (mkConst ``Arm64.memRegion) b (mkNatLit len)
    let prf ← mkExpectedTypeHint (mkApp (mkConst ``Entails.refl) raw)
      (mkApp2 (mkConst ``SepProp.Entails) raw regE)
    mkInfo b len prf
  else if raw.isAppOfArity ``ProofLib.stackAt 2 then
    let sp := raw.getArg! 0
    let some len ← evalClosedNat? (raw.getArg! 1) | return none
    let base := mkAppN (raw.getArg! 0) #[] -- resolved below via `sub`
    let _ := base
    let bExpr ← mkAppM ``HSub.hSub #[sp, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (raw.getArg! 1)]
    let regE := mkApp2 (mkConst ``Arm64.memRegion) bExpr (mkNatLit len)
    let prf ← mkExpectedTypeHint (mkApp (mkConst ``Entails.refl) raw)
      (mkApp2 (mkConst ``SepProp.Entails) raw regE)
    mkInfo bExpr len prf
  else if raw.isAppOfArity ``Arm64.pointsTo8 2 then
    let a := raw.getArg! 0; let v := raw.getArg! 1
    mkInfo a 1 (mkApp2 (mkConst ``ProofLib.pointsTo8_entails_memRegion) a v)
  else if raw.isAppOfArity ``Arm64.pointsTo16 2 then
    let a := raw.getArg! 0; let v := raw.getArg! 1
    mkInfo a 2 (mkApp2 (mkConst ``ProofLib.pointsTo16_entails_memRegion) a v)
  else if raw.isAppOfArity ``Arm64.pointsTo32 2 then
    let a := raw.getArg! 0; let v := raw.getArg! 1
    mkInfo a 4 (mkApp2 (mkConst ``ProofLib.pointsTo32_entails_memRegion) a v)
  else if raw.isAppOfArity ``Arm64.pointsTo64 2 then
    let a := raw.getArg! 0; let v := raw.getArg! 1
    mkInfo a 8 (mkApp2 (mkConst ``ProofLib.pointsTo64_entails_memRegion) a v)
  else if raw.isAppOfArity ``Arm64.pointsTo128 2 then
    let a := raw.getArg! 0; let v := raw.getArg! 1
    mkInfo a 16 (mkApp2 (mkConst ``pointsTo128_entails_memRegion) a v)
  else if raw.isAppOfArity ``Arm64.pointsToBytes 2 then
    let a := raw.getArg! 0; let bs := raw.getArg! 1
    let some len := evalListLen? bs | return none
    let lenE := mkNatLit len
    mkInfo a len (mkApp4 (mkConst ``ProofLib.pointsToBytes_entails_memRegion_of_length)
      a bs lenE (← mkEqRefl lenE))
  else if raw.isAppOfArity ``Arm64.pointsToWords64 2 then
    let a := raw.getArg! 0; let ws := raw.getArg! 1
    let some k := evalListLen? ws | return none
    let len := 8 * k
    if !(len ≤ (1 <<< 64)) then return none
    let lenE := mkNatLit len
    let hle := mkApp2 (mkConst ``le_two_pow_64_of_ble) lenE rflTrueExpr
    mkInfo a len (mkApp5 (mkConst ``pointsToWords64_entails_memRegion_of_len)
      a ws lenE (← mkEqRefl lenE) hle)
  else if raw.isAppOfArity ``ProofLib.cells 2 then
    let a := raw.getArg! 0; let kE := raw.getArg! 1
    let some k ← evalClosedNat? kE | return none
    let len := 8 * k
    if !(len ≤ (1 <<< 64)) then return none
    let lenE := mkNatLit len
    let hle := mkApp2 (mkConst ``le_two_pow_64_of_ble) lenE rflTrueExpr
    mkInfo a len (mkApp5 (mkConst ``cells_entails_memRegion_of_len) a kE lenE (← mkEqRefl lenE) hle)
  else if raw.isAppOfArity ``Arm64.stackFrameAt 2 then
    let sp := raw.getArg! 0; let nE := raw.getArg! 1
    let some len ← evalClosedNat? nE | return none
    if !(len ≤ (1 <<< 64)) then return none
    let lenE := mkNatLit len
    let hle := mkApp2 (mkConst ``le_two_pow_64_of_ble) lenE rflTrueExpr
    let prf := mkApp3 (mkConst ``stackFrameAt_entails_memRegion) sp lenE hle
    let prfTy ← inferType prf
    let base := (prfTy.getArg! 1).getArg! 0
    mkInfo base len prf
  else if raw.isAppOfArity ``Arm64.stackFrame16At 1 then
    let sp := raw.getArg! 0
    let prf := mkApp (mkConst ``stackFrame16At_entails_memRegion) sp
    let prfTy ← inferType prf
    mkInfo ((prfTy.getArg! 1).getArg! 0) 16 prf
  else if raw.isAppOfArity ``Arm64.stackFrame32At 1 then
    let sp := raw.getArg! 0
    let prf := mkApp (mkConst ``stackFrame32At_entails_memRegion) sp
    let prfTy ← inferType prf
    mkInfo ((prfTy.getArg! 1).getArg! 0) 32 prf
  else
    return none

private def proveOffsetStepEq (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (b1 : Expr) (n1 : Nat) (b2 : Expr) : TacticM Expr := do
  let n1BV := mkBV64Lit n1
  let b1c := b1.consumeMData
  let b2c := b2.consumeMData
  if b1c.isAppOfArity ``HSub.hSub 6 && b2c.isAppOfArity ``HSub.hSub 6 then
    let x1 := b1c.getArg! 4; let aLit := b1c.getArg! 5
    let x2 := b2c.getArg! 4; let cLit := b2c.getArg! 5
    let s ← saveState
    if (← withReducible (isDefEq x1 x2)) && !aLit.hasFVar && !cLit.hasFVar &&
       (← isDefEq (← mkAppM ``HSub.hSub #[aLit, n1BV]) cLit) then
      return ← mkEqSymm (mkApp5 (mkConst ``ProofLib.bitvec64_sub_add_fold_sub)
        x1 aLit n1BV cLit (← mkEqRefl cLit))
    else restoreState s
  if b1c.isAppOfArity ``HSub.hSub 6 then
    let x1 := b1c.getArg! 4; let aLit := b1c.getArg! 5
    let s ← saveState
    if (← withReducible (isDefEq x1 b2c)) && !aLit.hasFVar && (← isDefEq aLit n1BV) then
      return ← mkEqSymm (mkApp4 (mkConst ``ProofLib.bitvec64_sub_add_zero)
        x1 aLit n1BV (← mkEqRefl aLit))
    else restoreState s
  if b1c.isAppOfArity ``HAdd.hAdd 6 && b2c.isAppOfArity ``HAdd.hAdd 6 then
    let x1 := b1c.getArg! 4; let aLit := b1c.getArg! 5
    let x2 := b2c.getArg! 4; let cLit := b2c.getArg! 5
    let s ← saveState
    if (← withReducible (isDefEq x1 x2)) && !aLit.hasFVar && !cLit.hasFVar &&
       (← isDefEq (← mkAppM ``HAdd.hAdd #[aLit, n1BV]) cLit) then
      return ← mkEqSymm (mkApp5 (mkConst ``ProofLib.bitvec64_add_add_fold)
        x1 aLit n1BV cLit (← mkEqRefl cLit))
    else restoreState s
  let rhs ← mkAppM ``HAdd.hAdd #[b1, n1BV]
  if let some prf ← proveAddrEqFast? ctx cacheRef b2 rhs then
    return prf
  let eqTy ← mkEq b2 rhs
  let mv ← mkFreshExprMVar eqTy
  let rem ← evalTacticAt (← `(tactic| bv_omega)) mv.mvarId!
  unless rem.isEmpty do
    throwError "sep_join_lub: failed to prove contiguous offset step `{eqTy}`"
  return ← instantiateMVars mv

private def coalesceSortedCarved (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (sorted : Array CarvedAtomInfo) (targetBase : Expr) (targetLen : Nat) :
    TacticM (Expr × Expr) := do
  let last := sorted[sorted.size - 1]!
  let mut accAtom := last.rawAtom
  let mut accBase := last.base
  let mut accLen := last.len
  let mut accPrf := last.entailsPrf
  for step in [1 : sorted.size] do
    let cur := sorted[sorted.size - 1 - step]!
    let newLen := cur.len + accLen
    let hb ← proveOffsetStepEq ctx cacheRef cur.base cur.len accBase
    let newLenE := mkNatLit newLen
    let hN ← mkEqRefl newLenE
    let hle := mkApp2 (mkConst ``le_two_pow_64_of_ble) newLenE rflTrueExpr
    accPrf := mkAppN (mkConst ``memRegion_coalesce)
      #[cur.base, accBase, mkNatLit cur.len, mkNatLit accLen, newLenE,
        cur.rawAtom, accAtom, cur.entailsPrf, accPrf, hb, hN, hle]
    accAtom := mkSepExpr cur.rawAtom accAtom
    accBase := cur.base
    accLen := newLen
  let s ← saveState
  if ← withReducible (isDefEq accBase targetBase) then
    return (accAtom, accPrf)
  else
    restoreState s
    let hBase ← match ← proveAddrEqFast? ctx cacheRef accBase targetBase with
      | some p => pure p
      | none =>
        let eqTy ← mkEq accBase targetBase
        let mv ← mkFreshExprMVar eqTy
        let rem ← evalTacticAt (← `(tactic| bv_omega)) mv.mvarId!
        unless rem.isEmpty do
          throwError "sep_join_lub: failed to align region base `{eqTy}`"
        instantiateMVars mv
    let motive := mkLambda `b .default (mkApp (mkConst ``BitVec) (mkNatLit 64))
      (mkApp2 (mkConst ``SepProp.Entails) accAtom
        (mkApp2 (mkConst ``Arm64.memRegion) (.bvar 0) (mkNatLit targetLen)))
    let castRegPrf ← mkEqNDRec motive accPrf hBase
    return (accAtom, castRegPrf)

private partial def extractNonEmptyBlock (idxs : List Nat) (curIds : Array Nat) (curSpine : Expr) :
    MetaM (Expr × Array Nat × Option Expr × Option Expr) := do
  match idxs with
  | [] => throwError "extractNonEmptyBlock: empty index list"
  | [origIdx] =>
    let some pos := curIds.findIdx? (· == origIdx)
      | throwError "sep_join_lub: missing spine index {origIdx}"
    let (atom, rem?, p?) ← pullSpineIdxLinear pos curSpine
    return (atom, curIds.eraseIdx! pos, rem?, p?)
  | origIdx :: rest =>
    let some pos := curIds.findIdx? (· == origIdx)
      | throwError "sep_join_lub: missing spine index {origIdx}"
    let (a0, some rem1, p1?) ← pullSpineIdxLinear pos curSpine
      | throwError "sep_join_lub: unexpected singleton spine"
    let (restBlk, idsEnd, remEnd?, pRest?) ← extractNonEmptyBlock rest (curIds.eraseIdx! pos) rem1
    let pStep2? ← match pRest? with
      | none => pure none
      | some pR => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) a0) pR))
    let p12? ← mkEqTransOpt p1? pStep2?
    match remEnd? with
    | none => return (mkSepExpr a0 restBlk, idsEnd, none, p12?)
    | some remEnd =>
      let assocSymm ← mkEqSymm (mkApp3 (mkConst ``Arm64.sepConj_assoc) a0 restBlk remEnd)
      let pTot ← match p12? with | none => pure assocSymm | some p12 => mkEqTrans p12 assocSymm
      return (mkSepExpr a0 restBlk, idsEnd, some remEnd, some pTot)

private partial def expandEmptyBlocks (k : Nat) : MetaM (Expr × Option Expr) := do
  let empE : Expr := Lean.mkConst ``SepProp.emp
  if k ≤ 1 then
    return (empE, none)
  else
    let (restE, pRest?) ← expandEmptyBlocks (k - 1)
    let pHead ← mkEqSymm (mkApp (mkConst ``Arm64.emp_sepConj) empE)
    let pStep? ← match pRest? with
      | none => pure none
      | some pR => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) empE) pR))
    let pTot ← match pStep? with | none => pure pHead | some pS => mkEqTrans pHead pS
    return (mkSepExpr empE restE, some pTot)

private partial def partitionSpineIntoBlocks (blocks : List (Array Nat))
    (curIds : Array Nat) (curSpine : Expr) : MetaM (Expr × Option Expr) := do
  let empE : Expr := Lean.mkConst ``SepProp.emp
  match blocks with
  | [] => return (curSpine, none)
  | [b] =>
    if b.isEmpty || b == curIds then
      return (curSpine, none)
    else
      let (blkE, _, _, p?) ← extractNonEmptyBlock b.toList curIds curSpine
      return (blkE, p?)
  | b :: rest =>
    if b.isEmpty then
      let (restE, pRest?) ← partitionSpineIntoBlocks rest curIds curSpine
      let pEmp ← mkEqSymm (mkApp (mkConst ``Arm64.emp_sepConj) curSpine)
      let pStep? ← match pRest? with
        | none => pure none
        | some pR => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) empE) pR))
      let pTot ← match pStep? with | none => pure pEmp | some pS => mkEqTrans pEmp pS
      return (mkSepExpr empE restE, some pTot)
    else
      let (bE, idsAfter, remAfter?, pExt?) ← extractNonEmptyBlock b.toList curIds curSpine
      match remAfter? with
      | some remAfter =>
        let (restE, pRest?) ← partitionSpineIntoBlocks rest idsAfter remAfter
        let pStep? ← match pRest? with
          | none => pure none
          | some pR => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) bE) pR))
        let pTot? ← mkEqTransOpt pExt? pStep?
        return (mkSepExpr bE restE, pTot?)
      | none =>
        let (empChain, pEmpChain?) ← expandEmptyBlocks rest.length
        let p1 ← mkEqSymm (mkApp (mkConst ``Arm64.sepConj_emp) bE)
        let p2? ← match pEmpChain? with
          | none => pure none
          | some pEC => pure (some (← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) bE) pEC))
        let pTail ← match p2? with | none => pure p1 | some p2 => mkEqTrans p1 p2
        let pTot? ← mkEqTransOpt pExt? (some pTail)
        return (mkSepExpr bE empChain, pTot?)

private structure ReconcileGroup where
  tIdxs  : Array Nat
  eIdxs  : Array Nat
  tExpr  : Expr
  eExpr  : Expr
  jExpr  : Expr
  lubPrf : Expr
  deriving Inhabited

private def consumeUnusedEmpIdx? (atoms : Array Expr) (usedRef : IO.Ref (Array Bool)) :
    MetaM (Array Nat) := do
  let used ← usedRef.get
  for k in [:atoms.size] do
    if !used[k]! && (stripSepHyp atoms[k]!).consumeMData.isConstOf ``SepProp.emp then
      usedRef.set (used.set! k true)
      return #[k]
  return #[]

/-- Synthesizes `SepJoinLub cond aT aE ?J` via built-in and custom `SepJoinLub` instances. -/
private def trySynthSepJoinLub? (cond aT aE : Expr) : MetaM (Option (Expr × Expr)) := do
  let saved ← saveState
  let jMVar ← mkFreshExprMVar (mkConst ``SepProp)
  let cls := mkApp4 (mkConst ``SepJoinLub) cond aT aE jMVar
  if let .some inst ← trySynthInstance cls then
    let jE ← instantiateMVars jMVar
    let instE ← instantiateMVars inst
    if !jE.hasMVar && !instE.hasMVar then
      return some (jE, instE)
  restoreState saved
  return none

/-- Checks whether `aT` and `aE` have identical `(isRW, base, len)` footprints via `HasFootprint`
    so generic unary value LUB (`f v₁` vs `f v₂` → `∃∗ v, f v`) never conflates incompatible
    region sizes (`memRegion p 16` vs `memRegion p 32`). -/
private def hasMatchingFootprint (aT aE : Expr) : MetaM Bool := do
  let saved ← saveState
  let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
  let rw1 ← mkFreshExprMVar (mkConst ``Bool)
  let b1 ← mkFreshExprMVar bv64Ty
  let n1 ← mkFreshExprMVar (mkConst ``Nat)
  let rw2 ← mkFreshExprMVar (mkConst ``Bool)
  let b2 ← mkFreshExprMVar bv64Ty
  let n2 ← mkFreshExprMVar (mkConst ``Nat)
  let ok ← match ← trySynthInstance (mkApp4 (mkConst ``HasFootprint) aT rw1 b1 n1),
                 ← trySynthInstance (mkApp4 (mkConst ``HasFootprint) aE rw2 b2 n2) with
    | .some _, .some _ =>
      pure ((← withReducibleAndInstances (isDefEq rw1 rw2)) &&
            (← withReducibleAndInstances (isDefEq b1 b2)) &&
            (← withReducibleAndInstances (isDefEq n1 n2)))
    | _, _ => pure false
  restoreState saved
  return ok

/-- Synthesizes `(P_join, prf : SepJoinLub cond P_then P_else P_join)` by:
    1. Factoring out the common unchanged frame `F_common` in $O(k)$ steps without touching `F_common`,
    2. Reconciling asymmetric carved cells/slices vs `memRegion b n` via contiguous offset coalescing,
    3. Synthesizing 1-to-1 `SepJoinLub` instances (value differences → `∃∗ v` and custom `SepJoinLub`),
    4. Synthesizing 1-to-`emp` and `emp`-to-1 custom `SepJoinLub` instances (e.g. null-vs-pointer invariants),
    5. Applying same-footprint unary value existential LUB (`f v₁` vs `f v₂` → `∃∗ v, f v`),
    6. Coalescing heterogeneous sub-cell splits covering the same region `[b, b + n)` into `memRegion b n`. -/
def reconcileSpatialLUB (cond pThen pElse : Expr) : TacticM (Expr × Expr) := do
  if pThen == pElse then
    return (pThen, mkApp2 (mkConst ``SepJoinLub.refl) cond pThen)
  let ctx ← collectCtxFacts
  let addrCacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
  let (tSpine, pT0?, _) ← toRightSpine pThen
  let (eSpine, pE0?, _) ← toRightSpine pElse
  let tAtoms := spineAtoms tSpine
  let eAtoms := spineAtoms eSpine
  let tUsedRef ← IO.mkRef (Array.replicate tAtoms.size false)
  let eUsedRef ← IO.mkRef (Array.replicate eAtoms.size false)
  let mut tCommonIdxs : Array Nat := #[]
  let mut eCommonIdxs : Array Nat := #[]
  let empE : Expr := Lean.mkConst ``SepProp.emp
  -- 1. Greedily match common unchanged frame atoms
  for i in [:tAtoms.size] do
    let a := tAtoms[i]!
    if !(stripSepHyp a).consumeMData.isConstOf ``SepProp.emp then
      let eUsed ← eUsedRef.get
      let mut matchedJ? : Option Nat := none
      for j in [:eAtoms.size] do
        if matchedJ?.isNone && !eUsed[j]! then
          if ← matchConcreteSepAtom a eAtoms[j]! then
            matchedJ? := some j
      if let some j := matchedJ? then
        tUsedRef.modify (·.set! i true)
        eUsedRef.modify (·.set! j true)
        tCommonIdxs := tCommonIdxs.push i
        eCommonIdxs := eCommonIdxs.push j
  let mut groups : Array ReconcileGroup := #[]
  -- 2A. Asymmetric `memRegion` in `else` vs carved cells/slices in `then`
  for j in [:eAtoms.size] do
    if !(← eUsedRef.get)[j]! then
      let rawEj := (stripSepHyp eAtoms[j]!).consumeMData
      if rawEj.isAppOfArity ``Arm64.memRegion 2 || rawEj.isAppOfArity ``ProofLib.stackAt 2 then
        if let some regInfo ← atomMemRegionInfo? ctx addrCacheRef eAtoms[j]! then
          let tUsed ← tUsedRef.get
          let mut cands : Array (Nat × CarvedAtomInfo) := #[]
          for i in [:tAtoms.size] do
            if !tUsed[i]! then
              if let some ci ← atomMemRegionInfo? ctx addrCacheRef tAtoms[i]! then
                let s ← saveState
                let sameRoot ← withReducible (isDefEq ci.root regInfo.root)
                if !sameRoot then restoreState s
                if sameRoot && ci.len > 0 && ci.offset ≥ regInfo.offset &&
                   ci.offset + Int.ofNat ci.len ≤ regInfo.offset + Int.ofNat regInfo.len then
                  cands := cands.push (i, ci)
          if !cands.isEmpty then
            let sorted := cands.qsort (fun a b => a.2.offset < b.2.offset)
            let mut curOff := regInfo.offset
            let mut ok := true
            for (_, ci) in sorted do
              if ci.offset == curOff then curOff := curOff + Int.ofNat ci.len
              else ok := false
            if ok && curOff == regInfo.offset + Int.ofNat regInfo.len then
              eUsedRef.modify (·.set! j true)
              for (i, _) in sorted do tUsedRef.modify (·.set! i true)
              let (carvedE, hCoal) ←
                coalesceSortedCarved ctx addrCacheRef (sorted.map (·.2)) regInfo.base regInfo.len
              let regE := mkApp2 (mkConst ``Arm64.memRegion) regInfo.base (mkNatLit regInfo.len)
              let hCoalFull ←
                if rawEj == regE then pure hCoal
                else pure (mkApp5 (mkConst ``Entails.trans) carvedE regE rawEj hCoal regInfo.entailsPrf)
              let _ := hCoalFull
              let lubP := mkApp4 (mkConst ``lub_coalesce_then) cond carvedE regE hCoal
              groups := groups.push {
                tIdxs := sorted.map (·.1), eIdxs := #[j]
                tExpr := carvedE, eExpr := regE, jExpr := regE, lubPrf := lubP
              }
  -- 2B. Asymmetric `memRegion` in `then` vs carved cells/slices in `else`
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! then
      let rawTi := (stripSepHyp tAtoms[i]!).consumeMData
      if rawTi.isAppOfArity ``Arm64.memRegion 2 || rawTi.isAppOfArity ``ProofLib.stackAt 2 then
        if let some regInfo ← atomMemRegionInfo? ctx addrCacheRef tAtoms[i]! then
          let eUsed ← eUsedRef.get
          let mut cands : Array (Nat × CarvedAtomInfo) := #[]
          for j in [:eAtoms.size] do
            if !eUsed[j]! then
              if let some ci ← atomMemRegionInfo? ctx addrCacheRef eAtoms[j]! then
                let s ← saveState
                let sameRoot ← withReducible (isDefEq ci.root regInfo.root)
                if !sameRoot then restoreState s
                if sameRoot && ci.len > 0 && ci.offset ≥ regInfo.offset &&
                   ci.offset + Int.ofNat ci.len ≤ regInfo.offset + Int.ofNat regInfo.len then
                  cands := cands.push (j, ci)
          if !cands.isEmpty then
            let sorted := cands.qsort (fun a b => a.2.offset < b.2.offset)
            let mut curOff := regInfo.offset
            let mut ok := true
            for (_, ci) in sorted do
              if ci.offset == curOff then curOff := curOff + Int.ofNat ci.len
              else ok := false
            if ok && curOff == regInfo.offset + Int.ofNat regInfo.len then
              tUsedRef.modify (·.set! i true)
              for (j, _) in sorted do eUsedRef.modify (·.set! j true)
              let (carvedE, hCoal) ←
                coalesceSortedCarved ctx addrCacheRef (sorted.map (·.2)) regInfo.base regInfo.len
              let regE := mkApp2 (mkConst ``Arm64.memRegion) regInfo.base (mkNatLit regInfo.len)
              let lubP := mkApp4 (mkConst ``lub_coalesce_else) cond regE carvedE hCoal
              groups := groups.push {
                tIdxs := #[i], eIdxs := sorted.map (·.1)
                tExpr := regE, eExpr := carvedE, jExpr := regE, lubPrf := lubP
              }
  -- 3. 1-to-1 `SepJoinLub` synthesis (built-in typed points-to `∃∗ v` + custom `SepJoinLub` instances)
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! then
      let rawT := (stripSepHyp tAtoms[i]!).consumeMData
      if !rawT.isConstOf ``SepProp.emp then
        let eUsed ← eUsedRef.get
        let mut matched? : Option (Nat × Expr × Expr × Expr) := none
        for j in [:eAtoms.size] do
          if matched?.isNone && !eUsed[j]! then
            let rawE := (stripSepHyp eAtoms[j]!).consumeMData
            if !rawE.isConstOf ``SepProp.emp then
              if let some (jE, lubP) ← trySynthSepJoinLub? cond rawT rawE then
                matched? := some (j, rawE, jE, lubP)
        if let some (j, rawE, jE, lubP) := matched? then
          tUsedRef.modify (·.set! i true)
          eUsedRef.modify (·.set! j true)
          groups := groups.push {
            tIdxs := #[i], eIdxs := #[j]
            tExpr := rawT, eExpr := rawE, jExpr := jE, lubPrf := lubP
          }
  -- 4A. 1-to-`emp` custom `SepJoinLub` synthesis (`SepJoinLub cond rawT emp ?J`)
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! then
      let rawT := (stripSepHyp tAtoms[i]!).consumeMData
      if !rawT.isConstOf ``SepProp.emp then
        if let some (jE, lubP) ← trySynthSepJoinLub? cond rawT empE then
          tUsedRef.modify (·.set! i true)
          let eIdxs ← consumeUnusedEmpIdx? eAtoms eUsedRef
          groups := groups.push {
            tIdxs := #[i], eIdxs
            tExpr := rawT, eExpr := empE, jExpr := jE, lubPrf := lubP
          }
  -- 4B. `emp`-to-1 custom `SepJoinLub` synthesis (`SepJoinLub cond emp rawE ?J`)
  for j in [:eAtoms.size] do
    if !(← eUsedRef.get)[j]! then
      let rawE := (stripSepHyp eAtoms[j]!).consumeMData
      if !rawE.isConstOf ``SepProp.emp then
        if let some (jE, lubP) ← trySynthSepJoinLub? cond empE rawE then
          eUsedRef.modify (·.set! j true)
          let tIdxs ← consumeUnusedEmpIdx? tAtoms tUsedRef
          groups := groups.push {
            tIdxs, eIdxs := #[j]
            tExpr := empE, eExpr := rawE, jExpr := jE, lubPrf := lubP
          }
  -- 5. Same-footprint unary value LUB fallback (`f v₁` vs `f v₂` → `∃∗ v, f v`)
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! then
      let rawT := (stripSepHyp tAtoms[i]!).consumeMData
      if rawT.isApp && !rawT.isConstOf ``SepProp.emp then
        let fnT := rawT.appFn!; let v1 := rawT.appArg!
        let eUsed ← eUsedRef.get
        let mut matchedJ? : Option Nat := none
        for j in [:eAtoms.size] do
          if matchedJ?.isNone && !eUsed[j]! then
            let rawE := (stripSepHyp eAtoms[j]!).consumeMData
            if rawE.isApp && !rawE.isConstOf ``SepProp.emp then
              let s ← saveState
              if (← withReducible (isDefEq fnT rawE.appFn!)) &&
                 (← hasMatchingFootprint rawT rawE) then
                matchedJ? := some j
              else restoreState s
        if let some j := matchedJ? then
          let rawE := (stripSepHyp eAtoms[j]!).consumeMData
          let v2 := rawE.appArg!
          let lubP ← mkAppM ``SepJoinLub.val_exists #[cond, fnT, v1, v2]
          let lubTy ← inferType lubP
          tUsedRef.modify (·.set! i true)
          eUsedRef.modify (·.set! j true)
          groups := groups.push {
            tIdxs := #[i], eIdxs := #[j]
            tExpr := lubTy.getArg! 1, eExpr := lubTy.getArg! 2, jExpr := lubTy.getArg! 3
            lubPrf := lubP
          }
  -- 6. Heterogeneous sub-cell splits covering identical `[base, base + len)` → `memRegion base len`
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! then
      if let some startInfo ← atomMemRegionInfo? ctx addrCacheRef tAtoms[i]! then
        let tUsed ← tUsedRef.get
        let eUsed ← eUsedRef.get
        let mut tCands : Array (Nat × CarvedAtomInfo) := #[]
        let mut eCands : Array (Nat × CarvedAtomInfo) := #[]
        for i2 in [:tAtoms.size] do
          if !tUsed[i2]! then
            if let some ci ← atomMemRegionInfo? ctx addrCacheRef tAtoms[i2]! then
              let s ← saveState
              if (← withReducible (isDefEq ci.root startInfo.root)) && ci.len > 0 then
                tCands := tCands.push (i2, ci)
              else restoreState s
        for j2 in [:eAtoms.size] do
          if !eUsed[j2]! then
            if let some ci ← atomMemRegionInfo? ctx addrCacheRef eAtoms[j2]! then
              let s ← saveState
              if (← withReducible (isDefEq ci.root startInfo.root)) && ci.len > 0 then
                eCands := eCands.push (j2, ci)
              else restoreState s
        if !tCands.isEmpty && !eCands.isEmpty then
          let tSorted := tCands.qsort (fun a b => a.2.offset < b.2.offset)
          let eSorted := eCands.qsort (fun a b => a.2.offset < b.2.offset)
          if tSorted[0]!.2.offset == eSorted[0]!.2.offset then
            let baseOff := tSorted[0]!.2.offset
            let baseExpr := tSorted[0]!.2.base
            let mut offT := baseOff; let mut okT := true
            for (_, ci) in tSorted do
              if ci.offset == offT then offT := offT + Int.ofNat ci.len else okT := false
            let mut offE := baseOff; let mut okE := true
            for (_, ci) in eSorted do
              if ci.offset == offE then offE := offE + Int.ofNat ci.len else okE := false
            if okT && okE && offT == offE && offT > baseOff then
              let totLen := (offT - baseOff).toNat
              for (idxT, _) in tSorted do tUsedRef.modify (·.set! idxT true)
              for (idxE, _) in eSorted do eUsedRef.modify (·.set! idxE true)
              let (cT, hCoalT) ←
                coalesceSortedCarved ctx addrCacheRef (tSorted.map (·.2)) baseExpr totLen
              let (cE, hCoalE) ←
                coalesceSortedCarved ctx addrCacheRef (eSorted.map (·.2)) baseExpr totLen
              let regE := mkApp2 (mkConst ``Arm64.memRegion) baseExpr (mkNatLit totLen)
              let lubP := mkApp6 (mkConst ``lub_coalesce_both) cond cT cE regE hCoalT hCoalE
              groups := groups.push {
                tIdxs := tSorted.map (·.1), eIdxs := eSorted.map (·.1)
                tExpr := cT, eExpr := cE, jExpr := regE, lubPrf := lubP
              }
  -- Absorb leftover explicit `emp` atoms
  for i in [:tAtoms.size] do
    if !(← tUsedRef.get)[i]! && (stripSepHyp tAtoms[i]!).consumeMData.isConstOf ``SepProp.emp then
      tUsedRef.modify (·.set! i true)
      groups := groups.push {
        tIdxs := #[i], eIdxs := #[], tExpr := empE, eExpr := empE, jExpr := empE
        lubPrf := mkApp2 (mkConst ``SepJoinLub.refl) cond empE
      }
  for j in [:eAtoms.size] do
    if !(← eUsedRef.get)[j]! && (stripSepHyp eAtoms[j]!).consumeMData.isConstOf ``SepProp.emp then
      eUsedRef.modify (·.set! j true)
      groups := groups.push {
        tIdxs := #[], eIdxs := #[j], tExpr := empE, eExpr := empE, jExpr := empE
        lubPrf := mkApp2 (mkConst ``SepJoinLub.refl) cond empE
      }
  let tFinal ← tUsedRef.get; let eFinal ← eUsedRef.get
  for i in [:tAtoms.size] do
    if !tFinal[i]! then
      throwError "sep_join_lub: unreconciled `then` spatial atom `{tAtoms[i]!}`"
  for j in [:eAtoms.size] do
    if !eFinal[j]! then
      throwError "sep_join_lub: unreconciled `else` spatial atom `{eAtoms[j]!}`"
  -- 7. Assemble partitioned spines + `SepJoinLub` proof
  let hasCommon := !tCommonIdxs.isEmpty
  let blocksT := (groups.map (·.tIdxs)).toList ++ (if hasCommon then [tCommonIdxs] else [])
  let blocksE := (groups.map (·.eIdxs)).toList ++ (if hasCommon then [eCommonIdxs] else [])
  let (tStruct, pPartT?) ← partitionSpineIntoBlocks blocksT (Array.range tAtoms.size) tSpine
  let (_, pPartE?) ← partitionSpineIntoBlocks blocksE (Array.range eAtoms.size) eSpine
  let pTotT? ← mkEqTransOpt pT0? pPartT?
  let pTotE? ← mkEqTransOpt pE0? pPartE?
  let mut tailCursor := tStruct
  for _ in [:groups.size] do
    tailCursor := tailCursor.consumeMData.getArg! 1
  let (initT, initE, initJ, initLub, foldCount) ←
    if hasCommon then
      let fComm := tailCursor
      pure (fComm, fComm, fComm, mkApp2 (mkConst ``SepJoinLub.refl) cond fComm, groups.size)
    else if groups.isEmpty then
      pure (empE, empE, empE, mkApp2 (mkConst ``SepJoinLub.refl) cond empE, 0)
    else
      let gLast := groups[groups.size - 1]!
      pure (gLast.tExpr, gLast.eExpr, gLast.jExpr, gLast.lubPrf, groups.size - 1)
  let mut accT := initT
  let mut accE := initE
  let mut accJ := initJ
  let mut accLub := initLub
  for step in [:foldCount] do
    let grp := groups[foldCount - 1 - step]!
    accLub := mkAppN (mkConst ``SepJoinLub.sep)
      #[cond, grp.tExpr, grp.eExpr, grp.jExpr, accT, accE, accJ, grp.lubPrf, accLub]
    accT := mkSepExpr grp.tExpr accT
    accE := mkSepExpr grp.eExpr accE
    accJ := mkSepExpr grp.jExpr accJ
  if pTotT?.isNone && pTotE?.isNone && pThen == accT && pElse == accE then
    return (accJ, accLub)
  let hEqT ← match pTotT? with
    | some p => mkExpectedTypeHint p (← mkEq pThen accT)
    | none => mkExpectedTypeHint (← mkEqRefl accT) (← mkEq pThen accT)
  let hEqE ← match pTotE? with
    | some p => mkExpectedTypeHint p (← mkEq pElse accE)
    | none => mkExpectedTypeHint (← mkEqRefl accE) (← mkEq pElse accE)
  let finalLub := mkAppN (mkConst ``SepJoinLub.of_eq)
    #[cond, pThen, pElse, accT, accE, accJ, hEqT, hEqE, accLub]
  return (accJ, finalLub)

/-- `sep_join_lub`: synthesizes `P_join` (or reconciles into concrete `P_join`) and proves
    `SepJoinLub cond P_then P_else P_join` (or `(cond = true → P_then ⊢ P_join) ∧ (cond = false → P_else ⊢ P_join)`)
    with zero restated frame atoms and zero `ac_rfl`. -/
elab "sep_join_lub" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
  if goalTy.isAppOfArity ``SepJoinLub 4 then
    let cond := goalTy.getArg! 0
    let pThen := goalTy.getArg! 1
    let pElse := goalTy.getArg! 2
    let pJoinTarget := goalTy.getArg! 3
    let (jSynth, lubPrf) ← reconcileSpatialLUB cond pThen pElse
    if ← isDefEq jSynth pJoinTarget then
      goal.assign lubPrf
      replaceMainGoal []
    else
      let entMVar ← mkFreshExprMVar (mkApp2 (mkConst ``SepProp.Entails) jSynth pJoinTarget)
      let rem ← runFrameAccu false entMVar.mvarId!
      unless rem.isEmpty do
        throwError "sep_join_lub: synthesized `{jSynth}` could not align with target `{pJoinTarget}`"
      let monoPrf := mkAppN (mkConst ``SepJoinLub.mono_join)
        #[cond, pThen, pElse, jSynth, pJoinTarget, lubPrf, ← instantiateMVars entMVar]
      goal.assign monoPrf
      replaceMainGoal []
  else if goalTy.isAppOfArity ``And 2 then
    let lhsImp := (goalTy.getArg! 0).consumeMData
    let rhsImp := (goalTy.getArg! 1).consumeMData
    unless lhsImp.isForall && rhsImp.isForall do
      throwError "sep_join_lub: expected `SepJoinLub` or `(cond = true → P_then ⊢ P_join) ∧ (cond = false → P_else ⊢ P_join)`"
    let eqCond := lhsImp.bindingDomain!.consumeMData
    let entThen := lhsImp.bindingBody!.consumeMData
    let entElse := rhsImp.bindingBody!.consumeMData
    unless eqCond.isAppOfArity ``Eq 3 && entThen.isAppOfArity ``SepProp.Entails 2 &&
           entElse.isAppOfArity ``SepProp.Entails 2 do
      throwError "sep_join_lub: unexpected conjunction shape `{goalTy}`"
    let cond := eqCond.getArg! 1
    let pThen := entThen.getArg! 0
    let pElse := entElse.getArg! 0
    let pJoinTarget := entThen.getArg! 1
    let (jSynth, lubPrf) ← reconcileSpatialLUB cond pThen pElse
    if ← isDefEq jSynth pJoinTarget then
      goal.assign (mkApp5 (mkConst ``sepJoinLub_and_pair) cond pThen pElse jSynth lubPrf)
      replaceMainGoal []
    else
      let entMVar ← mkFreshExprMVar (mkApp2 (mkConst ``SepProp.Entails) jSynth pJoinTarget)
      let rem ← runFrameAccu false entMVar.mvarId!
      unless rem.isEmpty do
        throwError "sep_join_lub: synthesized `{jSynth}` could not align with target `{pJoinTarget}`"
      let monoPrf := mkAppN (mkConst ``SepJoinLub.mono_join)
        #[cond, pThen, pElse, jSynth, pJoinTarget, lubPrf, ← instantiateMVars entMVar]
      goal.assign (mkApp5 (mkConst ``sepJoinLub_and_pair) cond pThen pElse pJoinTarget monoPrf)
      replaceMainGoal []
  else
    throwError "sep_join_lub: expected `SepJoinLub` or branch-join entailment pair, got `{goalTy}`"

/-- `wp_if_join_auto J, hpc then <tThen> else <tElse>`: runs `tThen` and `tElse` to establish
    their respective branch spatial states `P_then` and `P_else`, automatically synthesizes `P_join`
    via `sep_join_lub`, and leaves the single join continuation goal. -/
macro "wp_if_join_auto " J:term "," hpc:term " then " tThen:tacticSeq " else " tElse:tacticSeq : tactic =>
  `(tactic| refine _root_.ProofLib.Sep.SepWP.ite_join_lub $J $hpc (by $tThen) (by $tElse) (by sep_join_lub) ?_)

/-- Term-argument variant of `wp_if_join_auto` taking branch proof terms `hthen` and `helse`. -/
macro "wp_join_auto " J:term "," hpc:term "," hthen:term "," helse:term : tactic =>
  `(tactic| refine _root_.ProofLib.Sep.SepWP.ite_join_lub $J $hpc $hthen $helse (by sep_join_lub) ?_)

end

end ProofLib.Sep
