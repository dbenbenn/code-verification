/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib.ProgramReflection -- shake: keep
public meta import Aesop.BuiltinRules
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
public meta import Mathlib.Tactic.ToDual
public import ProofLib.Lemmas
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public section

namespace CryptoVerification.E2E.Record.ImageWitness

open Arm64 ProofLib ProofLib.ProgramReflection Lean Meta Elab Term

set_option maxRecDepth 2000000

@[expose] def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listGet? xs k

theorem listGet?_eq_getElem? {α : Type} :
    ∀ (xs : List α) (k : Nat), listGet? xs k = xs[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => listGet?_eq_getElem? xs k

private theorem natListBeq_eq_false' : ∀ {l₁ l₂ : List Nat}, natListBeq l₁ l₂ = false → l₁ ≠ l₂
  | [], [], h => by contradiction
  | _ :: _, [], _ => nofun
  | [], _ :: _, _ => nofun
  | _ :: ns₁, _ :: ns₂, h => by
    simp only [natListBeq] at h
    split at h
    · intro hcons
      injection hcons with _ htail
      exact natListBeq_eq_false' h htail
    · rename_i hne
      intro hcons
      injection hcons with hhead _
      subst hhead
      exact absurd (Nat.beq_eq.mpr rfl) hne

private theorem natEntryBeq_eq_false' {e₁ e₂ : Nat × List Nat} (h : natEntryBeq e₁ e₂ = false) :
    e₁ ≠ e₂ := by
  simp only [natEntryBeq] at h
  split at h
  · intro heq
    exact natListBeq_eq_false' h (congrArg Prod.snd heq)
  · rename_i hlen
    intro heq
    exact absurd (Nat.beq_eq.mpr (congrArg Prod.fst heq)) hlen

private theorem string_beq_of_natEntryBeq_false' {l₁ l₂ : List Char}
    (h : natEntryBeq (encodeCharKey l₁) (encodeCharKey l₂) = false) :
    (String.ofList l₁ == String.ofList l₂) = false :=
  beq_eq_false_iff_ne.mpr
    (mt String.ofList_inj.mp (mt (congrArg encodeCharKey) (natEntryBeq_eq_false' h)))

private theorem natEntryFresh_getElem' {cs₀ : List Char} :
    ∀ (tl : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs₀) (prepareCharSymbols tl) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        tl[k]? = some (cs, addr) → natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs) = false
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl', hfresh, k, _, _, hk => by
    simp only [prepareCharSymbols, natEntryFresh] at hfresh
    split at hfresh
    · contradiction
    · rename_i hne01
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact Bool.eq_false_of_ne_true hne01
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact natEntryFresh_getElem' tl' hfresh k' hk

private theorem find_and_filter_none_of_fresh {cs : List Char} :
    ∀ (syms : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs) (prepareCharSymbols syms) = true →
      (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) = none ∧
      (toStringSymbols syms).filter (fun p => p.1 == String.ofList cs) = []
  | [], _ => ⟨rfl, rfl⟩
  | (cs₀, _) :: tl, h => by
    simp only [prepareCharSymbols, natEntryFresh] at h
    split at h
    · contradiction
    · rename_i hne
      have hbeq : (String.ofList cs₀ == String.ofList cs) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm (mt String.ofList_inj.mp
          (mt (congrArg encodeCharKey) (natEntryBeq_eq_false' (Bool.eq_false_of_ne_true hne)))))
      simp only [toStringSymbols, List.find?, List.filter, hbeq]
      exact find_and_filter_none_of_fresh tl h

private theorem find_and_filter_of_allFresh :
    ∀ (syms : List (List Char × Nat)),
      allFreshEntries (prepareCharSymbols syms) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        syms[k]? = some (cs, addr) →
        (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) =
          some (String.ofList cs, addr) ∧
        (toStringSymbols syms).filter (fun p => p.1 == String.ofList cs) =
          [(String.ofList cs, addr)]
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharSymbols, allFreshEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        simp only [toStringSymbols, List.find?, List.filter, beq_self_eq_true,
          (find_and_filter_none_of_fresh tl hfresh).2, and_self]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [toStringSymbols, List.find?, List.filter,
          string_beq_of_natEntryBeq_false' (natEntryFresh_getElem' tl hfresh k' hk)]
        exact find_and_filter_of_allFresh tl h k' hk
    · contradiction

private theorem toStringSymbols_getElem?' :
    ∀ (syms : List (List Char × Nat)) (k : Nat) {name : String} {addr : Nat},
      (toStringSymbols syms)[k]? = some (name, addr) →
      ∃ cs, syms[k]? = some (cs, addr) ∧ name = String.ofList cs
  | [], _, _, _, hk => by simp [toStringSymbols] at hk
  | (cs₀, _) :: _, 0, _, _, hk => by
    simp only [toStringSymbols, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    rcases hk with ⟨rfl, rfl⟩
    exact ⟨cs₀, rfl, rfl⟩
  | (_, _) :: tl, k + 1, _, _, hk => by
    simp only [toStringSymbols, List.getElem?_cons_succ] at hk
    exact toStringSymbols_getElem?' tl k hk

theorem lookup_and_unique_of_allFresh {syms : List (List Char × Nat)} {xs : List (String × Nat)}
    (hxs : xs = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    {k : Nat} {name : String} {off : Nat} (hk : xs[k]? = some (name, off)) :
    Obj.lookup name xs = some off ∧
    xs.filter (fun p => p.1 == name) = [(name, off)] := by
  rw [hxs] at hk ⊢
  rcases toStringSymbols_getElem?' syms k hk with ⟨cs, hk_cs, rfl⟩
  obtain ⟨hfind, hfilt⟩ := find_and_filter_of_allFresh syms hfresh k hk_cs
  exact ⟨by simp [Obj.lookup, hfind], hfilt⟩

theorem filter_sublist_eq_singleton {α : Type} {name : String}
    {pre mid post : List (String × α)} {v : α}
    (h : (pre ++ mid ++ post).filter (fun p => p.1 == name) = [(name, v)])
    (hmem : (name, v) ∈ mid) :
    mid.filter (fun p => p.1 == name) = [(name, v)] := by
  rw [List.filter_append, List.filter_append] at h
  have hmem_f : (name, v) ∈ mid.filter (fun p => p.1 == name) :=
    List.mem_filter.mpr ⟨hmem, beq_self_eq_true name⟩
  cases hpre : pre.filter (fun p => p.1 == name) with
  | nil =>
    rw [hpre, List.nil_append] at h
    cases hmid : mid.filter (fun p => p.1 == name) with
    | nil => simp [hmid] at hmem_f
    | cons a tl =>
      rw [hmid, List.cons_append] at h
      injection h with ha htl
      have htl_nil : tl = [] := (List.append_eq_nil_iff.mp htl).1
      subst ha; subst htl_nil; rfl
  | cons a tl =>
    rw [hpre, List.cons_append, List.cons_append] at h
    injection h with _ htl
    have hmid_nil : mid.filter (fun p => p.1 == name) = [] :=
      (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp htl).1).2
    simp [hmid_nil] at hmem_f

theorem lookupUnique_of_filter_sublist {α : Type} {name : String}
    {pre mid post : List (String × α)} {v : α}
    (h : (pre ++ mid ++ post).filter (fun p => p.1 == name) = [(name, v)])
    (hmem : (name, v) ∈ mid) :
    Obj.lookupUnique name mid = some v := by
  simp [Obj.lookupUnique, filter_sublist_eq_singleton h hmem]

private theorem natEntryFresh_of_allDisjoint' {symEntries : List (Nat × List Nat)} :
    ∀ (stubSyms : List (List Char × Nat)),
      allDisjointEntries (prepareCharSymbols stubSyms) symEntries = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        stubSyms[k]? = some (cs, addr) →
        natEntryFresh (encodeCharKey cs) symEntries = true
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharSymbols, allDisjointEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact hfresh
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact natEntryFresh_of_allDisjoint' tl h k' hk
    · contradiction

private theorem WordTree.toBytesAux_eq_append' :
    ∀ (t : WordTree) (acc : List (BitVec 8)),
      t.toBytesAux acc = t.toBytesAux [] ++ acc
  | .empty, _ => rfl
  | .leaf _ _ _ _, _ => rfl
  | .node _ l r, acc => by
    simp only [WordTree.toBytesAux]
    rw [toBytesAux_eq_append' l (r.toBytesAux acc),
        toBytesAux_eq_append' r acc, toBytesAux_eq_append' l (r.toBytesAux []),
        List.append_assoc]

theorem WordTree.length_toBytesAux_nil' :
    ∀ (t : WordTree) {n : Nat},
      t.checkSize? = some n →
      (t.toBytesAux []).length = 4 * n
  | .empty, _, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .leaf _ _ _ _, _, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .node lw l r, _, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    rw [WordTree.toBytesAux, toBytesAux_eq_append' l, List.length_append,
        length_toBytesAux_nil' l hl, length_toBytesAux_nil' r hr]
    omega

private theorem WordTree.sliceBytesAux_eq' :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (widx cnt : Nat),
      t.checkSize? = some n →
      widx + cnt ≤ n →
      ((t.toBytesAux []).drop (4 * widx)).take (4 * cnt) ++ acc =
        WordTree.sliceBytesAux t widx cnt acc
  | .empty, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?, Option.some.injEq] at hsz; subst hsz
    have hw : widx = 0 := by omega
    have hc : cnt = 0 := by omega
    subst hw; subst hc; rfl
  | .leaf b0 b1 b2 b3, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?, Option.some.injEq] at hsz; subst hsz
    rcases (by omega : cnt = 0 ∨ (widx = 0 ∧ cnt = 1)) with rfl | ⟨rfl, rfl⟩
    · simp [WordTree.sliceBytesAux]
    · rfl
  | .node lw l r, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    simp only [Option.some.injEq] at hsz; subst hsz
    have hlen_l := length_toBytesAux_nil' l hl
    have hlen_r := length_toBytesAux_nil' r hr
    simp only [WordTree.sliceBytesAux]
    by_cases hcnt0 : cnt = 0
    · subst hcnt0; simp
    · have hcnt_beq : (cnt == 0) = false := beq_eq_false_iff_ne.mpr hcnt0
      simp only [hcnt_beq, Bool.false_eq_true, ↓reduceIte]
      rw [WordTree.toBytesAux, toBytesAux_eq_append' l (r.toBytesAux [])]
      split
      · rename_i hleft
        have h1 : 4 * widx ≤ (l.toBytesAux []).length := by omega
        have h2 : 4 * cnt ≤ ((l.toBytesAux []).drop (4 * widx)).length := by
          rw [List.length_drop]; omega
        rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
        exact sliceBytesAux_eq' l acc widx cnt hl hleft
      · rename_i hnotleft
        split
        · rename_i hright
          have h1 : (l.toBytesAux []).length ≤ 4 * widx := by omega
          have hdrop_l : (l.toBytesAux []).drop (4 * widx) = [] :=
            List.drop_eq_nil_of_le h1
          have hsub : 4 * widx - (l.toBytesAux []).length = 4 * (widx - lw) := by omega
          rw [List.drop_append, hdrop_l, List.nil_append, hsub]
          exact sliceBytesAux_eq' r acc (widx - lw) cnt hr (by omega)
        · rename_i hnotright
          have h1 : 4 * widx ≤ (l.toBytesAux []).length := by omega
          have hrem : ((l.toBytesAux []).drop (4 * widx)).length = 4 * (lw - widx) := by
            rw [List.length_drop]; omega
          rw [List.drop_append_of_le_length h1, List.take_append, hrem]
          have htake_l : ((l.toBytesAux []).drop (4 * widx)).take (4 * cnt) =
              ((l.toBytesAux []).drop (4 * widx)).take (4 * (lw - widx)) := by
            rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          have hsub : 4 * cnt - 4 * (lw - widx) = 4 * (cnt - (lw - widx)) := by omega
          rw [htake_l, hsub, List.append_assoc,
              ← (show ((r.toBytesAux []).drop (4 * 0)).take (4 * (cnt - (lw - widx))) ++ acc = _ from
                sliceBytesAux_eq' r acc 0 (cnt - (lw - widx)) hr (by omega)),
              List.drop_zero]
          exact sliceBytesAux_eq' l _ widx (lw - widx) hl (by omega)

theorem sliceBytesChecked_eq' {t : WordTree} {n off span : Nat} {bs : List (BitVec 8)}
    (hwf : t.checkSize? = some n)
    (hs : WordTree.sliceBytesChecked t n off span = some bs) :
    ((t.toBytes.drop off).take span) = bs := by
  simp only [WordTree.sliceBytesChecked] at hs
  split at hs <;> try contradiction
  rename_i hal
  split at hs <;> try contradiction
  rename_i hle
  simp only [Option.some.injEq] at hs
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hal
  rcases hal with ⟨hal_off, hal_span⟩
  have hoff : off = 4 * (off / 4) := by omega
  have hspan : span = 4 * (span / 4) := by omega
  have h := WordTree.sliceBytesAux_eq' t [] (off / 4) (span / 4) hwf hle
  rw [List.append_nil] at h
  rw [WordTree.toBytes, hoff, hspan, h, hs]

structure CallWitness where
  roff : Nat
  isSym : Bool
  kTarget : Nat
  targetOff : Nat
  deriving Repr

structure CallFnWitness where
  kSym : Nat
  off : Nat
  calls : List CallWitness
  deriving Repr

structure FnWitness where
  kSym : Nat
  off : Nat
  deriving Repr

private meta def strLitVal (e : Expr) : MetaM String := do
  let some s ← (do
      if let .lit (.strVal s) := e then pure (some s)
      else if let .lit (.strVal s) := (← withTransparency .all (whnf e)) then pure (some s)
      else pure none)
    | throwError "expected string literal, got {e}"
  return s

private meta def natLitVal (e : Expr) : MetaM Nat := do
  let e ← withTransparency .all (whnf e)
  if let some n := e.rawNatLit? then return n
  if let some n := e.nat? then return n
  throwError "expected nat literal, got {e}"

private meta def mkListExpr (elemTy : Expr) (elems : Array Expr) : Expr := Id.run do
  let nilExpr := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  let mut acc := nilExpr
  for i in [0 : elems.size] do
    acc := mkApp2 consFn elems[elems.size - 1 - i]! acc
  return acc

@[expose] def checkCallWordsCW (off j : Nat) :
    List (BitVec 8) → List (BitVec 8) → List CallWitness → Bool
  | b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: c2 :: c3 :: cs, cws =>
    let w := [b0, b1, b2, b3]
    let actual := [c0, c1, c2, c3]
    let expected := match cws.find? (fun cw => cw.roff == 4 * j) with
      | some cw => Obj.patchBranchBytes w (off + 4 * j) cw.targetOff
      | none => w
    actual == expected && checkCallWordsCW off (j + 1) bs cs cws
  | [], [], _ => true
  | _, _, _ => false

theorem drop_four_cons {α : Type} (x0 x1 x2 x3 : α) (xs : List α) (k : Nat) :
    (x0 :: x1 :: x2 :: x3 :: xs).drop (4 * (k + 1)) = xs.drop (4 * k) := by
  have h : 4 * (k + 1) = 4 * k + 4 := by omega
  rw [h]; rfl

theorem checkCallWordsCW_get (off : Nat) (cws : List CallWitness) :
    ∀ (bs cs : List (BitVec 8)) (j₀ k : Nat),
      checkCallWordsCW off j₀ bs cs cws = true →
      k < bs.length / 4 →
      ((cs.drop (4 * k)).take 4 ==
        let w := (bs.drop (4 * k)).take 4
        match cws.find? (fun cw => cw.roff == 4 * (j₀ + k)) with
        | some cw => Obj.patchBranchBytes w (off + 4 * (j₀ + k)) cw.targetOff
        | none => w) = true
  | [], _, _, _, _, hk => by simp at hk
  | [_], _, _, _, _, hk => by simp at hk
  | [_, _], _, _, _, _, hk => by simp at hk
  | [_, _, _], _, _, _, _, hk => by simp at hk
  | b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: c2 :: c3 :: cs, j₀, k, h, hk => by
    simp only [checkCallWordsCW, Bool.and_eq_true] at h
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.drop_zero, List.take]
      exact h.1
    | succ k' =>
      have hk' : k' < bs.length / 4 := by
        simp only [List.length_cons] at hk; omega
      rw [drop_four_cons b0 b1 b2 b3 bs k', drop_four_cons c0 c1 c2 c3 cs k',
          show j₀ + (k' + 1) = (j₀ + 1) + k' by omega]
      exact checkCallWordsCW_get off cws bs cs (j₀ + 1) k' h.2 hk'
  | _ :: _ :: _ :: _ :: _, [], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_, _, _], _, _, h, _ => by simp [checkCallWordsCW] at h

theorem drop_take_four_of_slice {code cs : List (BitVec 8)} {off len j : Nat}
    (hslice : (code.drop off).take len = cs) (hj : j < len / 4) :
    (cs.drop (4 * j)).take 4 = (code.drop (off + 4 * j)).take 4 := by
  rw [← hslice, List.drop_take, List.drop_drop, List.take_take,
      Nat.min_eq_left (by omega)]

@[expose] def checkCallsRanges (off : Nat) : List (Nat × String) → List CallWitness → Bool
  | [], [] => true
  | _ :: calls, cw :: cws =>
    Obj.branchInRange (off + cw.roff) cw.targetOff && checkCallsRanges off calls cws
  | _, _ => false

@[expose] def lhsCallLookups (syms stubs : List (String × Nat)) :
    List CallWitness → List (Nat × Option (String × Nat))
  | [] => []
  | cw :: cws =>
    (cw.roff, if cw.isSym then listGet? syms cw.kTarget else listGet? stubs cw.kTarget) ::
      lhsCallLookups syms stubs cws

@[expose] def rhsCallLookups :
    List (Nat × String) → List CallWitness → List (Nat × Option (String × Nat))
  | (roff, sym) :: calls, cw :: cws => (roff, some (sym, cw.targetOff)) :: rhsCallLookups calls cws
  | _, _ => []

@[expose] def lhsFnLookups (syms : List (String × Nat)) :
    List FnWitness → List (Option (String × Nat))
  | [] => []
  | fw :: fws => listGet? syms fw.kSym :: lhsFnLookups syms fws

@[expose] def rhsFnLookups :
    List (String × List (BitVec 8)) → List FnWitness → List (Option (String × Nat))
  | (f, _) :: fns, fw :: fws => some (f, fw.off) :: rhsFnLookups fns fws
  | _, _ => []

@[expose] def lhsCallFnLookups (syms stubs : List (String × Nat)) :
    List CallFnWitness →
    List (Option (String × Nat) × List (Nat × Option (String × Nat)))
  | [] => []
  | cfw :: cfws =>
    (listGet? syms cfw.kSym, lhsCallLookups syms stubs cfw.calls) ::
      lhsCallFnLookups syms stubs cfws

@[expose] def rhsCallFnLookups :
    List (String × List (BitVec 8) × List (Nat × String)) → List CallFnWitness →
    List (Option (String × Nat) × List (Nat × Option (String × Nat)))
  | (f, _, calls) :: cfs, cfw :: cfws =>
    (some (f, cfw.off), rhsCallLookups calls cfw.calls) :: rhsCallFnLookups cfs cfws
  | _, _ => []

@[expose] def lhsLookups (syms stubs : List (String × Nat)) :
    List (List FnWitness × List CallFnWitness) →
    List (List (Option (String × Nat)) ×
      List (Option (String × Nat) × List (Nat × Option (String × Nat))))
  | [] => []
  | (fws, cfws) :: rest =>
    (lhsFnLookups syms fws, lhsCallFnLookups syms stubs cfws) :: lhsLookups syms stubs rest

theorem mem_mid_of_getElem?_append {α : Type} {pre mid post : List α} {k kLo kHi : Nat} {x : α}
    (hpre : pre.length = kLo) (hmid : pre.length + mid.length = kHi)
    (hlo : kLo ≤ k) (hhi : k < kHi)
    (hget : (pre ++ mid ++ post)[k]? = some x) :
    x ∈ mid := by
  rw [List.getElem?_append_left (by rw [List.length_append, hmid]; exact hhi)] at hget
  rw [List.getElem?_append_right (by rw [hpre]; exact hlo)] at hget
  exact List.mem_of_getElem? hget

elab "exact_no_defeq " t:term : tactic =>
  Elab.Tactic.withMainContext do
    let e ← Elab.Tactic.elabTerm t none
    (← Elab.Tactic.getMainGoal).assign e
    Elab.Tactic.replaceMainGoal []

end CryptoVerification.E2E.Record.ImageWitness
