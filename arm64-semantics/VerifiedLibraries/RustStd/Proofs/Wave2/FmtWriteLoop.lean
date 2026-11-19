/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteSym
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import ProofLib.SepLogic.WPp

/-!
# Algebra, Segment, and Loop Lemmas for `core::fmt::write`

Provides `FmtWriteFrame`, `FmtRun`, and `FmtReaches` combinators, `formatterAt` and
`fmtArgEntriesAt` separation-logic algebra, read-only template bytecode focusing (`x2 ↦ᵣ tpl`),
and epilogue and fast-path lemmas for `core::fmt::write`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib

/-! ## `FmtWriteFrame`, `FmtRun`, and `FmtReaches` Combinators -/

theorem fmtWriteFrame_refl (s : State) : FmtWriteFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem fmtWriteFrame_of_seg {s sm : State}
    (hnsp : ProofLib.NonSyscallPreserved s sm)
    (hsig : sm.sigActions = s.sigActions)
    (htp : sm.tpidrEl0 = s.tpidrEl0)
    (horc : sm.oracle = s.oracle)
    (hsym : sm.symtab = s.symtab) :
    FmtWriteFrame s sm :=
  ⟨hnsp.1, hnsp.2.2.2.2.2.2, hsig, htp, hnsp.2.2.1, hnsp.2.2.2.1,
   hnsp.2.2.2.2.1, horc, hnsp.2.2.2.2.2.1.1, hsym, fun a => congrFun hnsp.2.1 a⟩

theorem fmtReaches_head {σ : Type} {Step : FmtCall → σ → Bool → σ → Prop}
    (c : FmtCall) (cs : List FmtCall) (st : σ) :
    FmtReaches Step (c :: cs) st c st :=
  ⟨[], cs, rfl, .nil st⟩

theorem fmtReaches_cons_ok {σ : Type} {Step : FmtCall → σ → Bool → σ → Prop}
    {c c' : FmtCall} {cs : List FmtCall} {st st' st'' : σ}
    (hok : Step c st true st')
    (hr : FmtReaches Step cs st' c' st'') :
    FmtReaches Step (c :: cs) st c' st'' := by
  rcases hr with ⟨pre, post, hcs, hrun⟩
  exact ⟨c :: pre, post, by simp [hcs], .cons_ok hok hrun⟩

theorem fmtCallbacks_cons_inv {σ : Type} {P : Program} {W : σ → State → SepProp}
    {Step : FmtCall → σ → Bool → σ → Prop} {Panic Oom : FmtCall → σ → State → Prop}
    {stackBytes : Nat} {out vt writeStrFn : BitVec 64} {c : FmtCall} {cs : List FmtCall}
    (hcb : FmtCallbacks P W Step Panic Oom stackBytes out vt writeStrFn (c :: cs)) :
    FmtCallbacks P W Step Panic Oom stackBytes out vt writeStrFn cs :=
  { transport := hcb.transport
    write_str := fun ptr bs hm => hcb.write_str ptr bs (List.mem_cons_of_mem c hm)
    fmt_arg := fun idx val fn opts hm => hcb.fmt_arg idx val fn opts (List.mem_cons_of_mem c hm) }

/-! ## `formatterAt`, `memRegion 24`, and `fmtArgEntriesAt` Algebra -/

theorem formatterAt_eq_pointsTo64_triple (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) :
    formatterAt f outPtr vtPtr opts =
      ((f ↦₆₄ outPtr) ∗ ((f + 8#64) ↦₆₄ vtPtr) ∗
       ((f + 16#64) ↦₆₄ ((opts.precision ++ opts.width) ++ opts.flags))) := by
  unfold formatterAt
  have h16 := pointsTo16_pair (f + 20#64) opts.width opts.precision
  have h20 : f + 20#64 + 2#64 = f + 22#64 := by bv_omega
  rw [h20] at h16
  have h32 := pointsTo32_pair (f + 16#64) opts.flags (opts.precision ++ opts.width)
  have h16_off : f + 16#64 + 4#64 = f + 20#64 := by bv_omega
  rw [h16_off] at h32
  rw [h16, h32]

theorem formatterAt_default_eq_stp (f outPtr vtPtr : BitVec 64) :
    formatterAt f outPtr vtPtr defaultFmtOptions =
      ((f ↦₆₄ outPtr) ∗ ((f + 8#64) ↦₆₄ vtPtr) ∗ ((f + 16#64) ↦₆₄ 0x60000020#64)) := by
  rw [formatterAt_eq_pointsTo64_triple]
  rfl

theorem formatterAt_entails_memRegion24 (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) :
    formatterAt f outPtr vtPtr opts ⊢ memRegion f 24 := by
  rw [formatterAt_eq_pointsTo64_triple]
  exact triple64_entails_memRegion24 f outPtr vtPtr _

private theorem lcons {α : Type} {x y : α} {xs ys : List α} (hx : x = y) (hxs : xs = ys) :
    x :: xs = y :: ys :=
  hx ▸ hxs ▸ rfl

private theorem cw_toNat_append {m n : Nat} (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2 ^ n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

private theorem cw_toNat_extract {n : Nat} (s m : Nat) (x : BitVec n) :
    (x.extractLsb' s m).toNat = x.toNat / 2 ^ s % 2 ^ m := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem memRegion24_eq_exists_fmtFields (f : BitVec 64) :
    memRegion f 24 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
      ∃∗ fl : BitVec 32, ∃∗ wd : BitVec 16, ∃∗ pr : BitVec 16,
        ((f ↦₆₄ w0) ∗ ((f + 8#64) ↦₆₄ w1) ∗
         ((f + 16#64) ↦₃₂ fl) ∗ ((f + 20#64) ↦₁₆ wd) ∗ ((f + 22#64) ↦₁₆ pr)) := by
  rw [memRegion24_eq_exists_triple64 f]
  apply Entails.antisymm
  · apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    let fl : BitVec 32 := w2.extractLsb' 0 32
    let hi : BitVec 32 := w2.extractLsb' 32 32
    let wd : BitVec 16 := hi.extractLsb' 0 16
    let pr : BitVec 16 := hi.extractLsb' 16 16
    have hw2 : (pr ++ wd) ++ fl = w2 := by
      apply BitVec.eq_of_toNat_eq
      dsimp only [fl, hi, wd, pr]
      simp only [cw_toNat_append, cw_toNat_extract]
      have := w2.isLt; omega
    have hfmt := formatterAt_eq_pointsTo64_triple f w0 w1 { flags := fl, width := wd, precision := pr }
    dsimp only at hfmt
    rw [hw2] at hfmt
    rw [← hfmt]
    unfold formatterAt
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right fl (Entails.sepExists_right wd
        (Entails.sepExists_right pr (Entails.refl _)))))
  · apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro fl
    apply Entails.sepExists_elim; intro wd
    apply Entails.sepExists_elim; intro pr
    have hfmt := formatterAt_eq_pointsTo64_triple f w0 w1 { flags := fl, width := wd, precision := pr }
    dsimp only at hfmt
    change formatterAt f w0 w1 { flags := fl, width := wd, precision := pr } ⊢ _
    rw [hfmt]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right ((pr ++ wd) ++ fl) (Entails.refl _)))

def fmtArgElemAt (ro : Bool) (a v f : BitVec 64) : SepProp :=
  if ro then (a ↦₆₄ᵣ v) ∗ ((a + 8#64) ↦₆₄ᵣ f) else (a ↦₆₄ v) ∗ ((a + 8#64) ↦₆₄ f)

def fmtArgEntriesRest (ro : Bool) (a : BitVec 64)
    (args : List (BitVec 64 × BitVec 64)) (idx : Nat) : SepProp :=
  fmtArgEntriesAt ro a (args.take idx) ∗
  fmtArgEntriesAt ro (a + BitVec.ofNat 64 (16 * (idx + 1))) (args.drop (idx + 1))

theorem fmtArgEntriesAt_append (ro : Bool) (a : BitVec 64)
    (xs ys : List (BitVec 64 × BitVec 64)) :
    fmtArgEntriesAt ro a (xs ++ ys) =
      fmtArgEntriesAt ro a xs ∗
      fmtArgEntriesAt ro (a + BitVec.ofNat 64 (16 * xs.length)) ys := by
  induction xs generalizing a with
  | nil =>
    simp [fmtArgEntriesAt, emp_sepConj]
  | cons x xs ih =>
    rcases x with ⟨v, f⟩
    simp only [List.cons_append, fmtArgEntriesAt, List.length_cons]
    rw [ih (a + 16#64), sepConj_assoc]
    have hoff : a + 16#64 + BitVec.ofNat 64 (16 * xs.length) =
        a + BitVec.ofNat 64 (16 * (xs.length + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hoff]

theorem fmtArgEntriesAt_focus (ro : Bool) (a : BitVec 64)
    (args : List (BitVec 64 × BitVec 64)) {idx : Nat} {val word2 : BitVec 64}
    (hget : args[idx]? = some (val, word2)) :
    fmtArgEntriesAt ro a args =
      fmtArgElemAt ro (a + BitVec.ofNat 64 (16 * idx)) val word2 ∗
      fmtArgEntriesRest ro a args idx := by
  have hlt : idx < args.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsplit : args = args.take idx ++ [(val, word2)] ++ args.drop (idx + 1) := by
    have h1 := (List.take_append_drop idx args).symm
    have hdrop : args.drop idx = (val, word2) :: args.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      have heq : args[idx] = (val, word2) := by simpa [hlt] using hget
      rw [heq]
    rw [hdrop] at h1
    simpa [List.append_assoc] using h1
  conv => lhs; rw [hsplit]
  rw [List.append_assoc, fmtArgEntriesAt_append, fmtArgEntriesAt_append]
  have htl : (args.take idx).length = idx := List.length_take_of_le (by omega)
  simp only [htl, fmtArgEntriesAt, List.length_singleton, Nat.mul_one,
    fmtArgElemAt, fmtArgEntriesRest]
  have hoff : a + BitVec.ofNat 64 (16 * idx) + 16#64 =
      a + BitVec.ofNat 64 (16 * (idx + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hoff]
  ac_rfl

def fmtWord2HiRest (ro : Bool) (p8 : BitVec 64) (word2 : BitVec 64) : SepProp :=
  if ro then
    ((p8 + 2#64) ↦₁₆ᵣ word2.extractLsb' 16 16) ∗
    ((p8 + 4#64) ↦₃₂ᵣ word2.extractLsb' 32 32)
  else
    ((p8 + 2#64) ↦₁₆ word2.extractLsb' 16 16) ∗
    ((p8 + 4#64) ↦₃₂ word2.extractLsb' 32 32)

private theorem bv8_ext_eq {a b : BitVec 8} (h : a.toNat = b.toNat) : a = b :=
  BitVec.eq_of_toNat_eq h

theorem fmtArgElemAt_splitCount16 (ro : Bool) (p val word2 : BitVec 64) :
    fmtArgElemAt ro p val word2 =
      (if ro then (p + 8#64) ↦₁₆ᵣ word2.setWidth 16 else (p + 8#64) ↦₁₆ word2.setWidth 16) ∗
      ((if ro then p ↦₆₄ᵣ val else p ↦₆₄ val) ∗ fmtWord2HiRest ro (p + 8#64) word2) := by
  have hw : word2 = word2.extractLsb' 32 32 ++ (word2.extractLsb' 16 16 ++ word2.setWidth 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [cw_toNat_append, cw_toNat_extract, BitVec.toNat_setWidth]
    have := word2.isLt; omega
  cases ro
  · simp only [fmtArgElemAt, fmtWord2HiRest, Bool.false_eq_true, ↓reduceIte]
    conv => lhs; arg 2; rw [hw, ← pointsTo32_pair (p + 8#64), ← pointsTo16_pair (p + 8#64)]
    ac_rfl
  · simp only [fmtArgElemAt, fmtWord2HiRest, ↓reduceIte]
    have hro64 : ((p + 8#64) ↦₆₄ᵣ word2) =
        (((p + 8#64) ↦₁₆ᵣ word2.setWidth 16) ∗
         (((p + 8#64 + 2#64) ↦₁₆ᵣ word2.extractLsb' 16 16) ∗
          ((p + 8#64 + 4#64) ↦₃₂ᵣ word2.extractLsb' 32 32))) := by
      rw [pointsTo64RO_eq_pointsToBytesRO, pointsTo16RO_eq_pointsToBytesRO,
          pointsTo16RO_eq_pointsToBytesRO, pointsTo32RO_eq_pointsToBytesRO]
      have hunp : unpack64 word2 =
          (unpack16 (word2.setWidth 16) ++ unpack16 (word2.extractLsb' 16 16)) ++
          unpack32 (word2.extractLsb' 32 32) := by
        simp only [unpack64, unpack32, unpack16, List.cons_append, List.nil_append]
        have := word2.isLt
        exact lcons (bv8_ext_eq (by simp only [cw_toNat_extract, BitVec.toNat_setWidth]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract, BitVec.toNat_setWidth]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) <|
          lcons (bv8_ext_eq (by simp only [cw_toNat_extract]; omega)) rfl
      rw [hunp, pointsToBytesRO_append, pointsToBytesRO_append]
      simp only [unpack16, List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
      have ha4 : p + 8#64 + BitVec.ofNat 64 4 = p + 8#64 + 4#64 := rfl
      have ha2 : p + 8#64 + BitVec.ofNat 64 2 = p + 8#64 + 2#64 := rfl
      rw [ha4, ha2]
      ac_rfl
    rw [hro64]
    ac_rfl

theorem fmtCountAt_eq_some_iff {args : List (BitVec 64 × BitVec 64)} {i : Nat} {c : BitVec 16} :
    fmtCountAt args i = some c ↔ ∃ val word2, args[i]? = some (val, word2) ∧ word2.setWidth 16 = c := by
  unfold fmtCountAt
  cases h : args[i]? with
  | none => simp
  | some p =>
    rcases p with ⟨val, word2⟩
    constructor
    · intro hs
      injection hs with hs'
      exact ⟨val, word2, rfl, hs'⟩
    · rintro ⟨val', word2', heq, hc⟩
      injection heq with hp
      cases hp
      simp [hc]

/-! ## Read-Only Template Bytecode (`x2 ↦ᵣ tpl`) Focusing and Duplication -/

/-- Duplicate a contiguous sub-slice `(x2 + pos) ↦ᵣ ((tpl.drop pos).take len)` out of `x2 ↦ᵣ tpl`,
    retaining `x2 ↦ᵣ tpl` alongside the extracted slice. -/
theorem tpl_dup_slice (x2 : BitVec 64) (tpl : List (BitVec 8)) (pos len : Nat)
    (hle : pos + len ≤ tpl.length) :
    (x2 ↦ᵣ tpl) ⊢
      ((x2 + BitVec.ofNat 64 pos) ↦ᵣ ((tpl.drop pos).take len)) ∗ (x2 ↦ᵣ tpl) := by
  have hsplit : tpl = tpl.take pos ++ ((tpl.drop pos).take len ++ tpl.drop (pos + len)) := by
    have hdd : tpl.drop (pos + len) = (tpl.drop pos).drop len := List.drop_drop.symm
    rw [hdd, List.take_append_drop, List.take_append_drop]
  have htl : (tpl.take pos).length = pos := List.length_take_of_le (by omega)
  have h1 : (x2 ↦ᵣ tpl) =
      (x2 ↦ᵣ tpl.take pos) ∗
      (((x2 + BitVec.ofNat 64 pos) ↦ᵣ ((tpl.drop pos).take len)) ∗
       ((x2 + BitVec.ofNat 64 pos + BitVec.ofNat 64 ((tpl.drop pos).take len).length) ↦ᵣ
        tpl.drop (pos + len))) := by
    conv => lhs; rw [hsplit]
    rw [pointsToBytesRO_append, pointsToBytesRO_append, htl]
  have heq : (x2 ↦ᵣ tpl) =
      ((x2 + BitVec.ofNat 64 pos) ↦ᵣ ((tpl.drop pos).take len)) ∗ (x2 ↦ᵣ tpl) := by
    conv => lhs; rw [h1, ← pointsToBytesRO_dup (x2 + BitVec.ofNat 64 pos) ((tpl.drop pos).take len)]
    conv => rhs; arg 2; rw [h1]
    ac_rfl
  rw [← heq]
  exact Entails.refl _

/-- Split `x2 ↦ᵣ (pre ++ rest)` at `pos = pre.length` when `rest = b :: tail`. -/
theorem tpl_split_byte (x2 : BitVec 64) (pre : List (BitVec 8)) (b : BitVec 8) (tail : List (BitVec 8)) :
    (x2 ↦ᵣ (pre ++ b :: tail)) =
      ((x2 + BitVec.ofNat 64 pre.length) ↦₈ᵣ b) ∗
      ((x2 ↦ᵣ pre) ∗ ((x2 + BitVec.ofNat 64 (pre.length + 1)) ↦ᵣ tail)) := by
  rw [pointsToBytesRO_append, pointsToBytesRO_cons]
  have hoff : x2 + BitVec.ofNat 64 pre.length + 1#64 = x2 + BitVec.ofNat 64 (pre.length + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hoff]
  ac_rfl

/-- Combine 2 read-only bytes `[b0, b1]` into `↦₁₆ᵣ (BitVec.ofNat 16 (leBytesNat [b0, b1]))`. -/
theorem pointsToBytesRO_pair_eq_le16 (a : BitVec 64) (b0 b1 : BitVec 8) :
    (a ↦ᵣ [b0, b1]) = (a ↦₁₆ᵣ BitVec.ofNat 16 (leBytesNat [b0, b1])) := by
  have hle : BitVec.ofNat 16 (leBytesNat [b0, b1]) = b1 ++ b0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [leBytesNat, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero,
      BitVec.toNat_ofNat, cw_toNat_append]
    have := b0.isLt; have := b1.isLt
    omega
  rw [hle, pointsTo16RO_eq_pointsToBytesRO]
  have hunp : unpack16 (b1 ++ b0) = [b0, b1] := by
    simp only [unpack16]
    have := b0.isLt; have := b1.isLt
    exact lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega))
      (lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega)) rfl)
  rw [hunp]

/-- Combine 4 read-only bytes `[b0, b1, b2, b3]` into `↦₃₂ᵣ (BitVec.ofNat 32 (leBytesNat [b0, b1, b2, b3]))`. -/
theorem pointsToBytesRO_quad_eq_le32 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ᵣ [b0, b1, b2, b3]) = (a ↦₃₂ᵣ BitVec.ofNat 32 (leBytesNat [b0, b1, b2, b3])) := by
  have hle : BitVec.ofNat 32 (leBytesNat [b0, b1, b2, b3]) = b3 ++ b2 ++ b1 ++ b0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [leBytesNat, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero,
      BitVec.toNat_ofNat, cw_toNat_append]
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    omega
  rw [hle, pointsTo32RO_eq_pointsToBytesRO]
  have hunp : unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
    simp only [unpack32]
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    exact lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega)) <|
      lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega)) <|
      lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega)) <|
      lcons (bv8_ext_eq (by simp only [cw_toNat_extract, cw_toNat_append]; omega)) rfl
  rw [hunp]

/-! ## Proof Context (`CwCtx`), Postconditions, Epilogues, and Odd-`x3` Fast Path -/

/-- Shared context for a single invocation of `core::fmt::write`. -/
structure CwCtx (σ : Type) where
  P : Program
  W : σ → State → SepProp
  Step : FmtCall → σ → Bool → σ → Prop
  Panic : FmtCall → σ → State → Prop
  Oom : FmtCall → σ → State → Prop
  stackBytes : Nat
  hstack : 0x70 + stackBytes ≤ 2 ^ 64
  out : BitVec 64
  vt : BitVec 64
  writeStrFn : BitVec 64
  argsRo : Bool
  tplPtr : BitVec 64
  argsPtr : BitVec 64
  tpl : List (BitVec 8)
  args : List (BitVec 64 × BitVec 64)
  s0 : State
  R : SepProp
  ret_pc : BitVec 64

/-- Normal-return `SepWPp` postcondition parameterized by remaining calls `cs` and writer state `st`. -/
def CwQ {σ : Type} (C : CwCtx σ) (cs : List FmtCall) (st : σ) : State → SepProp → Prop :=
  fun sf P_f =>
    (∃ ok : Bool, ∃ st' : σ,
      sf.readReg32 .x0 = (if ok then 0#32 else 1#32) ∧
      FmtRun C.Step cs st ok st' ∧
      ((sf.mem ⊨ P_f ∗ C.R) →
        sf.mem ⊨
          (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
           fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
           C.W st' sf ∗ stackFrameAt C.s0.sp (0x70 + C.stackBytes)) ∗ C.R)) ∧
    sf.sp = C.s0.sp ∧ CalleeSavedPreserved C.s0 sf

/-- Panic `SepWPp` postcondition parameterized by remaining calls `cs` and writer state `st`. -/
def CwQp {σ : Type} (C : CwCtx σ) (cs : List FmtCall) (st : σ) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ C.R) →
      sf.mem ⊨ (⌜∃ c stm, FmtReaches C.Step cs st c stm ∧ C.Panic c stm sf⌝ ∗ anyHeap) ∗ C.R

/-- Out-of-memory `SepWPp` postcondition parameterized by remaining calls `cs` and writer state `st`. -/
def CwOom {σ : Type} (C : CwCtx σ) (cs : List FmtCall) (st : σ) : State → SepProp :=
  fun sf => ⌜∃ c stm, FmtReaches C.Step cs st c stm ∧ C.Oom c stm sf⌝

theorem sepWPp_sepExists_left {α : Type} {P : Program} {ret : BitVec 64} {s : State}
    {A : α → SepProp} {B : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp P ret s (A x ∗ B) Q Qp oom) :
    SepWPp P ret s ((∃∗ x, A x) ∗ B) Q Qp oom := by
  intro R' hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R' hmx hL

theorem sepWPp_pure_left {φ : Prop} {P : Program} {ret : BitVec 64} {s : State}
    {B : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp P ret s B Q Qp oom) :
    SepWPp P ret s (⌜φ⌝ ∗ B) Q Qp oom := by
  intro R' hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R' hm.2 hL

theorem sepWPp_conseq {P : Program} {ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop} {oom1 oom2 : State → SepProp}
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (hQp : ∀ sf P_f, Qp1 sf P_f → Qp2 sf P_f)
    (hoom : ∀ sf R', (sf.mem ⊨ oom1 sf ∗ R') → (sf.mem ⊨ oom2 sf ∗ R'))
    (h : SepWPp P ret s Pre Q1 Qp1 oom1) :
    SepWPp P ret s Pre Q2 Qp2 oom2 := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨ho, hmo⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hQp sf P_f hqp⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨ho, hoom sf R' hmo⟩)⟩

theorem cw_step_ok_conseq {σ : Type} (C : CwCtx σ)
    {c : FmtCall} {cs : List FmtCall} {st st' : σ} {s : State} {Pre : SepProp}
    (hok : C.Step c st true st')
    (h : SepWPp C.P C.ret_pc s Pre (CwQ C cs st') (CwQp C cs st') (CwOom C cs st')) :
    SepWPp C.P C.ret_pc s Pre (CwQ C (c :: cs) st) (CwQp C (c :: cs) st) (CwOom C (c :: cs) st) := by
  refine sepWPp_conseq ?_ ?_ ?_ h
  · rintro sf P_f ⟨⟨ok, st'', hw0, hrun, hmem⟩, hsp, hcs⟩
    exact ⟨⟨ok, st'', hw0, .cons_ok hok hrun, hmem⟩, hsp, hcs⟩
  · intro sf P_f hqp hm
    have hm' := hqp hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
    rcases hm' with ⟨⟨c', stm, hr, hpan⟩, hany⟩
    exact ⟨⟨c', stm, fmtReaches_cons_ok hok hr, hpan⟩, hany⟩
  · intro sf R' hmo
    dsimp only [CwOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    rcases hmo with ⟨⟨c', stm, hr, hoom⟩, hR⟩
    exact ⟨⟨c', stm, fmtReaches_cons_ok hok hr, hoom⟩, hR⟩

theorem spAligned_sub_112_and {sp0 : BitVec 64} (h : (sp0 - 112#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have h0 : ((sp0 - 112#64) &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : ((sp0 - 112#64) &&& 15#64).toNat = (sp0 - 112#64).toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod (sp0 - 112#64).toNat 4
  have hm2 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  rw [hm1, BitVec.toNat_sub] at h0
  simp only [BitVec.toNat_ofNat] at h0
  apply BitVec.eq_of_toNat_eq
  rw [hm2]
  simp only [BitVec.toNat_ofNat]
  have := sp0.isLt
  omega

theorem spAligned_to_sub_112_and {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 112#64) &&& 15#64 = 0#64 := by
  have h0 : (sp0 &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  have hm2 : ((sp0 - 112#64) &&& 15#64).toNat = (sp0 - 112#64).toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod (sp0 - 112#64).toNat 4
  rw [hm1] at h0
  apply BitVec.eq_of_toNat_eq
  rw [hm2, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := sp0.isLt
  omega

section
arm64_proof_prelude
set_option linter.literalFetch false

/-- Epilogue (`+0x198 .. +0x1b0`): restores `x19..x26`, `x29`, `x30 = C.ret_pc`, adds `0x70` to `sp`,
    folds the `0x70 + stackBytes` stack frame, transports `W st'`, and executes `ret`. -/
theorem cwEpilogue_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {cs : List FmtCall} {st st' : σ} {ok : Bool} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hpc : s.pc = cwPl0.base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hw0 : s.readReg32 .x0 = if ok then 0#32 else 1#32)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0)
    (hfmt_run : FmtRun C.Step cs st ok st')
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2) :
    SepWPp C.P C.ret_pc s
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
       C.W st' s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
        cwSavedSlots C.s0.sp C.s0 C.ret_pc))
      (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := C.ret_pc)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 408#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  have hw0' : s'.readReg32 .x0 = if ok then 0#32 else 1#32 := (hcpu_in.readReg32 .x0).trans hw0
  dsimp only [cwSavedSlots]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hnsp hsig htp horc hsym => ?_
  have hpcf : sm.pc = C.ret_pc := by
    rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrunf : sm.status = .Running := by
    rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hspf : sm.sp = C.s0.sp := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have hw0f : sm.readReg32 .x0 = if ok then 0#32 else 1#32 := by
    simp [arm64_norm] at hw0'
    rw [hcpu_out.readReg32 .x0]; simp [arm64_norm, hw0']
  have hcsf : CalleeSavedPreserved C.s0 sm := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27]
    · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  refine SepWPp.done hpcf hrunf ⟨⟨ok, st', hw0f, hfmt_run, fun hm => ?_⟩, hspf, hcsf⟩
  have hent :
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       (fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
        (C.W st' s ∗
         (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
          (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
           (memRegion (C.s0.sp - 104#64) 24 ∗
            (((C.s0.sp - 80#64) ↦₆₄ C.s0.readReg64 (.gpr 29#5)) ∗
             (((C.s0.sp - 72#64) ↦₆₄ C.ret_pc) ∗
              (((C.s0.sp - 64#64) ↦₆₄ C.s0.readReg64 (.gpr 26#5)) ∗
               (((C.s0.sp - 56#64) ↦₆₄ C.s0.readReg64 (.gpr 25#5)) ∗
                (((C.s0.sp - 48#64) ↦₆₄ C.s0.readReg64 (.gpr 24#5)) ∗
                 (((C.s0.sp - 40#64) ↦₆₄ C.s0.readReg64 (.gpr 23#5)) ∗
                  (((C.s0.sp - 32#64) ↦₆₄ C.s0.readReg64 (.gpr 22#5)) ∗
                   (((C.s0.sp - 24#64) ↦₆₄ C.s0.readReg64 (.gpr 21#5)) ∗
                    (((C.s0.sp - 16#64) ↦₆₄ C.s0.readReg64 (.gpr 20#5)) ∗
                     ((C.s0.sp - 8#64) ↦₆₄ C.s0.readReg64 (.gpr 19#5))))))))))))))))) ⊢
      ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
      fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
      C.W st' sm ∗ stackFrameAt C.s0.sp (0x70 + C.stackBytes) := by
    have hfold := cwFrame_fold C.s0.sp pad C.s0 C.ret_pc
    dsimp only [cwSavedSlots] at hfold
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (htrans st' s sm hframe) ?_))
    rw [stackFrameAt_split C.s0.sp 0x70 C.stackBytes C.hstack, sepConj_comm (stackFrameAt C.s0.sp 0x70)]
    exact sepConj_mono_right hfold
  exact Satisfies.mono (sepConj_mono_left hent) hm

/-- `Ok(())` exit (`+0x18c`: `mov w0, wzr; b +0x198`). -/
theorem cwExitOk_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hpc : s.pc = cwPl0.base + 396#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2) :
    SepWPp C.P C.ret_pc s
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
       C.W st s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
        cwSavedSlots C.s0.sp C.s0 C.ret_pc))
      (CwQ C [] st) (CwQp C [] st) (CwOom C [] st) := by
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 408#64)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 396#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (htrans st s sm hframe)))) ?_
  refine cwEpilogue_wpp C hext_blk hcl_sm
    (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hcpu_in.sp_eq, hsp])
    (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
    (ok := true)
    (by rw [hcpu_out.readReg32 .x0]; simp [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
    (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
    (.nil st) htrans

/-- `Err(Error)` exit (`+0x194`: `mov w0, #1`, falling through to `+0x198`). -/
theorem cwExitErr_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {cs : List FmtCall} {st st' : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hpc : s.pc = cwPl0.base + 404#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0)
    (hfmt_run : FmtRun C.Step cs st false st')
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2) :
    SepWPp C.P C.ret_pc s
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
       C.W st' s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
        cwSavedSlots C.s0.sp C.s0 C.ret_pc))
      (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 408#64)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 404#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (htrans st' s sm hframe)))) ?_
  refine cwEpilogue_wpp C hext_blk hcl_sm
    (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hcpu_in.sp_eq, hsp])
    (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
    (ok := false)
    (by rw [hcpu_out.readReg32 .x0]; simp [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
    (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
    hfmt_run htrans

/-- Odd-`x3` `Arguments::from_str` fast path (`+0x15c .. +0x188` tail-calling `write_str` via `br x3`). -/
theorem cwOddFastPath_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {st₀ : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hodd : C.argsPtr.getLsbD 0 = true)
    (hlen : C.tpl.length = (C.argsPtr >>> 1).toNat)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      [FmtCall.writeStr C.tplPtr C.tpl])
    (hpc : s.pc = cwPl0.base + 348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = C.out)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    SepWPp C.P C.ret_pc s
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       (C.tplPtr ↦ᵣ C.tpl) ∗
       C.W st₀ s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
        cwSavedSlots C.s0.sp C.s0 C.ret_pc))
      (CwQ C [FmtCall.writeStr C.tplPtr C.tpl] st₀)
      (CwQp C [FmtCall.writeStr C.tplPtr C.tpl] st₀)
      (CwOom C [FmtCall.writeStr C.tplPtr C.tpl] st₀) := by
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := C.writeStrFn)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 348#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr := (hcpu_in.readReg64 _).trans hx2
  have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
  have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
  have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
  dsimp only [cwSavedSlots]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  have hpc_sm : sm.pc = C.writeStrFn := by
    rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrun_sm : sm.status = .Running := by
    rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm : sm.sp = C.s0.sp := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have hsp_al_sm : sm.spAligned = true := by
    simp [arm64_norm, hsp'] at hsp_al'
    rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al'
  have hlr_sm : sm.readReg64 Reg.lr = C.ret_pc := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx0_sm : sm.readReg64 .x0 = C.out := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx1_sm : sm.readReg64 .x1 = C.tplPtr := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx2_sm : (sm.readReg64 .x2).toNat = C.tpl.length := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hlen]
  have hcs_sm : CalleeSavedPreserved C.s0 sm := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27]
    · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28]
    · rw [hcpu_out.readReg64]; simp [arm64_norm]
    · rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hstk_comm : C.stackBytes + 0x70 ≤ 2 ^ 64 := by have := C.hstack; omega
  let F_tail : SepProp :=
    ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
    (C.tplPtr ↦ᵣ C.tpl) ∗
    stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70
  refine call_wpp_coreFmt (x := st₀) (F := F_tail) (ret_pc := C.ret_pc)
    (hcb.write_str C.tplPtr C.tpl (.head _)) hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => by
      dsimp only [fmtWriteStrCallSpec] at hex
      rw [satisfies_pure_sepConj] at hex; exact hex.1)
    (fun sf _ ⟨R', hpan⟩ hm_pan => ?_)
    (fun sf hpcf hrunf hspf hcs_sf _hcl_sf => ?_)
    (fun sf R' _ hoom => ?_)
  · have hent_pre :
        (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
         ((C.tplPtr ↦ᵣ C.tpl) ∗
          (C.W st₀ s ∗
           (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
            (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
             (memRegion (C.s0.sp - 104#64) 24 ∗
              (((C.s0.sp - 80#64) ↦₆₄ C.s0.readReg64 (.gpr 29#5)) ∗
               (((C.s0.sp - 72#64) ↦₆₄ C.ret_pc) ∗
                (((C.s0.sp - 64#64) ↦₆₄ C.s0.readReg64 (.gpr 26#5)) ∗
                 (((C.s0.sp - 56#64) ↦₆₄ C.s0.readReg64 (.gpr 25#5)) ∗
                  (((C.s0.sp - 48#64) ↦₆₄ C.s0.readReg64 (.gpr 24#5)) ∗
                   (((C.s0.sp - 40#64) ↦₆₄ C.s0.readReg64 (.gpr 23#5)) ∗
                    (((C.s0.sp - 32#64) ↦₆₄ C.s0.readReg64 (.gpr 22#5)) ∗
                     (((C.s0.sp - 24#64) ↦₆₄ C.s0.readReg64 (.gpr 21#5)) ∗
                      (((C.s0.sp - 16#64) ↦₆₄ C.s0.readReg64 (.gpr 20#5)) ∗
                       ((C.s0.sp - 8#64) ↦₆₄ C.s0.readReg64 (.gpr 19#5))))))))))))))))) ⊢
        (fmtWriteStrCallSpec C.W C.Step C.Panic C.Oom C.stackBytes C.out C.tplPtr C.tpl).pre st₀ sm ∗ F_tail := by
      dsimp only [fmtWriteStrCallSpec, F_tail]
      have hfold := cwFrame_fold C.s0.sp pad C.s0 C.ret_pc
      dsimp only [cwSavedSlots] at hfold
      have hstk_eq :
          stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗ stackFrameAt C.s0.sp 0x70 =
            stackFrameAt sm.sp C.stackBytes ∗ stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70 := by
        rw [sepConj_comm (stackFrameAt (C.s0.sp - 112#64) C.stackBytes),
          ← stackFrameAt_split C.s0.sp 0x70 C.stackBytes C.hstack,
          Nat.add_comm 0x70 C.stackBytes,
          stackFrameAt_split C.s0.sp C.stackBytes 0x70 hstk_comm, hsp_sm]
      conv => rhs; rw [sepConj_assoc]
      refine Entails.pure_right ⟨hx0_sm, hx1_sm, hx2_sm⟩ ?_
      conv => lhs; arg 2; arg 1; rw [← pointsToBytesRO_dup C.tplPtr C.tpl]
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (hcb.transport st₀ s sm hframe)
          (Entails.trans (sepConj_mono_right hfold) (by rw [hstk_eq]; exact Entails.refl _))))) ?_
      have hac :
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (((C.tplPtr ↦ᵣ C.tpl) ∗ (C.tplPtr ↦ᵣ C.tpl)) ∗
             (C.W st₀ sm ∗
              (stackFrameAt sm.sp C.stackBytes ∗
               stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70))) =
          ((C.tplPtr ↦ᵣ C.tpl) ∗ C.W st₀ sm ∗ stackFrameAt sm.sp C.stackBytes) ∗
            (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗ (C.tplPtr ↦ᵣ C.tpl) ∗
             stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70) := by
        ac_rfl
      rw [hac]
      exact Entails.refl _
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent_pre) hm
  · dsimp only [fmtWriteStrCallSpec] at hpan hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.writeStr C.tplPtr C.tpl, st₀,
      fmtReaches_head _ [] st₀, hpan.1⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  · dsimp only [fmtWriteStrCallSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0f, hstep⟩
    have hrun_res : FmtRun C.Step [FmtCall.writeStr C.tplPtr C.tpl] st₀ ok st' := by
      cases ok
      · exact .cons_err hstep
      · exact .cons_ok hstep (.nil st')
    refine SepWPp.done hpcf hrunf ⟨⟨ok, st', hw0f, hrun_res, fun hm => ?_⟩, hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩
    have hent_post :
        ((C.W st' sf ∗ stackFrameAt sm.sp C.stackBytes) ∗ F_tail) ⊢
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
          fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
          C.W st' sf ∗ stackFrameAt C.s0.sp (0x70 + C.stackBytes) := by
      dsimp only [F_tail, fmtArgumentsAt]
      simp only [hodd, ↓reduceIte, sepConj_emp, hsp_sm, sepConj_assoc]
      have hstk_back :
          stackFrameAt C.s0.sp C.stackBytes ∗ stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70 =
            stackFrameAt C.s0.sp (0x70 + C.stackBytes) := by
        rw [← stackFrameAt_split C.s0.sp C.stackBytes 0x70 hstk_comm, Nat.add_comm]
      have hac :
          C.W st' sf ∗
            (stackFrameAt C.s0.sp C.stackBytes ∗
             (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
              ((C.tplPtr ↦ᵣ C.tpl) ∗
               stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70))) =
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            ((C.tplPtr ↦ᵣ C.tpl) ∗
             (C.W st' sf ∗
              (stackFrameAt C.s0.sp C.stackBytes ∗
               stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 0x70))) := by
        ac_rfl
      rw [hac, hstk_back]
      exact Entails.refl _
    exact Satisfies.mono (sepConj_mono_left hent_post) hm
  · dsimp only [fmtWriteStrCallSpec, CwOom] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom
    rw [satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.writeStr C.tplPtr C.tpl, st₀, fmtReaches_head _ [] st₀, hoom.1⟩,
      Satisfies.drop_left hoom.2⟩

end

end VerifiedLibraries.RustStd
