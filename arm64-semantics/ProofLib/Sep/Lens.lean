/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Addr
public import ProofLib.SepLogic.Cells
public meta import Lean

/-!
# First-Order Separation-Logic Lenses, `StructLayout`, and `WordCodec`

Provides first-order algebraic separation-logic lenses (`SepLens`, `LawfulSepLens`, `SepLensAt`),
declarative byte-layout descriptors (`StructField`, `StructLayout`) with automatic gap/explicit
`memRegion` padding and 1-step stack reclamation (`StructLayout.struct_to_memRegion`),
symbolic-offset array and downward slot-table lenses (`pointsToArray`, `slotsDownFrom`),
width-polymorphic `WordCodec` windows (`u8`..`u128` and 16-byte word pairs) over byte slices (`↦ₛ`)
and physical cell maps (`OwnByteMap`), and demand-driven `SepWP` stepping tactics (`lens_open`,
`lens_switch`, `lens_close`, `wp_lens_step`, `wp_lens_auto`).
-/

namespace ProofLib.Sep

open Arm64 ProofLib

/-! ## 1. First-Order Algebraic `SepLens`, Transitive Composition, and `SepWP` Framing -/

public section

/-- Typeclass-backed extensible registry tag for `@[sep_lens]` rules. -/
class SepLensRule (declName : Lean.Name) : Prop where
  isLens : True := trivial

end

public meta section

open Lean Elab Command Meta

/-- Extract the declaration identifier from a `command` syntax tree. -/
partial def findLensDeclId? (stx : Syntax) : Option Ident :=
  if stx.getKind == ``Lean.Parser.Command.declId then
    some ⟨stx[0]⟩
  else
    stx.getArgs.findSome? findLensDeclId?

/-- Register a `SepLens` or `LawfulSepLens` theorem in the global `@[sep_lens]` index. -/
elab (priority := high) "@[sep_lens]" cmd:command : command => do
  elabCommand cmd
  let some rawId := findLensDeclId? cmd
    | throwError "@[sep_lens]: expected a named declaration"
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload rawId
  let instCmd ← `(command| instance : _root_.ProofLib.Sep.SepLensRule $(quote fullName) := {})
  elabCommand instCmd

/-- Register an already-declared `SepLens` or `LawfulSepLens` theorem in `@[sep_lens]`. -/
elab "register_sep_lens " id:ident : command => do
  let fullName ← liftCoreM <| realizeGlobalConstNoOverload id
  let instCmd ← `(command| instance : _root_.ProofLib.Sep.SepLensRule $(quote fullName) := {})
  elabCommand instCmd

end

public section

/-- First-order algebraic separation-logic lens decomposing `Whole s` into `Focus (get s) ∗ Hole s`
    without higher-order magic-wand closures in kernel proof terms. -/
structure SepLens {α β : Type} (Whole : α → SepProp) (Focus : β → SepProp) (Hole : α → SepProp)
    (get : α → β) (put : α → β → α) : Prop where
  open_entails  : ∀ s, Whole s ⊢ Focus (get s) ∗ Hole s
  close_entails : ∀ s v', Focus v' ∗ Hole s ⊢ Whole (put s v')

/-- Lawful algebraic `SepLens` bundling the three get/put lens equations so read-only accesses
    automatically re-close to the unchanged `Whole s`. -/
structure LawfulSepLens {α β : Type} (Whole : α → SepProp) (Focus : β → SepProp)
    (Hole : α → SepProp) (get : α → β) (put : α → β → α) : Prop
    extends SepLens Whole Focus Hole get put where
  put_get : ∀ s, put s (get s) = s
  get_put : ∀ s v', get (put s v') = v'
  put_put : ∀ s v₁ v₂, put (put s v₁) v₂ = put s v₂

/-- Read-only round-trip re-closure: when `Focus (get s)` is unchanged, `LawfulSepLens`
    restores `Whole s` directly via `put_get`. -/
theorem LawfulSepLens.unextract {α β : Type}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : α → SepProp}
    {get : α → β} {put : α → β → α}
    (hL : LawfulSepLens Whole Focus Hole get put) (s : α) :
    Focus (get s) ∗ Hole s ⊢ Whole s := by
  have h := hL.close_entails s (get s)
  rwa [hL.put_get s] at h

/-- Identity `SepLens` on any predicate family `Whole`. -/
theorem SepLens.id {α : Type} (Whole : α → SepProp) :
    SepLens Whole Whole (fun _ => emp) _root_.id (fun _ v' => v') where
  open_entails s := by simp only [_root_.id, sepConj_emp]; exact Entails.refl _
  close_entails _ v' := by simp only [sepConj_emp]; exact Entails.refl _

/-- Identity `LawfulSepLens` on any predicate family `Whole`. -/
theorem LawfulSepLens.id {α : Type} (Whole : α → SepProp) :
    LawfulSepLens Whole Whole (fun _ => emp) _root_.id (fun _ v' => v') where
  toSepLens := SepLens.id Whole
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

/-- Transitive first-order `SepLens` composition (`Whole₁ → Mid` composed with `Mid → Focus`)
    with composite hole `Hole₁ s ∗ Hole₂ (get₁ s)`. -/
theorem SepLens.trans {α β γ : Type}
    {Whole₁ : α → SepProp} {Mid : β → SepProp} {Focus : γ → SepProp}
    {Hole₁ : α → SepProp} {Hole₂ : β → SepProp}
    {get₁ : α → β} {put₁ : α → β → α}
    {get₂ : β → γ} {put₂ : β → γ → β}
    (h₁ : SepLens Whole₁ Mid Hole₁ get₁ put₁)
    (h₂ : SepLens Mid Focus Hole₂ get₂ put₂) :
    SepLens Whole₁ Focus (fun s => Hole₁ s ∗ Hole₂ (get₁ s))
      (fun s => get₂ (get₁ s))
      (fun s v' => put₁ s (put₂ (get₁ s) v')) where
  open_entails s := by
    refine Entails.trans (h₁.open_entails s) ?_
    refine Entails.trans (sepConj_mono_left (h₂.open_entails (get₁ s))) ?_
    rw [sepConj_assoc, sepConj_comm (Hole₂ (get₁ s)) (Hole₁ s)]
    exact Entails.refl _
  close_entails s v' := by
    rw [sepConj_comm (Hole₁ s) (Hole₂ (get₁ s)), ← sepConj_assoc]
    exact Entails.trans (sepConj_mono_left (h₂.close_entails (get₁ s) v'))
      (h₁.close_entails s (put₂ (get₁ s) v'))

/-- Alias for `SepLens.trans`. -/
abbrev SepLens.comp := @SepLens.trans

/-- Transitive composition of `LawfulSepLens` instances preserving all three get/put laws. -/
theorem LawfulSepLens.trans {α β γ : Type}
    {Whole₁ : α → SepProp} {Mid : β → SepProp} {Focus : γ → SepProp}
    {Hole₁ : α → SepProp} {Hole₂ : β → SepProp}
    {get₁ : α → β} {put₁ : α → β → α}
    {get₂ : β → γ} {put₂ : β → γ → β}
    (h₁ : LawfulSepLens Whole₁ Mid Hole₁ get₁ put₁)
    (h₂ : LawfulSepLens Mid Focus Hole₂ get₂ put₂) :
    LawfulSepLens Whole₁ Focus (fun s => Hole₁ s ∗ Hole₂ (get₁ s))
      (fun s => get₂ (get₁ s))
      (fun s v' => put₁ s (put₂ (get₁ s) v')) where
  toSepLens := h₁.toSepLens.trans h₂.toSepLens
  put_get s := by rw [h₂.put_get (get₁ s), h₁.put_get s]
  get_put s v' := by rw [h₁.get_put s (put₂ (get₁ s) v'), h₂.get_put (get₁ s) v']
  put_put s v₁ v₂ := by
    rw [h₁.get_put s (put₂ (get₁ s) v₁), h₂.put_put (get₁ s) v₁ v₂, h₁.put_put]

/-- Alias for `LawfulSepLens.trans`. -/
abbrev LawfulSepLens.comp := @LawfulSepLens.trans

/-- Pure-invariant-guarded predicate family `⌜inv s⌝ ∗ Whole s` for domain-checked lenses
    (such as `i < xs.length` on `pointsToArray` or `off + w ≤ bs.length` on `↦ₛ`). -/
def Guarded {α : Type} (inv : α → Prop) (Whole : α → SepProp) (s : α) : SepProp :=
  ⌜inv s⌝ ∗ Whole s

/-- Lift an unguarded outer lens `Whole₁ → Mid` to propagate an inner domain guard `inv₂`
    whenever `get₁ (put₁ s m') = m'`. -/
theorem SepLens.liftGuard {α β : Type} {inv₂ : β → Prop}
    {Whole₁ : α → SepProp} {Mid : β → SepProp} {Hole₁ : α → SepProp}
    {get₁ : α → β} {put₁ : α → β → α}
    (h₁ : SepLens Whole₁ Mid Hole₁ get₁ put₁)
    (hgp : ∀ s m', get₁ (put₁ s m') = m' := by intros; rfl) :
    SepLens (Guarded (fun s => inv₂ (get₁ s)) Whole₁) (Guarded inv₂ Mid) Hole₁ get₁ put₁ where
  open_entails s := Entails.pure_left fun hinv => by
    refine Entails.trans (h₁.open_entails s) ?_
    exact sepConj_mono_left (Entails.pure_right hinv (Entails.refl _))
  close_entails s m' := by
    unfold Guarded
    rw [sepConj_assoc]
    refine Entails.pure_left fun hinv => ?_
    refine Entails.trans (h₁.close_entails s m') ?_
    refine Entails.pure_right ?_ (Entails.refl _)
    dsimp only
    rw [hgp s m']
    exact hinv

/-- Compose an unguarded outer lens `Whole₁ → Mid` with a domain-guarded inner lens
    `Guarded inv₂ Mid → Focus`. -/
theorem SepLens.trans_guarded {α β γ : Type} {inv₂ : β → Prop}
    {Whole₁ : α → SepProp} {Mid : β → SepProp} {Focus : γ → SepProp}
    {Hole₁ : α → SepProp} {Hole₂ : β → SepProp}
    {get₁ : α → β} {put₁ : α → β → α}
    {get₂ : β → γ} {put₂ : β → γ → β}
    (h₁ : SepLens Whole₁ Mid Hole₁ get₁ put₁)
    (h₂ : SepLens (Guarded inv₂ Mid) Focus Hole₂ get₂ put₂)
    (hgp : ∀ s m', get₁ (put₁ s m') = m' := by intros; rfl) :
    SepLens (Guarded (fun s => inv₂ (get₁ s)) Whole₁) Focus
      (fun s => Hole₁ s ∗ Hole₂ (get₁ s))
      (fun s => get₂ (get₁ s))
      (fun s v' => put₁ s (put₂ (get₁ s) v')) :=
  (h₁.liftGuard hgp).trans h₂

/-- Alias for `SepLens.trans_guarded`. -/
abbrev SepLens.comp_guarded := @SepLens.trans_guarded

/-- Compose a domain-guarded outer lens `Guarded inv₁ Whole₁ → Mid` with a domain-guarded
    inner lens `Guarded inv₂ Mid → Focus` when `inv₁ s → get₁ (put₁ s m') = m'`. -/
theorem SepLens.trans_both_guarded {α β γ : Type} {inv₁ : α → Prop} {inv₂ : β → Prop}
    {Whole₁ : α → SepProp} {Mid : β → SepProp} {Focus : γ → SepProp}
    {Hole₁ : α → SepProp} {Hole₂ : β → SepProp}
    {get₁ : α → β} {put₁ : α → β → α}
    {get₂ : β → γ} {put₂ : β → γ → β}
    (h₁ : SepLens (Guarded inv₁ Whole₁) Mid Hole₁ get₁ put₁)
    (h₂ : SepLens (Guarded inv₂ Mid) Focus Hole₂ get₂ put₂)
    (hgp : ∀ s m', inv₁ s → get₁ (put₁ s m') = m') :
    SepLens (Guarded (fun s => inv₁ s ∧ inv₂ (get₁ s)) Whole₁) Focus
      (fun s => ⌜inv₁ s⌝ ∗ Hole₁ s ∗ Hole₂ (get₁ s))
      (fun s => get₂ (get₁ s))
      (fun s v' => put₁ s (put₂ (get₁ s) v')) where
  open_entails s := Entails.pure_left fun ⟨hi₁, hi₂⟩ => by
    have hop₁ := Entails.trans (Entails.pure_right hi₁ (Entails.refl _)) (h₁.open_entails s)
    have hop₂ : Mid (get₁ s) ⊢ Focus (get₂ (get₁ s)) ∗ Hole₂ (get₁ s) :=
      Entails.trans (Entails.pure_right hi₂ (Entails.refl _)) (h₂.open_entails (get₁ s))
    refine Entails.trans hop₁ ?_
    refine Entails.trans (sepConj_mono_left hop₂) ?_
    rw [sepConj_assoc, sepConj_comm (Hole₂ (get₁ s)) (Hole₁ s)]
    exact sepConj_mono_right (Entails.pure_right hi₁ (Entails.refl _))
  close_entails s v' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun hi₁ => ?_
    rw [sepConj_comm (Hole₁ s) (Hole₂ (get₁ s)), ← sepConj_assoc]
    have hcl₂ := h₂.close_entails (get₁ s) v'
    unfold Guarded at hcl₂ ⊢
    refine Entails.trans (sepConj_mono_left hcl₂) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hi₂ => ?_
    refine Entails.trans (h₁.close_entails s (put₂ (get₁ s) v')) ?_
    refine Entails.pure_left fun hi₁' => ?_
    refine Entails.pure_right ⟨hi₁', ?_⟩ (Entails.refl _)
    rw [hgp s (put₂ (get₁ s) v') hi₁]
    exact hi₂

/-- Pointwise instantiation of a `SepLens` at a concrete snapshot `s : α`, uniformly erasing
    any `Guarded` domain obligation once discharged at open time. -/
structure SepLensAt {α β : Type} (Whole : α → SepProp) (Focus : β → SepProp)
    (Hole : SepProp) (s : α) (val : β) (put : β → α) : Prop where
  open_at  : Whole s ⊢ Focus val ∗ Hole
  close_at : ∀ v', Focus v' ∗ Hole ⊢ Whole (put v')

/-- Instantiate an unguarded `SepLens` at snapshot `s`. -/
theorem SepLens.atState {α β : Type}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : α → SepProp}
    {get : α → β} {put : α → β → α}
    (h : SepLens Whole Focus Hole get put) (s : α) :
    SepLensAt Whole Focus (Hole s) s (get s) (put s) where
  open_at := h.open_entails s
  close_at v' := h.close_entails s v'

/-- Instantiate a `LawfulSepLens` at snapshot `s`. -/
theorem LawfulSepLens.atState {α β : Type}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : α → SepProp}
    {get : α → β} {put : α → β → α}
    (h : LawfulSepLens Whole Focus Hole get put) (s : α) :
    SepLensAt Whole Focus (Hole s) s (get s) (put s) :=
  h.toSepLens.atState s

/-- Instantiate a `Guarded` `SepLens` at snapshot `s` using `hinv : inv s`, returning an
    unguarded `SepLensAt` on `Whole`. -/
theorem SepLens.atGuarded {α β : Type} {inv : α → Prop}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : α → SepProp}
    {get : α → β} {put : α → β → α}
    (h : SepLens (Guarded inv Whole) Focus Hole get put) (s : α) (hinv : inv s) :
    SepLensAt Whole Focus (Hole s) s (get s) (put s) where
  open_at := Entails.trans (Entails.pure_right hinv (Entails.refl _)) (h.open_entails s)
  close_at v' := Entails.trans (h.close_entails s v') (Entails.pure_left fun _ => Entails.refl _)

/-- Spine marker wrapping an open lens hole together with its `SepLensAt` certificate (and optional
    `put val = s` round-trip witness when `isLawful = true`) so `lens_switch` and `lens_close`
    never re-prove or unfold the hole. -/
def LensOpen {α β : Type} (Whole : α → SepProp) (Focus : β → SepProp)
    (Hole : SepProp) (s : α) (val : β) (put : β → α)
    (_hL : SepLensAt Whole Focus Hole s val put)
    {isLawful : Bool} (_hpg : if isLawful then put val = s else True := by trivial) : SepProp :=
  Hole

/-- Scoped open-step-close combinator on `SepWP`: opens `Whole s` out of `P`, frames `Hole ∗ Frame`
    around a multi-step `hbody` operating solely on `Focus val`, and re-closes `Focus v' ∗ Hole`
    into `Whole (put v')`. -/
theorem sepWP_with_lens {α β : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Frame : SepProp} {Q : State → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : SepProp}
    {s : α} {val v' : β} {put : β → α}
    (hL : SepLensAt Whole Focus Hole s val put)
    (hfocus : P = Whole s ∗ Frame := by sep_focus)
    (hbody : SepWP prog target_pc st (Focus val)
      (fun sf Pf => (Pf ⊢ Focus v') ∧ Q sf) oom) :
    SepWP prog target_pc st P
      (fun sf Pf => (Pf ⊢ Whole (put v') ∗ Frame) ∧ Q sf) oom := by
  rw [hfocus]
  have hop : Whole s ∗ Frame ⊢ Focus val ∗ (Hole ∗ Frame) := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left hL.open_at
  refine SepWP.weaken_pre hop ?_
  refine SepWP.mono (SepWP.frame_post_entails (F := Hole ∗ Frame) hbody) ?_ (fun _ _ _ ho => ho)
  intro sf Pf _ _ ⟨hPf, hQ⟩
  refine ⟨Entails.trans hPf ?_, hQ⟩
  rw [← sepConj_assoc]
  exact sepConj_mono_left (hL.close_at v')

/-- Dot-notation alias for `sepWP_with_lens`. -/
abbrev SepLensAt.with_sepWP := @sepWP_with_lens

/-- Continuation-passing `SepWP` lens open: extracts `Focus val` to the head of `P` and parks
    the remaining fields in a single `LensOpen` spine token. -/
theorem sepWP_open_lens {α β : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : SepProp}
    {s : α} {val : β} {put : β → α}
    {isLawful : Bool}
    (hL : SepLensAt Whole Focus Hole s val put)
    (hpg : if isLawful then put val = s else True)
    (hfocus : P = Whole s ∗ Frame)
    (h : SepWP prog target_pc st
      (Focus val ∗ (LensOpen Whole Focus Hole s val put hL (isLawful := isLawful) hpg ∗ Frame))
      post oom) :
    SepWP prog target_pc st P post oom := by
  rw [hfocus]
  refine SepWP.weaken_pre ?_ h
  rw [← sepConj_assoc]
  exact sepConj_mono_left hL.open_at

/-- Continuation-passing `SepWP` lens close: folds `Focus v'` and `LensOpen` back into `Whole s'`
    given `put v' = s'` (which is `rfl` when mutated and `put_get` when unchanged). -/
theorem sepWP_close_lens_eq {α β : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Rest Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : SepProp}
    {s s' : α} {val v' : β} {put : β → α}
    {hL : SepLensAt Whole Focus Hole s val put}
    {isLawful : Bool} {hpg : if isLawful then put val = s else True}
    (hopen : P = LensOpen Whole Focus Hole s val put hL (isLawful := isLawful) hpg ∗ Rest)
    (hval : Rest = Focus v' ∗ Frame)
    (heq : put v' = s')
    (h : SepWP prog target_pc st (Whole s' ∗ Frame) post oom) :
    SepWP prog target_pc st P post oom := by
  subst heq
  rw [hopen, hval, ← sepConj_assoc,
      sepConj_comm (LensOpen Whole Focus Hole s val put hL (isLawful := isLawful) hpg) (Focus v')]
  exact SepWP.weaken_pre (sepConj_mono_left (hL.close_at v')) h

/-- Continuation-passing `SepWP` lens close with `s' := put v'`. -/
theorem sepWP_close_lens {α β : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Rest Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus : β → SepProp} {Hole : SepProp}
    {s : α} {val v' : β} {put : β → α}
    {hL : SepLensAt Whole Focus Hole s val put}
    {isLawful : Bool} {hpg : if isLawful then put val = s else True}
    (hopen : P = LensOpen Whole Focus Hole s val put hL (isLawful := isLawful) hpg ∗ Rest)
    (hval : Rest = Focus v' ∗ Frame)
    (h : SepWP prog target_pc st (Whole (put v') ∗ Frame) post oom) :
    SepWP prog target_pc st P post oom :=
  sepWP_close_lens_eq hopen hval rfl h

/-- Switch active focus between two lenses on the same composite `Whole` in one combinator step. -/
theorem sepWP_switch_lens_eq {α β₁ β₂ : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Rest Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus₁ : β₁ → SepProp} {Focus₂ : β₂ → SepProp}
    {Hole₁ Hole₂ : SepProp}
    {s sMid : α} {val₁ v₁' : β₁} {put₁ : β₁ → α}
    {hL₁ : SepLensAt Whole Focus₁ Hole₁ s val₁ put₁}
    {isLawful₁ : Bool} {hpg₁ : if isLawful₁ then put₁ val₁ = s else True}
    {val₂ : β₂} {put₂ : β₂ → α}
    {isLawful₂ : Bool}
    (hopen : P = LensOpen Whole Focus₁ Hole₁ s val₁ put₁ hL₁ (isLawful := isLawful₁) hpg₁ ∗ Rest)
    (hval : Rest = Focus₁ v₁' ∗ Frame)
    (heq : put₁ v₁' = sMid)
    (hL₂ : SepLensAt Whole Focus₂ Hole₂ sMid val₂ put₂)
    (hpg₂ : if isLawful₂ then put₂ val₂ = sMid else True)
    (h : SepWP prog target_pc st
      (Focus₂ val₂ ∗
        (LensOpen Whole Focus₂ Hole₂ sMid val₂ put₂ hL₂ (isLawful := isLawful₂) hpg₂ ∗ Frame))
      post oom) :
    SepWP prog target_pc st P post oom :=
  sepWP_close_lens_eq hopen hval heq (sepWP_open_lens hL₂ hpg₂ rfl h)

/-- Switch active focus between two lenses on `Whole` with `sMid := put₁ v₁'`. -/
theorem sepWP_switch_lens {α β₁ β₂ : Type}
    {prog : Program} {target_pc : BitVec 64} {st : State}
    {P Rest Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {Whole : α → SepProp} {Focus₁ : β₁ → SepProp} {Focus₂ : β₂ → SepProp}
    {Hole₁ Hole₂ : SepProp}
    {s : α} {val₁ v₁' : β₁} {put₁ : β₁ → α}
    {hL₁ : SepLensAt Whole Focus₁ Hole₁ s val₁ put₁}
    {isLawful₁ : Bool} {hpg₁ : if isLawful₁ then put₁ val₁ = s else True}
    {val₂ : β₂} {put₂ : β₂ → α}
    {isLawful₂ : Bool}
    (hopen : P = LensOpen Whole Focus₁ Hole₁ s val₁ put₁ hL₁ (isLawful := isLawful₁) hpg₁ ∗ Rest)
    (hval : Rest = Focus₁ v₁' ∗ Frame)
    (hL₂ : SepLensAt Whole Focus₂ Hole₂ (put₁ v₁') val₂ put₂)
    (hpg₂ : if isLawful₂ then put₂ val₂ = put₁ v₁' else True)
    (h : SepWP prog target_pc st
      (Focus₂ val₂ ∗
        (LensOpen Whole Focus₂ Hole₂ (put₁ v₁') val₂ put₂ hL₂ (isLawful := isLawful₂) hpg₂ ∗ Frame))
      post oom) :
    SepWP prog target_pc st P post oom :=
  sepWP_switch_lens_eq hopen hval rfl hL₂ hpg₂ h

/-! ## 2(a). Declarative `StructLayout`, Padding, Small-Struct Fast Path, & Stack Reclaim -/

/-- Canonical field pointer `p` at offset `0` and `p + BitVec.ofNat 64 off` for `off > 0`. -/
abbrev fieldAddr (p : BitVec 64) (off : Nat) : BitVec 64 :=
  if off == 0 then p else p + BitVec.ofNat 64 off

theorem fieldAddr_eq_add (p : BitVec 64) (off : Nat) :
    fieldAddr p off = p + BitVec.ofNat 64 off := by
  unfold fieldAddr
  split <;> rename_i h
  · simp only [beq_iff_eq] at h
    subst h
    simp
  · rfl

theorem pointsToArray_to_memRegion {α : Type} (stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (helem : ∀ p x, elemAt p x ⊢ memRegion p stride)
    (xs : List α) (p : BitVec 64) (h : stride * xs.length ≤ 2 ^ 64) :
    pointsToArray stride elemAt p xs ⊢ memRegion p (stride * xs.length) := by
  induction xs generalizing p with
  | nil =>
    rw [List.length_nil, Nat.mul_zero, memRegion_zero, pointsToArray_nil]
    exact Entails.refl _
  | cons x xs ih =>
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm] at h ⊢
    rw [pointsToArray_cons,
        memRegion_split_le p stride (stride + stride * xs.length) (by omega) (by omega)]
    rw [show stride + stride * xs.length - stride = stride * xs.length by omega]
    exact sepConj_mono (helem p x) (ih (p + BitVec.ofNat 64 stride) (by omega))

/-- Classification of a `StructField` entry for layout validation and small-struct fast-path
    dispatch. -/
inductive StructFieldKind where
  | u8
  | u16
  | u32
  | u64
  | u128
  | pad
  | slice
  | subArray
  | dynArray
  deriving DecidableEq, Repr, Inhabited, BEq

namespace StructFieldKind

/-- True when a field is a fixed-width scalar (`u8`, `u16`, `u32`, `u64`, `u128`) without
    padding, byte slices, or embedded/dynamic arrays. -/
@[expose] def isFixedScalar : StructFieldKind → Bool
  | .u8 | .u16 | .u32 | .u64 | .u128 => true
  | .pad | .slice | .subArray | .dynArray => false

/-- True when a field is a variable-length trailing `dynArray`. -/
@[expose] def isDynArray : StructFieldKind → Bool
  | .dynArray => true
  | _ => false

end StructFieldKind

/-- Descriptor for a single field or padding region in a C/Rust `StructLayout` over pure snapshot
    type `M` (zero existential binders). -/
structure StructField (M : Type) where
  kind      : StructFieldKind
  off       : Nat
  sz        : Nat
  render    : BitVec 64 → M → SepProp
  valid     : M → Prop := fun _ => True
  to_region : ∀ p m, valid m → sz ≤ 2 ^ 64 →
    render p m ⊢ memRegion (p + BitVec.ofNat 64 off) sz

namespace StructField

/-- 8-bit scalar field `(p + off) ↦₈ get m`. -/
@[expose] def field8 {M : Type} (off : Nat) (get : M → BitVec 8) : StructField M where
  kind := .u8
  off := off
  sz := 1
  render p m := (fieldAddr p off) ↦₈ get m
  to_region p m _ _ := by rw [← fieldAddr_eq_add]; exact pointsTo8_entails_memRegion _ _

/-- Alias for `StructField.field8`. -/
abbrev u8 := @field8

/-- 16-bit scalar field `(p + off) ↦₁₆ get m`. -/
@[expose] def field16 {M : Type} (off : Nat) (get : M → BitVec 16) : StructField M where
  kind := .u16
  off := off
  sz := 2
  render p m := (fieldAddr p off) ↦₁₆ get m
  to_region p m _ _ := by rw [← fieldAddr_eq_add]; exact pointsTo16_entails_memRegion _ _

/-- Alias for `StructField.field16`. -/
abbrev u16 := @field16

/-- 32-bit scalar field `(p + off) ↦₃₂ get m`. -/
@[expose] def field32 {M : Type} (off : Nat) (get : M → BitVec 32) : StructField M where
  kind := .u32
  off := off
  sz := 4
  render p m := (fieldAddr p off) ↦₃₂ get m
  to_region p m _ _ := by rw [← fieldAddr_eq_add]; exact pointsTo32_entails_memRegion _ _

/-- Alias for `StructField.field32`. -/
abbrev u32 := @field32

/-- 64-bit scalar field `(p + off) ↦₆₄ get m`. -/
@[expose] def field64 {M : Type} (off : Nat) (get : M → BitVec 64) : StructField M where
  kind := .u64
  off := off
  sz := 8
  render p m := (fieldAddr p off) ↦₆₄ get m
  to_region p m _ _ := by rw [← fieldAddr_eq_add]; exact pointsTo64_entails_memRegion _ _

/-- Alias for `StructField.field64`. -/
abbrev u64 := @field64

/-- 128-bit scalar field `(p + off) ↦₁₂₈ get m`. -/
@[expose] def field128 {M : Type} (off : Nat) (get : M → BitVec 128) : StructField M where
  kind := .u128
  off := off
  sz := 16
  render p m := (fieldAddr p off) ↦₁₂₈ get m
  to_region p m _ _ := by rw [← fieldAddr_eq_add]; exact pointsTo128_entails_memRegion _ _

/-- Alias for `StructField.field128`. -/
abbrev u128 := @field128

/-- Uninitialized / alignment padding `[p + off, p + off + sz)` modeled as `memRegion`. -/
@[expose] def pad (M : Type) (off sz : Nat) : StructField M where
  kind := .pad
  off := off
  sz := sz
  render p _ := memRegion (fieldAddr p off) sz
  to_region p _ _ _ := by rw [← fieldAddr_eq_add]; exact Entails.refl _

/-- Fixed-size embedded byte-slice field `(p + off) ↦ₛ get m` of `sz` bytes. -/
@[expose] def slice {M : Type} (off sz : Nat) (get : M → List (BitVec 8)) : StructField M where
  kind := .slice
  off := off
  sz := sz
  render p m := (fieldAddr p off) ↦ₛ get m
  valid m := (get m).length = sz
  to_region p m hlen _ := by
    rw [← fieldAddr_eq_add]
    exact pointsToBytes_entails_memRegion_of_length hlen

/-- Fixed-count embedded sub-array `pointsToArray stride elemAt (p + off) (get m)`. -/
@[expose] def subArray {M α : Type} (off stride cnt : Nat) (elemAt : BitVec 64 → α → SepProp)
    (helem : ∀ q x, elemAt q x ⊢ memRegion q stride) (get : M → List α) : StructField M where
  kind := .subArray
  off := off
  sz := stride * cnt
  render p m := pointsToArray stride elemAt (fieldAddr p off) (get m)
  valid m := (get m).length = cnt
  to_region p m hlen hsz := by
    rw [← fieldAddr_eq_add, ← hlen]
    exact pointsToArray_to_memRegion stride elemAt helem (get m) (fieldAddr p off)
      (by simpa [hlen] using hsz)

/-- Variable-length / flexible-array-member field `pointsToArray stride elemAt (p + off) (get m)`. -/
@[expose] def dynArray {M α : Type} (off stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (get : M → List α) : StructField M where
  kind := .dynArray
  off := off
  sz := 0
  render p m := pointsToArray stride elemAt (fieldAddr p off) (get m)
  valid _ := False
  to_region _ _ hv _ := False.elim hv

end StructField

/-- Emit implicit alignment gap `memRegion` when `cur < off`, else `R` unchanged. -/
@[expose] def renderWithGap (p : BitVec 64) (cur off : Nat) (R : SepProp) : SepProp :=
  if cur < off then memRegion (fieldAddr p cur) (off - cur) ∗ R else R

/-- Emit trailing alignment padding `memRegion` when `cur < totalSz`, else `emp`. -/
@[expose] def renderTailGap (p : BitVec 64) (cur totalSz : Nat) : SepProp :=
  if cur < totalSz then memRegion (fieldAddr p cur) (totalSz - cur) else emp

/-- Render `StructField`s starting from byte cursor `cur` up to `totalSz`, automatically turning
    any unmentioned alignment gaps into `memRegion` slices. -/
@[expose] def fieldsRenderAt {M : Type} (p : BitVec 64) (m : M) (cur totalSz : Nat) :
    List (StructField M) → SepProp
  | [] => renderTailGap p cur totalSz
  | f :: fs =>
    renderWithGap p cur f.off (f.render p m) ∗ fieldsRenderAt p m (f.off + f.sz) totalSz fs

/-- Spine-only hole remaining when field `idx` is focused out of `fieldsRenderAt`. -/
@[expose] def fieldsHoleAt {M : Type} (p : BitVec 64) (m : M) (cur totalSz : Nat) :
    List (StructField M) → Nat → SepProp
  | [], _ => renderTailGap p cur totalSz
  | f :: fs, 0 =>
    renderWithGap p cur f.off (fieldsRenderAt p m (f.off + f.sz) totalSz fs)
  | f :: fs, idx + 1 =>
    renderWithGap p cur f.off (f.render p m) ∗ fieldsHoleAt p m (f.off + f.sz) totalSz fs idx

/-- Conjunction of per-field length invariants. -/
@[expose] def fieldsValid {M : Type} (m : M) : List (StructField M) → Prop
  | [] => True
  | f :: fs => f.valid m ∧ fieldsValid m fs

/-- Exact contiguity check without gaps (`cur == f.off` at every step and final `cur == totalSz`). -/
@[expose] def fieldsContiguousAt {M : Type} (cur : Nat) : List (StructField M) → Nat → Bool
  | [], totalSz => cur == totalSz
  | f :: fs, totalSz => (f.off == cur) && fieldsContiguousAt (cur + f.sz) fs totalSz

/-- Layout well-formedness check rejecting overlapping fields (`f.off < cur`), out-of-bounds
    fields (`f.off + f.sz > totalSz`), `totalSz > 2 ^ 64`, and non-terminal `dynArray` fields. -/
@[expose] def fieldsWellFormedAt {M : Type} (cur : Nat) : List (StructField M) → Nat → Bool
  | [], totalSz => Nat.ble cur totalSz && Nat.ble totalSz 0x10000000000000000
  | [f], totalSz =>
    if f.kind.isDynArray then
      Nat.ble cur f.off && (f.off == totalSz) && Nat.ble totalSz 0x10000000000000000
    else
      Nat.ble cur f.off && Nat.ble (f.off + f.sz) totalSz && Nat.ble totalSz 0x10000000000000000
  | f :: fs, totalSz =>
    (!f.kind.isDynArray) && Nat.ble cur f.off &&
      fieldsWellFormedAt (f.off + f.sz) fs totalSz

/-- Fixed-size reclaimability check: well-formed and free of trailing `dynArray` fields. -/
@[expose] def fieldsReclaimableAt {M : Type} (cur : Nat) : List (StructField M) → Nat → Bool
  | [], totalSz => Nat.ble cur totalSz && Nat.ble totalSz 0x10000000000000000
  | f :: fs, totalSz =>
    (!f.kind.isDynArray) && Nat.ble cur f.off &&
      fieldsReclaimableAt (f.off + f.sz) fs totalSz

theorem fieldsRenderAt_focus {M : Type} (p : BitVec 64) (m : M) :
    ∀ (cur totalSz : Nat) (fs : List (StructField M)) (idx : Nat) (hidx : idx < fs.length),
      fieldsRenderAt p m cur totalSz fs =
        (fs[idx]'hidx).render p m ∗ fieldsHoleAt p m cur totalSz fs idx
  | _, _, [], _, hidx => absurd hidx (Nat.not_lt_zero _)
  | cur, totalSz, f :: fs, 0, _ => by
    dsimp only [fieldsRenderAt, fieldsHoleAt, renderWithGap, List.getElem_cons_zero]
    split
    · rw [sepConj_comm (memRegion _ _) (f.render p m), sepConj_assoc]
    · rfl
  | cur, totalSz, f :: fs, idx + 1, hidx => by
    have hlt : idx < fs.length := Nat.lt_of_succ_lt_succ hidx
    dsimp only [fieldsRenderAt, fieldsHoleAt, List.getElem_cons_succ]
    rw [fieldsRenderAt_focus p m (f.off + f.sz) totalSz fs idx hlt, ← sepConj_assoc,
        sepConj_comm (renderWithGap p cur f.off (f.render p m)) ((fs[idx]'hlt).render p m),
        sepConj_assoc]

theorem fieldsReclaimableAt_le {M : Type} (fs : List (StructField M)) (cur totalSz : Nat)
    (h : fieldsReclaimableAt cur fs totalSz = true) :
    cur ≤ totalSz ∧ totalSz ≤ 2 ^ 64 := by
  induction fs generalizing cur with
  | nil =>
    simp only [fieldsReclaimableAt, Bool.and_eq_true] at h
    exact ⟨Nat.le_of_ble_eq_true h.1, le_two_pow_64_of_ble h.2⟩
  | cons f fs ih =>
    simp only [fieldsReclaimableAt, Bool.and_eq_true] at h
    have hcur : cur ≤ f.off := Nat.le_of_ble_eq_true h.1.2
    have ⟨hrest, hb⟩ := ih (f.off + f.sz) h.2
    exact ⟨by omega, hb⟩

theorem fieldsRenderAt_to_memRegion {M : Type} (p : BitVec 64) (m : M)
    (fs : List (StructField M)) (cur totalSz : Nat)
    (hrec : fieldsReclaimableAt cur fs totalSz = true)
    (hval : fieldsValid m fs) :
    fieldsRenderAt p m cur totalSz fs ⊢ memRegion (p + BitVec.ofNat 64 cur) (totalSz - cur) := by
  induction fs generalizing cur with
  | nil =>
    have ⟨hle, _⟩ := fieldsReclaimableAt_le ([] : List (StructField M)) cur totalSz hrec
    dsimp only [fieldsRenderAt, renderTailGap]
    split <;> rename_i hlt
    · rw [fieldAddr_eq_add]
      exact Entails.refl _
    · have heq : totalSz - cur = 0 := by omega
      rw [heq, memRegion_zero]
      exact Entails.refl _
  | cons f fs ih =>
    simp only [fieldsReclaimableAt, Bool.and_eq_true] at hrec
    have hcur : cur ≤ f.off := Nat.le_of_ble_eq_true hrec.1.2
    have ⟨hend, hbound⟩ := fieldsReclaimableAt_le fs (f.off + f.sz) totalSz hrec.2
    rcases hval with ⟨hvf, hvfs⟩
    have hhead : renderWithGap p cur f.off (f.render p m) ⊢
        memRegion (p + BitVec.ofNat 64 cur) (f.off + f.sz - cur) := by
      dsimp only [renderWithGap]
      split <;> rename_i hlt
      · rw [fieldAddr_eq_add,
            memRegion_split_le (p + BitVec.ofNat 64 cur) (f.off - cur) (f.off + f.sz - cur)
              (by omega) (by omega)]
        have hadd : p + BitVec.ofNat 64 cur + BitVec.ofNat 64 (f.off - cur) =
            p + BitVec.ofNat 64 f.off := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, show cur + (f.off - cur) = f.off by omega]
        have hsub : f.off + f.sz - cur - (f.off - cur) = f.sz := by omega
        rw [hadd, hsub]
        exact sepConj_mono_right (f.to_region p m hvf (by omega))
      · have heq : f.off = cur := by omega
        rw [heq, show cur + f.sz - cur = f.sz by omega]
        have hf := f.to_region p m hvf (by omega)
        rwa [heq] at hf
    rw [memRegion_split_le (p + BitVec.ofNat 64 cur) (f.off + f.sz - cur) (totalSz - cur)
        (by omega) (by omega)]
    have hadd2 : p + BitVec.ofNat 64 cur + BitVec.ofNat 64 (f.off + f.sz - cur) =
        p + BitVec.ofNat 64 (f.off + f.sz) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
          show cur + (f.off + f.sz - cur) = f.off + f.sz by omega]
    have hsub2 : totalSz - cur - (f.off + f.sz - cur) = totalSz - (f.off + f.sz) := by omega
    rw [hadd2, hsub2]
    exact sepConj_mono hhead (ih (f.off + f.sz) hrec.2 hvfs)

/-- Declarative C/Rust struct layout parameterized by pure model snapshot `M`. -/
structure StructLayout (M : Type) where
  totalSz : Nat
  fields  : List (StructField M)

namespace StructLayout

/-- Composite ownership of struct `L` at base pointer `p` with pure snapshot `m : M`. -/
@[expose] def own {M : Type} (L : StructLayout M) (p : BitVec 64) (m : M) : SepProp :=
  fieldsRenderAt p m 0 L.totalSz L.fields

/-- Packed spine-only hole when field `idx` is focused out of `L.own p m`. -/
@[expose] def hole {M : Type} (L : StructLayout M) (idx : Nat) (p : BitVec 64) (m : M) : SepProp :=
  fieldsHoleAt p m 0 L.totalSz L.fields idx

/-- Field-level length invariants (trivial `True` for all scalar and `pad` fields). -/
@[expose] def valid {M : Type} (L : StructLayout M) (m : M) : Prop :=
  fieldsValid m L.fields

/-- Layout well-formedness: non-overlapping ascending offsets within `[0, L.totalSz]` and
    `L.totalSz ≤ 2 ^ 64`. -/
@[expose] def wf {M : Type} (L : StructLayout M) : Bool :=
  fieldsWellFormedAt 0 L.fields L.totalSz

/-- True when `L` is well-formed and has no variable-length `dynArray` tail, so `L.own p m`
    collapses to `memRegion p L.totalSz`. -/
@[expose] def reclaimable {M : Type} (L : StructLayout M) : Bool :=
  fieldsReclaimableAt 0 L.fields L.totalSz

/-- Adaptive fast-path predicate: true when `L` is well-formed, has `fields.length ≤ 6`, and
    every field is a fixed-width scalar (`u8`, `u16`, `u32`, `u64`, `u128`) without explicit
    padding, byte slices, or sub/dynamic arrays. -/
@[expose] def isSmallFlatScalar {M : Type} (L : StructLayout M) : Bool :=
  L.wf && Nat.ble L.fields.length 6 && L.fields.all (fun f => f.kind.isFixedScalar)

/-- Automatic spine-only per-field `SepLens` for field `idx` of a well-formed `StructLayout`. -/
theorem fieldLens {M β : Type} (L : StructLayout M)
    (idx : Nat) (p : BitVec 64) (Focus : β → SepProp)
    (get : M → β) (put : M → β → M)
    (_hwf : L.wf = true := by decide)
    (hidx : idx < L.fields.length := by decide)
    (hget : ∀ m, (L.fields[idx]'hidx).render p m = Focus (get m) := by intros; rfl)
    (hput : ∀ m v', (L.fields[idx]'hidx).render p (put m v') = Focus v' := by intros; rfl)
    (hhole : ∀ m v', L.hole idx p (put m v') = L.hole idx p m := by intros; rfl) :
    SepLens (L.own p) Focus (L.hole idx p) get put where
  open_entails m := by
    refine Entails.of_eq ?_
    unfold StructLayout.own StructLayout.hole
    rw [fieldsRenderAt_focus p m 0 L.totalSz L.fields idx hidx, hget m]
  close_entails m v' := by
    refine Entails.of_eq ?_
    unfold StructLayout.own
    rw [fieldsRenderAt_focus p (put m v') 0 L.totalSz L.fields idx hidx, hput m v']
    exact congrArg (Focus v' ∗ ·) (hhole m v').symm

/-- Automatic per-field `LawfulSepLens` for field `idx` of a well-formed `StructLayout` over
    any Lean `structure M`. -/
theorem lawfulFieldLens {M β : Type} (L : StructLayout M)
    (idx : Nat) (p : BitVec 64) (Focus : β → SepProp)
    (get : M → β) (put : M → β → M)
    (hwf : L.wf = true := by decide)
    (hidx : idx < L.fields.length := by decide)
    (hget : ∀ m, (L.fields[idx]'hidx).render p m = Focus (get m) := by intros; rfl)
    (hput : ∀ m v', (L.fields[idx]'hidx).render p (put m v') = Focus v' := by intros; rfl)
    (hhole : ∀ m v', L.hole idx p (put m v') = L.hole idx p m := by intros; rfl)
    (hpg : ∀ m, put m (get m) = m := by intros; rfl)
    (hgp : ∀ m v', get (put m v') = v' := by intros; rfl)
    (hpp : ∀ m v₁ v₂, put (put m v₁) v₂ = put m v₂ := by intros; rfl) :
    LawfulSepLens (L.own p) Focus (L.hole idx p) get put where
  toSepLens := L.fieldLens idx p Focus get put hwf hidx hget hput hhole
  put_get := hpg
  get_put := hgp
  put_put := hpp

/-- Automatic 1-step stack reclamation: any fixed-size well-formed `StructLayout` (mixing scalars,
    explicit/implicit padding, and fixed-size slices/sub-arrays) collapses to `memRegion p L.totalSz`. -/
theorem struct_to_memRegion {M : Type} (L : StructLayout M) (p : BitVec 64) (m : M)
    (hrec : L.reclaimable = true := by decide)
    (hvalid : L.valid m := by trivial) :
    L.own p m ⊢ memRegion p L.totalSz := by
  unfold StructLayout.own
  have h := fieldsRenderAt_to_memRegion p m L.fields 0 L.totalSz hrec hvalid
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero] using h

/-- Alias for `StructLayout.struct_to_memRegion`. -/
abbrev to_memRegion := @struct_to_memRegion

end StructLayout

/-! ## 2(b). Symbolic-Offset Array & Downward-Bucket Lenses (`pointsToArray` & `slotsDownFrom`) -/

/-- Round-trip identity `xs.set i (xs.getD i d) = xs` for any `List` and index `i`. -/
theorem list_set_getD_self {α : Type} (xs : List α) (i : Nat) (d : α) :
    xs.set i (xs.getD i d) = xs := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        List.set_getElem_self]
  · exact List.set_eq_of_length_le (by omega)

@[sep_lens]
/-- Symbolic-index `SepLens` focusing element `i` of `pointsToArray stride elemAt base`. -/
theorem pointsToArray_lens {α : Type} [Inhabited α] (stride : Nat)
    (elemAt : BitVec 64 → α → SepProp) (base : BitVec 64) (i : Nat) :
    SepLens
      (Guarded (fun xs : List α => i < xs.length) (pointsToArray stride elemAt base))
      (elemAt (base + BitVec.ofNat 64 (stride * i)))
      (fun xs => ⌜i < xs.length⌝ ∗
        (pointsToArray stride elemAt base (xs.take i) ∗
         pointsToArray stride elemAt (base + BitVec.ofNat 64 (stride * (i + 1))) (xs.drop (i + 1))))
      (fun xs => xs.getD i default)
      (fun xs v' => xs.set i v') where
  open_entails xs := Entails.pure_left fun hi => by
    rw [pointsToArray_focus stride elemAt base xs i hi]
    exact sepConj_mono_right (Entails.pure_right hi (Entails.refl _))
  close_entails xs v' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun hi => ?_
    rw [pointsToArray_update stride elemAt base xs i v' hi]
    exact Entails.pure_right (by dsimp only; rw [List.length_set]; exact hi) (Entails.refl _)

@[sep_lens]
/-- Hardware `LSL`-addressed `pointsToArray` `SepLens` at `base + (BitVec.ofNat 64 i <<< shift)`. -/
theorem pointsToArray_shift_lens {α : Type} [Inhabited α] (shift : Nat)
    (elemAt : BitVec 64 → α → SepProp) (base : BitVec 64) (i : Nat) :
    SepLens
      (Guarded (fun xs : List α => i < xs.length ∧ (2 ^ shift) * i < 2 ^ 64)
        (pointsToArray (2 ^ shift) elemAt base))
      (elemAt (base + (BitVec.ofNat 64 i <<< shift)))
      (fun xs => ⌜i < xs.length ∧ (2 ^ shift) * i < 2 ^ 64⌝ ∗
        (pointsToArray (2 ^ shift) elemAt base (xs.take i) ∗
         pointsToArray (2 ^ shift) elemAt
           (base + BitVec.ofNat 64 ((2 ^ shift) * (i + 1))) (xs.drop (i + 1))))
      (fun xs => xs.getD i default)
      (fun xs v' => xs.set i v') where
  open_entails xs := Entails.pure_left fun ⟨hi, hsh⟩ => by
    have hi_lt : i < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left i (Nat.two_pow_pos shift)) hsh
    have hmul : i * (2 ^ shift) < 2 ^ 64 := by rw [Nat.mul_comm]; exact hsh
    have heq : BitVec.ofNat 64 i <<< shift = BitVec.ofNat 64 ((2 ^ shift) * i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi_lt,
          Nat.shiftLeft_eq, Nat.mod_eq_of_lt hmul, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hsh, Nat.mul_comm]
    rw [heq, pointsToArray_focus (2 ^ shift) elemAt base xs i hi]
    exact sepConj_mono_right (Entails.pure_right ⟨hi, hsh⟩ (Entails.refl _))
  close_entails xs v' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun ⟨hi, hsh⟩ => ?_
    have hi_lt : i < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left i (Nat.two_pow_pos shift)) hsh
    have hmul : i * (2 ^ shift) < 2 ^ 64 := by rw [Nat.mul_comm]; exact hsh
    have heq : BitVec.ofNat 64 i <<< shift = BitVec.ofNat 64 ((2 ^ shift) * i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi_lt,
          Nat.shiftLeft_eq, Nat.mod_eq_of_lt hmul, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hsh, Nat.mul_comm]
    rw [heq, pointsToArray_update (2 ^ shift) elemAt base xs i v' hi]
    exact Entails.pure_right ⟨by rw [List.length_set]; exact hi, hsh⟩ (Entails.refl _)

/-- 16-byte `(first, second)` 64-bit word pair at `p`. -/
abbrev slotPairAt (p : BitVec 64) (kv : BitVec 64 × BitVec 64) : SepProp :=
  (p ↦₆₄ kv.1) ∗ ((p + 8#64) ↦₆₄ kv.2)

/-- Downward 16-byte slot address `top - ((i + 1) * 16)`. -/
@[expose] def slotAddr (top : BitVec 64) (i : Nat) : BitVec 64 :=
  top - BitVec.ofNat 64 ((i + 1) * 16)

/-- Downward-growing 16-byte slot array starting immediately below `top`
    (`slots[i]` lives at `top - ((i + 1) * 16)`). -/
def slotsDownFrom (top : BitVec 64) : List (BitVec 64 × BitVec 64) → SepProp
  | [] => emp
  | kv :: rest => slotPairAt (top - 16#64) kv ∗ slotsDownFrom (top - 16#64) rest

@[simp]
theorem slotsDownFrom_nil (top : BitVec 64) : slotsDownFrom top [] = emp := by rfl

@[simp]
theorem slotsDownFrom_cons (top : BitVec 64) (kv : BitVec 64 × BitVec 64)
    (rest : List (BitVec 64 × BitVec 64)) :
    slotsDownFrom top (kv :: rest) =
      slotPairAt (top - 16#64) kv ∗ slotsDownFrom (top - 16#64) rest := by rfl

theorem slotsDownFrom_append (top : BitVec 64)
    (xs ys : List (BitVec 64 × BitVec 64)) :
    slotsDownFrom top (xs ++ ys) =
      slotsDownFrom top xs ∗
        slotsDownFrom (top - BitVec.ofNat 64 (xs.length * 16)) ys := by
  induction xs generalizing top with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, slotsDownFrom_cons, List.length_cons, ih, sepConj_assoc]
    have htop : top - 16#64 - BitVec.ofNat 64 (xs.length * 16) =
        top - BitVec.ofNat 64 ((xs.length + 1) * 16) := by
      have : (xs.length + 1) * 16 = 16 + xs.length * 16 := by omega
      rw [this, BitVec.ofNat_add]
      bv_lin
    rw [htop]

theorem slotsDownFrom_focus (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    (i : Nat) (hi : i < slots.length) :
    slotsDownFrom top slots =
      slotPairAt (slotAddr top i) (slots.getD i default) ∗
        (slotsDownFrom top (slots.take i) ∗
         slotsDownFrom (slotAddr top i) (slots.drop (i + 1))) := by
  conv => lhs; rw [← List.take_append_drop i slots, List.drop_eq_getD_cons slots i default hi]
  rw [slotsDownFrom_append, slotsDownFrom_cons, List.length_take_of_le (Nat.le_of_lt hi)]
  have haddr : top - BitVec.ofNat 64 (i * 16) - 16#64 = slotAddr top i := by
    unfold slotAddr
    have : (i + 1) * 16 = i * 16 + 16 := by omega
    rw [this, BitVec.ofNat_add]
    bv_lin
  rw [haddr, ← sepConj_assoc,
      sepConj_comm (slotsDownFrom top (slots.take i)) (slotPairAt (slotAddr top i) _),
      sepConj_assoc]

theorem slotsDownFrom_update (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    (i : Nat) (kv' : BitVec 64 × BitVec 64) (hi : i < slots.length) :
    slotPairAt (slotAddr top i) kv' ∗
      (slotsDownFrom top (slots.take i) ∗
       slotsDownFrom (slotAddr top i) (slots.drop (i + 1))) =
      slotsDownFrom top (slots.set i kv') := by
  have hi' : i < (slots.set i kv').length := by simpa using hi
  rw [slotsDownFrom_focus top (slots.set i kv') i hi']
  have hget : (slots.set i kv').getD i default = kv' := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  have htake : (slots.set i kv').take i = slots.take i := List.take_set_of_le (Nat.le_refl i)
  have hdrop : (slots.set i kv').drop (i + 1) = slots.drop (i + 1) := List.drop_set_of_lt (by omega)
  simp only [hget, htake, hdrop]

@[sep_lens]
/-- Symbolic-index downward 16-byte bucket `SepLens` at `top - ((i + 1) * 16)`. -/
theorem slotsDownFrom_lens (top : BitVec 64) (i : Nat) :
    SepLens
      (Guarded (fun slots => i < slots.length) (slotsDownFrom top))
      (slotPairAt (top - BitVec.ofNat 64 ((i + 1) * 16)))
      (fun slots => ⌜i < slots.length⌝ ∗
        (slotsDownFrom top (slots.take i) ∗
         slotsDownFrom (slotAddr top i) (slots.drop (i + 1))))
      (fun slots => slots.getD i default)
      (fun slots kv' => slots.set i kv') where
  open_entails slots := Entails.pure_left fun hi => by
    rw [slotsDownFrom_focus top slots i hi]
    exact sepConj_mono_right (Entails.pure_right hi (Entails.refl _))
  close_entails slots kv' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun hi => ?_
    change (slotPairAt (slotAddr top i) kv' ∗ _) ⊢ _
    rw [slotsDownFrom_update top slots i kv' hi]
    exact Entails.pure_right (by dsimp only; rw [List.length_set]; exact hi) (Entails.refl _)

theorem slotAddr_eq_neg_shift (top : BitVec 64) (idx : Nat) (h16 : idx * 16 < 2 ^ 64) :
    (top - (BitVec.ofNat 64 idx <<< 4)) - 16#64 = slotAddr top idx := by
  have hidx : idx < 2 ^ 64 := by omega
  have hsh : BitVec.ofNat 64 idx <<< 4 = BitVec.ofNat 64 (idx * 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx,
        Nat.shiftLeft_eq, show 2 ^ 4 = 16 by rfl, Nat.mod_eq_of_lt h16,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h16]
  unfold slotAddr
  have hmul : (idx + 1) * 16 = idx * 16 + 16 := by omega
  rw [hsh, hmul, BitVec.ofNat_add]
  bv_lin

@[sep_lens]
/-- Hardware negative-offset downward bucket `SepLens` matching ARM64
    `sub xSlot, xTop, xIdx, lsl #4 ; stp xFirst, xSecond, [xSlot, #-16]`. -/
theorem slotsDownFrom_neg_lens (top : BitVec 64) (idx : Nat) :
    SepLens
      (Guarded (fun slots => idx < slots.length ∧ idx * 16 < 2 ^ 64) (slotsDownFrom top))
      (slotPairAt ((top - (BitVec.ofNat 64 idx <<< 4)) - 16#64))
      (fun slots => ⌜idx < slots.length ∧ idx * 16 < 2 ^ 64⌝ ∗
        (slotsDownFrom top (slots.take idx) ∗
         slotsDownFrom (slotAddr top idx) (slots.drop (idx + 1))))
      (fun slots => slots.getD idx default)
      (fun slots kv' => slots.set idx kv') where
  open_entails slots := Entails.pure_left fun ⟨hi, h16⟩ => by
    rw [slotAddr_eq_neg_shift top idx h16, slotsDownFrom_focus top slots idx hi]
    exact sepConj_mono_right (Entails.pure_right ⟨hi, h16⟩ (Entails.refl _))
  close_entails slots kv' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun ⟨hi, h16⟩ => ?_
    rw [slotAddr_eq_neg_shift top idx h16, slotsDownFrom_update top slots idx kv' hi]
    exact Entails.pure_right ⟨by rw [List.length_set]; exact hi, h16⟩ (Entails.refl _)

/-! ## 2(c). Width-Polymorphic `WordCodec`, `SliceWindowLens`, and `OwnByteMap` (`ownCells`) Lens -/

/-- Width-polymorphic little-endian memory cell codec unifying `↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`,
    `↦₁₂₈`, and 16-byte `(BitVec 64 × BitVec 64)` pairs across `↦ₛ` slices and `ownCells` maps. -/
class WordCodec (α : Type) where
  width             : Nat
  pointsTo          : BitVec 64 → α → SepProp
  decode            : List (BitVec 8) → α
  encode            : α → List (BitVec 8)
  encode_len        : ∀ v, (encode v).length = width
  decode_encode     : ∀ v, decode (encode v) = v
  encode_decode     : ∀ bs, bs.length = width → encode (decode bs) = bs
  pointsTo_eq_bytes : ∀ a v, pointsTo a v = (a ↦ₛ encode v)

theorem unpackLE_setWidth_readLE (bs : List (BitVec 8)) (n : Nat)
    (hbs : bs.length = n) (hn : n ≤ 8) :
    ProofLib.ByteSlice.unpackLE n ((ProofLib.ByteSlice.readLE bs 0 n).setWidth (8 * n)) = bs := by
  have h1 : ProofLib.ByteSlice.unpackLE n ((ProofLib.ByteSlice.readLE bs 0 n).setWidth (8 * n)) =
      ProofLib.ByteSlice.unpackLE n (ProofLib.ByteSlice.readLE bs 0 n) := by
    apply List.ext_getElem (by simp)
    intro j hj1 _
    have hj : j < n := by simpa using hj1
    ext k hk
    simp only [ProofLib.ByteSlice.unpackLE, List.getElem_map, List.getElem_range,
      BitVec.getElem_extractLsb']
    have hlt : 8 * j + k < 8 * n := by omega
    simp [hlt]
  rw [h1, ProofLib.ByteSlice.unpackLE_readLE bs 0 n (by omega) hn]
  unfold ProofLib.ByteSlice.slice
  rw [List.drop_zero, List.take_of_length_le (by omega)]

@[reducible]
instance instWordCodec8 : WordCodec (BitVec 8) where
  width := 1
  pointsTo a v := a ↦₈ v
  decode bs := bs.getD 0 0#8
  encode v := [v]
  encode_len _ := rfl
  decode_encode _ := rfl
  encode_decode bs hbs := by
    match bs, hbs with
    | [b], _ => rfl
  pointsTo_eq_bytes a v := (pointsToBytes_singleton a v).symm

@[reducible]
instance instWordCodec16 : WordCodec (BitVec 16) where
  width := 2
  pointsTo a v := a ↦₁₆ v
  decode bs := (ProofLib.ByteSlice.readLE bs 0 2).setWidth 16
  encode v := ProofLib.ByteSlice.unpackLE 2 v
  encode_len v := ProofLib.ByteSlice.unpackLE_length 2 v
  decode_encode v := ProofLib.ByteSlice.setWidth_readLE_unpackLE 2 v (by decide) (by decide)
  encode_decode bs hbs := unpackLE_setWidth_readLE bs 2 hbs (by decide)
  pointsTo_eq_bytes a v := by
    have hlen : (ProofLib.ByteSlice.unpackLE 2 v).length = 2 := ProofLib.ByteSlice.unpackLE_length 2 v
    have hsl : ProofLib.ByteSlice.slice (ProofLib.ByteSlice.unpackLE 2 v) 0 2 =
        ProofLib.ByteSlice.unpackLE 2 v := by
      unfold ProofLib.ByteSlice.slice
      rw [List.drop_zero, List.take_of_length_le (by omega)]
    rw [← hsl, pointsToBytes_slice_eq_pointsTo16 a (ProofLib.ByteSlice.unpackLE 2 v) 0 (by omega),
        ProofLib.ByteSlice.setWidth_readLE_unpackLE 2 v (by decide) (by decide)]

@[reducible]
instance instWordCodec32 : WordCodec (BitVec 32) where
  width := 4
  pointsTo a v := a ↦₃₂ v
  decode bs := (ProofLib.ByteSlice.readLE bs 0 4).setWidth 32
  encode v := ProofLib.ByteSlice.unpackLE 4 v
  encode_len v := ProofLib.ByteSlice.unpackLE_length 4 v
  decode_encode v := ProofLib.ByteSlice.setWidth_readLE_unpackLE 4 v (by decide) (by decide)
  encode_decode bs hbs := unpackLE_setWidth_readLE bs 4 hbs (by decide)
  pointsTo_eq_bytes a v := by
    have hlen : (ProofLib.ByteSlice.unpackLE 4 v).length = 4 := ProofLib.ByteSlice.unpackLE_length 4 v
    have hsl : ProofLib.ByteSlice.slice (ProofLib.ByteSlice.unpackLE 4 v) 0 4 =
        ProofLib.ByteSlice.unpackLE 4 v := by
      unfold ProofLib.ByteSlice.slice
      rw [List.drop_zero, List.take_of_length_le (by omega)]
    rw [← hsl, pointsToBytes_slice_eq_pointsTo32 a (ProofLib.ByteSlice.unpackLE 4 v) 0 (by omega),
        ProofLib.ByteSlice.setWidth_readLE_unpackLE 4 v (by decide) (by decide)]

@[reducible]
instance instWordCodec64 : WordCodec (BitVec 64) where
  width := 8
  pointsTo a v := a ↦₆₄ v
  decode bs := ProofLib.ByteSlice.readLE bs 0 8
  encode v := ProofLib.ByteSlice.unpackLE 8 v
  encode_len v := ProofLib.ByteSlice.unpackLE_length 8 v
  decode_encode v := ProofLib.ByteSlice.readLE_unpackLE_64 8 v
  encode_decode bs hbs := by
    rw [ProofLib.ByteSlice.unpackLE_readLE bs 0 8 (by omega) (by decide)]
    unfold ProofLib.ByteSlice.slice
    rw [List.drop_zero, List.take_of_length_le (by omega)]
  pointsTo_eq_bytes a v := by
    have hlen : (ProofLib.ByteSlice.unpackLE 8 v).length = 8 := ProofLib.ByteSlice.unpackLE_length 8 v
    have hsl : ProofLib.ByteSlice.slice (ProofLib.ByteSlice.unpackLE 8 v) 0 8 =
        ProofLib.ByteSlice.unpackLE 8 v := by
      unfold ProofLib.ByteSlice.slice
      rw [List.drop_zero, List.take_of_length_le (by omega)]
    rw [← hsl, pointsToBytes_slice_eq_pointsTo64 a (ProofLib.ByteSlice.unpackLE 8 v) 0 (by omega),
        ProofLib.ByteSlice.readLE_unpackLE_64 8 v]

@[reducible]
instance instWordCodecPair64 : WordCodec (BitVec 64 × BitVec 64) where
  width := 16
  pointsTo a kv := slotPairAt a kv
  decode bs := (ProofLib.ByteSlice.readLE (bs.take 8) 0 8, ProofLib.ByteSlice.readLE (bs.drop 8) 0 8)
  encode kv := ProofLib.ByteSlice.unpackLE 8 kv.1 ++ ProofLib.ByteSlice.unpackLE 8 kv.2
  encode_len kv := by simp [ProofLib.ByteSlice.unpackLE_length]
  decode_encode kv := by
    have h1 : (ProofLib.ByteSlice.unpackLE 8 kv.1 ++ ProofLib.ByteSlice.unpackLE 8 kv.2).take 8 =
        ProofLib.ByteSlice.unpackLE 8 kv.1 := by
      rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    have h2 : (ProofLib.ByteSlice.unpackLE 8 kv.1 ++ ProofLib.ByteSlice.unpackLE 8 kv.2).drop 8 =
        ProofLib.ByteSlice.unpackLE 8 kv.2 := by
      rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append]
    rw [h1, h2, ProofLib.ByteSlice.readLE_unpackLE_64 8 kv.1,
        ProofLib.ByteSlice.readLE_unpackLE_64 8 kv.2]
  encode_decode bs hbs := by
    have ht : (bs.take 8).length = 8 := by simp [hbs]
    have hd : (bs.drop 8).length = 8 := by simp [hbs]
    have e1 := (inferInstance : WordCodec (BitVec 64)).encode_decode (bs.take 8) ht
    have e2 := (inferInstance : WordCodec (BitVec 64)).encode_decode (bs.drop 8) hd
    dsimp [WordCodec.encode, WordCodec.decode] at e1 e2
    rw [e1, e2, List.take_append_drop]
  pointsTo_eq_bytes a kv := by
    unfold slotPairAt
    have p1 := (inferInstance : WordCodec (BitVec 64)).pointsTo_eq_bytes a kv.1
    have p2 := (inferInstance : WordCodec (BitVec 64)).pointsTo_eq_bytes (a + 8#64) kv.2
    dsimp [WordCodec.pointsTo, WordCodec.encode] at p1 p2
    rw [pointsToBytes_append, ProofLib.ByteSlice.unpackLE_length, p1, p2]

@[reducible]
instance instWordCodec128 : WordCodec (BitVec 128) where
  width := 16
  pointsTo a v := a ↦₁₂₈ v
  decode bs :=
    ProofLib.ByteSlice.readLE (bs.drop 8) 0 8 ++ ProofLib.ByteSlice.readLE (bs.take 8) 0 8
  encode v :=
    ProofLib.ByteSlice.unpackLE 8 (v.extractLsb' 0 64) ++
      ProofLib.ByteSlice.unpackLE 8 (v.extractLsb' 64 64)
  encode_len v := by simp [ProofLib.ByteSlice.unpackLE_length]
  decode_encode v := by
    let lo := v.extractLsb' 0 64
    let hi := v.extractLsb' 64 64
    have h1 : (ProofLib.ByteSlice.unpackLE 8 lo ++ ProofLib.ByteSlice.unpackLE 8 hi).take 8 =
        ProofLib.ByteSlice.unpackLE 8 lo := by
      rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    have h2 : (ProofLib.ByteSlice.unpackLE 8 lo ++ ProofLib.ByteSlice.unpackLE 8 hi).drop 8 =
        ProofLib.ByteSlice.unpackLE 8 hi := by
      rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append]
    rw [h1, h2, ProofLib.ByteSlice.readLE_unpackLE_64 8 lo,
        ProofLib.ByteSlice.readLE_unpackLE_64 8 hi]
    dsimp only [lo, hi]
    bv_bits
  encode_decode bs hbs := by
    let lo := ProofLib.ByteSlice.readLE (bs.take 8) 0 8
    let hi := ProofLib.ByteSlice.readLE (bs.drop 8) 0 8
    have hlo : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
    have hhi : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
    rw [hlo, hhi]
    exact (inferInstance : WordCodec (BitVec 64 × BitVec 64)).encode_decode bs hbs
  pointsTo_eq_bytes a v := by
    rw [pointsTo128_split64]
    exact (inferInstance : WordCodec (BitVec 64 × BitVec 64)).pointsTo_eq_bytes a
      (v.extractLsb' 0 64, v.extractLsb' 64 64)

/-- Read-only round-trip identity for `sliceWindow_lens`. -/
theorem sliceWindow_put_get {α : Type} [c : WordCodec α] (bs : List (BitVec 8)) (off : Nat)
    (h : off + c.width ≤ bs.length) :
    ProofLib.ByteSlice.write bs off
      (c.encode (c.decode (ProofLib.ByteSlice.slice bs off c.width))) = bs := by
  rw [c.encode_decode _ (ProofLib.ByteSlice.slice_length bs off c.width h),
      ProofLib.ByteSlice.write_slice_self bs off c.width h]

@[sep_lens]
/-- Width-polymorphic symbolic-offset byte-slice window lens (`SliceWindowLens`): focuses
    `c.pointsTo (base + BitVec.ofNat 64 off)` (`↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦₁₂₈`, or 16B `slotPairAt`)
    out of `base ↦ₛ bs` and updates `bs` via `ByteSlice.write`. -/
theorem sliceWindow_lens {α : Type} [c : WordCodec α] (base : BitVec 64) (off : Nat) :
    SepLens
      (Guarded (fun bs : List (BitVec 8) => off + c.width ≤ bs.length) (pointsToBytes base))
      (c.pointsTo (base + BitVec.ofNat 64 off))
      (fun bs => ⌜off + c.width ≤ bs.length⌝ ∗
        ((base ↦ₛ bs.take off) ∗
         ((base + BitVec.ofNat 64 (off + c.width)) ↦ₛ bs.drop (off + c.width))))
      (fun bs => c.decode (ProofLib.ByteSlice.slice bs off c.width))
      (fun bs v' => ProofLib.ByteSlice.write bs off (c.encode v')) where
  open_entails bs := Entails.pure_left fun h => by
    rw [pointsToBytes_focus base bs off c.width h,
        c.pointsTo_eq_bytes (base + BitVec.ofNat 64 off) _,
        c.encode_decode (ProofLib.ByteSlice.slice bs off c.width)
          (ProofLib.ByteSlice.slice_length bs off c.width h)]
    exact sepConj_mono_right (Entails.pure_right h (Entails.refl _))
  close_entails bs v' := by
    rw [sepConj_pure_left_comm]
    refine Entails.pure_left fun h => ?_
    rw [c.pointsTo_eq_bytes (base + BitVec.ofNat 64 off) v',
        pointsToBytes_write_len base bs (c.encode v') off c.width (c.encode_len v') h]
    refine Entails.pure_right ?_ (Entails.refl _)
    dsimp only
    rw [ProofLib.ByteSlice.write_length bs (c.encode v') off (by rw [c.encode_len]; exact h)]
    exact h

@[sep_lens]
/-- Offset-zero specialization of `sliceWindow_lens` focusing `c.pointsTo base` directly. -/
theorem sliceWindow_zero_lens {α : Type} [c : WordCodec α] (base : BitVec 64) :
    SepLens
      (Guarded (fun bs : List (BitVec 8) => c.width ≤ bs.length) (pointsToBytes base))
      (c.pointsTo base)
      (fun bs => ⌜c.width ≤ bs.length⌝ ∗
        ((base ↦ₛ bs.take 0) ∗
         ((base + BitVec.ofNat 64 c.width) ↦ₛ bs.drop c.width)))
      (fun bs => c.decode (ProofLib.ByteSlice.slice bs 0 c.width))
      (fun bs v' => ProofLib.ByteSlice.write bs 0 (c.encode v')) where
  open_entails bs := Entails.pure_left fun h => by
    have h0 : 0 + c.width ≤ bs.length := by omega
    have hop := (sliceWindow_lens (α := α) base 0).open_entails bs
    have hop' := Entails.trans (Entails.pure_right h0 (Entails.refl _)) hop
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.zero_add] using hop'
  close_entails bs v' := by
    have hcl := (sliceWindow_lens (α := α) base 0).close_entails bs v'
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.zero_add] using hcl

/-- Pointwise writable byte-map predicate backed by `ProofLib.ownCells`. -/
def OwnByteMap (dom : BitVec 64 → Bool) (byteVal : BitVec 64 → BitVec 8) : SepProp :=
  ownCells (fun a => if dom a then some (.rw (byteVal a)) else none)

theorem OwnByteMap_def (dom : BitVec 64 → Bool) (byteVal : BitVec 64 → BitVec 8) :
    OwnByteMap dom byteVal =
      ownCells (fun a => if dom a then some (.rw (byteVal a)) else none) := by
  rfl

/-- Boolean half-open window test `x ∈ [addr, addr + n)`. -/
def inWindowBool (addr : BitVec 64) (n : Nat) (x : BitVec 64) : Bool :=
  decide (addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + n)

/-- Read `n` contiguous bytes from `byteVal` starting at `addr`. -/
def readMapBytes (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => byteVal addr :: readMapBytes byteVal (addr + 1#64) n

@[simp]
theorem readMapBytes_zero (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64) :
    readMapBytes byteVal addr 0 = [] := by rfl

@[simp]
theorem readMapBytes_succ (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64) (n : Nat) :
    readMapBytes byteVal addr (n + 1) =
      byteVal addr :: readMapBytes byteVal (addr + 1#64) n := by rfl

/-- Functional update writing `bs` into `byteVal` at `[addr, addr + bs.length)`. -/
def writeMapBytes (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (bs : List (BitVec 8)) (x : BitVec 64) : BitVec 8 :=
  if decide (addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + bs.length) then
    bs.getD (x.toNat - addr.toNat) 0#8
  else
    byteVal x

@[simp]
theorem readMapBytes_length (byteVal : BitVec 64 → BitVec 8) :
    ∀ (n : Nat) (addr : BitVec 64), (readMapBytes byteVal addr n).length = n
  | 0, _ => rfl
  | n + 1, addr => by simp [readMapBytes, readMapBytes_length byteVal n (addr + 1#64)]

private theorem toNat_add_one {addr : BitVec 64} (h : addr.toNat + 1 < 2 ^ 64) :
    (addr + 1#64).toNat = addr.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem readMapBytes_getD (byteVal : BitVec 64 → BitVec 8)
    (n : Nat) (addr : BitVec 64) (i : Nat)
    (hb : addr.toNat + n ≤ 2 ^ 64) (hi : i < n) :
    (readMapBytes byteVal addr n).getD i 0#8 = byteVal (addr + BitVec.ofNat 64 i) := by
  induction n generalizing addr i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    cases i with
    | zero => simp [readMapBytes]
    | succ i =>
      have hlt : i < n := Nat.lt_of_succ_lt_succ hi
      have h1 : (addr + 1#64).toNat = addr.toNat + 1 := toNat_add_one (by omega)
      simp only [readMapBytes, List.getD_cons_succ]
      rw [ih (addr + 1#64) i (by omega) hlt]
      have hadd : addr + 1#64 + BitVec.ofNat 64 i = addr + BitVec.ofNat 64 (i + 1) := by
        have : (1 : Nat) + i = i + 1 := by omega
        rw [BitVec.add_assoc]
        change addr + (BitVec.ofNat 64 1 + BitVec.ofNat 64 i) = _
        rw [← BitVec.ofNat_add, this]
      rw [hadd]

theorem readMapBytes_eq_of_forall (bv : BitVec 64 → BitVec 8)
    (bs : List (BitVec 8)) (addr : BitVec 64)
    (hb : addr.toNat + bs.length ≤ 2 ^ 64)
    (h : ∀ i, (hi : i < bs.length) → bv (addr + BitVec.ofNat 64 i) = bs[i]'hi) :
    readMapBytes bv addr bs.length = bs := by
  induction bs generalizing addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hb
    have h0 : bv addr = b := by simpa using h 0 (Nat.zero_lt_succ _)
    cases rest with
    | nil => simp [readMapBytes, h0]
    | cons b' rest' =>
      simp only [List.length_cons] at hb
      have h1 : (addr + 1#64).toNat = addr.toNat + 1 := toNat_add_one (by omega)
      rw [List.length_cons, readMapBytes, h0]
      congr 1
      refine ih (addr + 1#64) (by simp only [List.length_cons]; omega) ?_
      intro j hj
      have hadd : addr + 1#64 + BitVec.ofNat 64 j = addr + BitVec.ofNat 64 (j + 1) := by
        have : (1 : Nat) + j = j + 1 := by omega
        rw [BitVec.add_assoc]
        change addr + (BitVec.ofNat 64 1 + BitVec.ofNat 64 j) = _
        rw [← BitVec.ofNat_add, this]
      rw [hadd]
      exact h (j + 1) (Nat.succ_lt_succ hj)

theorem readMapBytes_writeMapBytes (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (bs : List (BitVec 8)) (hbound : addr.toNat + bs.length ≤ 2 ^ 64) :
    readMapBytes (writeMapBytes byteVal addr bs) addr bs.length = bs := by
  refine readMapBytes_eq_of_forall (writeMapBytes byteVal addr bs) bs addr hbound ?_
  intro i hi
  have htn : (addr + BitVec.ofNat 64 i).toNat = addr.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hcond : decide (addr.toNat ≤ addr.toNat + i ∧ addr.toNat + i < addr.toNat + bs.length) =
      true := by
    rw [decide_eq_true_eq]
    omega
  unfold writeMapBytes
  rw [htn]
  simp only [hcond, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem writeMapBytes_readMapBytes (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (n : Nat) (hbound : addr.toNat + n ≤ 2 ^ 64) :
    writeMapBytes byteVal addr (readMapBytes byteVal addr n) = byteVal := by
  funext x
  unfold writeMapBytes
  rw [readMapBytes_length]
  split <;> rename_i hx
  · simp only [decide_eq_true_eq] at hx
    rw [readMapBytes_getD byteVal n addr (x.toNat - addr.toNat) hbound (by omega)]
    have hxeq : addr + BitVec.ofNat 64 (x.toNat - addr.toNat) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hxeq]
  · rfl

theorem writeMapBytes_writeMapBytes (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (bs₁ bs₂ : List (BitVec 8)) (hlen : bs₁.length = bs₂.length) :
    writeMapBytes (writeMapBytes byteVal addr bs₁) addr bs₂ = writeMapBytes byteVal addr bs₂ := by
  funext x
  unfold writeMapBytes
  rw [hlen]
  split <;> rfl

/-- Core inductive cut splitting `(addr ↦ₛ readMapBytes byteVal addr n)` out of `OwnByteMap`. -/
theorem OwnByteMap_split_window
    (n : Nat) (dom : BitVec 64 → Bool) (byteVal : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (hbound : addr.toNat + n ≤ 2 ^ 64)
    (hdom : ∀ i, i < n → dom (addr + BitVec.ofNat 64 i) = true) :
    OwnByteMap dom byteVal =
      (addr ↦ₛ readMapBytes byteVal addr n) ∗
        OwnByteMap (fun x => dom x && !inWindowBool addr n x) byteVal := by
  induction n generalizing dom addr with
  | zero =>
    simp only [readMapBytes, pointsToBytes_nil, emp_sepConj]
    congr 1
    funext x
    have hfalse : inWindowBool addr 0 x = false := by
      unfold inWindowBool
      simp only [Nat.add_zero, decide_eq_false_iff_not]
      omega
    simp [hfalse]
  | succ n ih =>
    have hd0 : dom addr = true := by simpa using hdom 0 (Nat.zero_lt_succ n)
    have hcut : OwnByteMap dom byteVal =
        (addr ↦₈ byteVal addr) ∗ OwnByteMap (fun x => dom x && decide (x ≠ addr)) byteVal := by
      unfold OwnByteMap
      rw [ownCells_cut_rw _ addr (byteVal addr) (by simp [hd0])]
      congr 2
      funext x
      by_cases hx : x = addr <;> simp [hx]
    cases n with
    | zero =>
      rw [hcut]
      simp only [readMapBytes, pointsToBytes_singleton]
      congr 1
      unfold OwnByteMap
      congr 1
      funext x
      have hmask0 : (dom x && decide (x ≠ addr)) = (dom x && !inWindowBool addr 1 x) := by
        cases dom x <;> simp only [Bool.false_and, Bool.true_and]
        unfold inWindowBool
        by_cases hx : x = addr
        · subst hx
          have hw : x.toNat ≤ x.toNat ∧ x.toNat < x.toNat + 1 := by omega
          simp [hw]
        · have hxtn : x.toNat ≠ addr.toNat := fun he => hx (BitVec.eq_of_toNat_eq he)
          have hw : ¬(addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + 1) := by omega
          simp [hx, hw]
      simp only [hmask0]
    | succ m =>
      have h1 : (addr + 1#64).toNat = addr.toNat + 1 := toNat_add_one (by omega)
      have hdom' : ∀ j, j < m + 1 →
          (dom ((addr + 1#64) + BitVec.ofNat 64 j) &&
            decide ((addr + 1#64) + BitVec.ofNat 64 j ≠ addr)) = true := by
        intro j hj
        have hadd : (addr + 1#64) + BitVec.ofNat 64 j = addr + BitVec.ofNat 64 (j + 1) := by
          have : (1 : Nat) + j = j + 1 := by omega
          rw [BitVec.add_assoc]
          change addr + (BitVec.ofNat 64 1 + BitVec.ofNat 64 j) = _
          rw [← BitVec.ofNat_add, this]
        rw [hadd]
        have hne : addr + BitVec.ofNat 64 (j + 1) ≠ addr := by
          intro heq
          have htn := congrArg BitVec.toNat heq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat] at htn
          omega
        simp [hdom (j + 1) (Nat.succ_lt_succ hj), hne]
      rw [hcut, ih (fun x => dom x && decide (x ≠ addr)) (addr + 1#64) (by omega) hdom']
      conv =>
        rhs
        rw [readMapBytes, pointsToBytes_cons]
      rw [sepConj_assoc]
      congr 1
      congr 1
      unfold OwnByteMap
      congr 1
      funext x
      have hmask : ((dom x && decide (x ≠ addr)) && !inWindowBool (addr + 1#64) (m + 1) x) =
          (dom x && !inWindowBool addr (m + 1 + 1) x) := by
        cases hdx : dom x <;> simp only [Bool.false_and, Bool.true_and]
        unfold inWindowBool
        rw [h1]
        by_cases hx : x = addr
        · subst hx
          have hw : x.toNat ≤ x.toNat ∧ x.toNat < x.toNat + (m + 1 + 1) := by omega
          have hw0 : ¬(x.toNat + 1 ≤ x.toNat ∧ x.toNat < x.toNat + 1 + (m + 1)) := by omega
          simp [hw, hw0]
        · have hxtn : x.toNat ≠ addr.toNat := fun he => hx (BitVec.eq_of_toNat_eq he)
          have hdec : decide (x ≠ addr) = true := decide_eq_true hx
          rw [hdec, Bool.true_and]
          by_cases hw : addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + (m + 1 + 1)
          · have hw' : addr.toNat + 1 ≤ x.toNat ∧ x.toNat < addr.toNat + 1 + (m + 1) := by omega
            simp [hw, hw']
          · have hw' : ¬(addr.toNat + 1 ≤ x.toNat ∧ x.toNat < addr.toNat + 1 + (m + 1)) := by omega
            simp [hw, hw']
      dsimp only
      simp only [hmask]

/-- Inverse absorption reassembling `(addr ↦ₛ bs)` back into `OwnByteMap dom (writeMapBytes ...)`. -/
theorem OwnByteMap_absorb_window (dom : BitVec 64 → Bool) (byteVal : BitVec 64 → BitVec 8)
    (addr : BitVec 64) (bs : List (BitVec 8))
    (hbound : addr.toNat + bs.length ≤ 2 ^ 64)
    (hdom : ∀ i, i < bs.length → dom (addr + BitVec.ofNat 64 i) = true) :
    (addr ↦ₛ bs) ∗ OwnByteMap (fun x => dom x && !inWindowBool addr bs.length x) byteVal =
      OwnByteMap dom (writeMapBytes byteVal addr bs) := by
  rw [OwnByteMap_split_window bs.length dom (writeMapBytes byteVal addr bs) addr hbound hdom,
      readMapBytes_writeMapBytes byteVal addr bs hbound]
  congr 1
  unfold OwnByteMap
  congr 1
  funext x
  dsimp only
  by_cases hwin : (dom x && !inWindowBool addr bs.length x) = true
  · simp only [hwin, ↓reduceIte]
    have hnotin : ¬(addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + bs.length) := by
      unfold inWindowBool at hwin
      rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hwin
      exact hwin.2
    unfold writeMapBytes
    simp [hnotin]
  · have hwin' : (dom x && !inWindowBool addr bs.length x) = false :=
      Bool.eq_false_iff.mpr hwin
    simp only [hwin', Bool.false_eq_true, ↓reduceIte]

@[sep_lens]
/-- Width-polymorphic `LawfulSepLens` over `OwnByteMap` (`ownCells`) handling `u8`, `u16`, `u32`,
    `u64`, `u128`, and 16-byte `(BitVec 64 × BitVec 64)` pairs uniformly. -/
theorem ownByteMap_lawful {α : Type} [c : WordCodec α]
    (dom : BitVec 64 → Bool) (addr : BitVec 64)
    (hbound : addr.toNat + c.width ≤ 2 ^ 64)
    (hdom : ∀ i, i < c.width → dom (addr + BitVec.ofNat 64 i) = true) :
    LawfulSepLens (OwnByteMap dom) (c.pointsTo addr)
      (fun byteVal => OwnByteMap (fun x => dom x && !inWindowBool addr c.width x) byteVal)
      (fun byteVal => c.decode (readMapBytes byteVal addr c.width))
      (fun byteVal v' => writeMapBytes byteVal addr (c.encode v')) where
  open_entails byteVal := by
    refine Entails.of_eq ?_
    rw [OwnByteMap_split_window c.width dom byteVal addr hbound hdom,
        c.pointsTo_eq_bytes addr _,
        c.encode_decode _ (readMapBytes_length byteVal c.width addr)]
  close_entails byteVal v' := by
    refine Entails.of_eq ?_
    have hlen : (c.encode v').length = c.width := c.encode_len v'
    rw [c.pointsTo_eq_bytes addr v', ← hlen]
    exact OwnByteMap_absorb_window dom byteVal addr (c.encode v')
      (by rw [hlen]; exact hbound) (by rw [hlen]; exact hdom)
  put_get byteVal := by
    rw [c.encode_decode _ (readMapBytes_length byteVal c.width addr)]
    exact writeMapBytes_readMapBytes byteVal addr c.width hbound
  get_put byteVal v' := by
    have hlen : (c.encode v').length = c.width := c.encode_len v'
    rw [← hlen, readMapBytes_writeMapBytes byteVal addr (c.encode v') (by rw [hlen]; exact hbound),
        c.decode_encode v']
  put_put byteVal v₁ v₂ :=
    writeMapBytes_writeMapBytes byteVal addr (c.encode v₁) (c.encode v₂)
      (by rw [c.encode_len, c.encode_len])

/-- Plain `SepLens` projection of `ownByteMap_lawful`. -/
theorem ownByteMap_lens {α : Type} [c : WordCodec α]
    (dom : BitVec 64 → Bool) (addr : BitVec 64)
    (hbound : addr.toNat + c.width ≤ 2 ^ 64)
    (hdom : ∀ i, i < c.width → dom (addr + BitVec.ofNat 64 i) = true) :
    SepLens (OwnByteMap dom) (c.pointsTo addr)
      (fun byteVal => OwnByteMap (fun x => dom x && !inWindowBool addr c.width x) byteVal)
      (fun byteVal => c.decode (readMapBytes byteVal addr c.width))
      (fun byteVal v' => writeMapBytes byteVal addr (c.encode v')) :=
  (ownByteMap_lawful dom addr hbound hdom).toSepLens

end

/-! ## 3. Demand-Driven `lens_open` / `lens_switch` / `lens_close`, `wp_lens_step`, & `wp_lens_auto` -/

public meta section

open Lean Meta Elab Tactic

/-- Requested leaf memory shape from an instruction or explicit `width` hint. -/
inductive LensAccessShape where
  | anyWidth (w : Nat)
  | pair64
  | simd128
  deriving DecidableEq, Repr, Inhabited, BEq

namespace LensAccessShape

def byteWidth : LensAccessShape → Nat
  | .anyWidth w => w
  | .pair64 | .simd128 => 16

end LensAccessShape

/-- Decode a quoted `Lean.Name` expression from a `SepLensRule` instance type. -/
partial def evalQuotedName? (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e
  if e.isConstOf ``Name.anonymous then
    return some .anonymous
  else if e.isAppOfArity ``Name.str 2 then
    let some p ← evalQuotedName? (e.getArg! 0) | return none
    match (← whnf (e.getArg! 1)) with
    | .lit (.strVal s) => return some (.str p s)
    | _ => return none
  else if e.isAppOfArity ``Name.num 2 then
    let some p ← evalQuotedName? (e.getArg! 0) | return none
    match (← whnf (e.getArg! 1)) with
    | .lit (.natVal n) => return some (.num p n)
    | _ => return none
  else
    return none

/-- Query all `@[sep_lens]` rule declarations registered in the global instance index
    (including imported `.olean` modules and declarations in the current module). -/
def getSepLensRules : MetaM (Array Name) := do
  let idx ← Meta.getGlobalInstancesIndex
  let pat := mkApp (mkConst ``SepLensRule) (← mkFreshExprMVar (mkConst ``Name))
  let entries ← idx.getUnify pat
  let env ← getEnv
  let mut out : Array Name := #[]
  for ie in entries do
    if let some instName := ie.globalName? then
      if let some ci := env.find? instName then
        if ci.type.isAppOfArity ``SepLensRule 1 then
          if let some nm ← evalQuotedName? (ci.type.getArg! 0) then
            if !out.contains nm then
              out := out.push nm
  return out

/-- Fast 64-bit address equality prover combining `ProofLib.Sep.proveAddrEqFast?` (`canonAddr64`)
    with `ProofLib.proveSepAddrEqMeta?` fallback for shift/nonlinear expressions. -/
def proveLensAddrEq? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (lhs rhs : Expr) : MetaM (Option Expr) := do
  if let some p ← proveAddrEqFast? ctx cacheRef lhs rhs then
    return some p
  ProofLib.proveSepAddrEqMeta? lhs rhs

/-- Candidate 1-step or composed algebraic lens extracted from `StructLayout` or `@[sep_lens]`. -/
structure RawLensCand where
  alpha     : Expr
  beta      : Expr
  wholeFn   : Expr
  focusFn   : Expr
  holeFn    : Expr
  getFn     : Expr
  putFn     : Expr
  guardFn?  : Option Expr
  lensProof : Expr
  /-- Optional proof builder `fun sVal invPrf? => MetaM (Option (put (get sVal) = sVal))`. -/
  putGetAt? : Option (Expr → Option Expr → MetaM (Option Expr)) := none

partial def peelListCons (e : Expr) : MetaM (Array Expr) := do
  let mut cur ← whnf e
  let mut acc : Array Expr := #[]
  for _ in [0:64] do
    if cur.isAppOfArity ``List.cons 3 then
      acc := acc.push (cur.getArg! 1)
      cur ← whnf (cur.getArg! 2)
    else
      break
  return acc

/-- Synthesize `put : M → β → M` for a single-constructor snapshot structure `M` given `get`. -/
def mkStructPutFn? (M beta get : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let fn := M.getAppFn
  let .const structName lvls := fn | return none
  let some sinfo := getStructureInfo? env structName | return none
  let fieldIdx? ← withLocalDeclD `m M fun mFVar => do
    let appReduced ← Core.betaReduce (mkApp get mFVar)
    if let .const projFn _ := appReduced.getAppFn then
      if let some pinfo ← getProjectionFnInfo? projFn then
        if appReduced.appArg! == mFVar then
          return some pinfo.i
    let body ← whnf appReduced
    match body with
    | .proj sName idx inner =>
      if sName == structName && inner == mFVar then pure (some idx) else pure none
    | _ => pure none
  let some fieldIdx := fieldIdx? | return none
  let ctorInfo := getStructureCtor env structName
  let params := M.getAppArgs
  let putFn ← withLocalDeclD `m M fun mVar =>
    withLocalDeclD `v beta fun vVar => do
      let mut ctorArgs : Array Expr := params
      for j in [0 : sinfo.fieldNames.size] do
        if j == fieldIdx then
          ctorArgs := ctorArgs.push vVar
        else
          ctorArgs := ctorArgs.push (.proj structName j mVar)
      let ctorApp := mkAppN (mkConst ctorInfo.name lvls) ctorArgs
      mkLambdaFVars #[mVar, vVar] ctorApp
  return some putFn

/-- Build canonical field address `p` (at offset `0`) or `p + k#64` using `mkBV64Lit`. -/
def mkCleanFieldAddr (base offExpr : Expr) : MetaM Expr := do
  if let some n ← evalClosedNat? offExpr then
    if n == 0 then return base
    else return ← mkAppM ``HAdd.hAdd #[base, mkBV64Lit n]
  return mkApp2 (mkConst ``fieldAddr) base offExpr

/-- Check whether `StructLayout.wf L` reduces to `true`, returning `none` if ill-formed. -/
def checkStructLayoutWf? (M L : Expr) : MetaM (Option Expr) := do
  let wfExpr := mkApp2 (mkConst ``StructLayout.wf) M L
  let wfRed ← whnf wfExpr
  if wfRed.isConstOf ``Bool.true then
    let goalTy ← mkEq wfExpr (mkConst ``Bool.true)
    return some (← mkExpectedTypeHint rflTrueExpr goalTy)
  return none

/-- Enumerate 1-step per-field `SepLens` candidates for any well-formed `StructLayout.own L p`.
    Returns `(isWellFormed, candidates)`. -/
def enumStructLayoutCands (wholeFn : Expr) : MetaM (Bool × Array RawLensCand) := do
  let wf ← whnfR wholeFn
  if !wf.isAppOfArity ``StructLayout.own 3 then return (true, #[])
  let M := wf.getArg! 0
  let L := wf.getArg! 1
  let p := wf.getArg! 2
  let some hwfPrf ← checkStructLayoutWf? M L
    | return (false, #[])
  let fieldsExpr ← mkAppM ``StructLayout.fields #[L]
  let flds ← peelListCons fieldsExpr
  let mut out : Array RawLensCand := #[]
  for h : idx in [0 : flds.size] do
    let fld ← whnfR flds[idx]
    let decoded? : Option (Expr × Expr × Expr) ← do
      if fld.isAppOfArity ``StructField.field8 3 then
        let off := fld.getArg! 1
        let get := fld.getArg! 2
        let beta := mkApp (mkConst ``BitVec) (mkNatLit 8)
        let addr ← mkCleanFieldAddr p off
        let focusFn := .lam `v beta (mkApp2 (mkConst ``Arm64.pointsTo8) addr (.bvar 0)) .default
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.field16 3 then
        let off := fld.getArg! 1
        let get := fld.getArg! 2
        let beta := mkApp (mkConst ``BitVec) (mkNatLit 16)
        let addr ← mkCleanFieldAddr p off
        let focusFn := .lam `v beta (mkApp2 (mkConst ``Arm64.pointsTo16) addr (.bvar 0)) .default
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.field32 3 then
        let off := fld.getArg! 1
        let get := fld.getArg! 2
        let beta := mkApp (mkConst ``BitVec) (mkNatLit 32)
        let addr ← mkCleanFieldAddr p off
        let focusFn := .lam `v beta (mkApp2 (mkConst ``Arm64.pointsTo32) addr (.bvar 0)) .default
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.field64 3 then
        let off := fld.getArg! 1
        let get := fld.getArg! 2
        let beta := mkApp (mkConst ``BitVec) (mkNatLit 64)
        let addr ← mkCleanFieldAddr p off
        let focusFn := .lam `v beta (mkApp2 (mkConst ``Arm64.pointsTo64) addr (.bvar 0)) .default
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.field128 3 then
        let off := fld.getArg! 1
        let get := fld.getArg! 2
        let beta := mkApp (mkConst ``BitVec) (mkNatLit 128)
        let addr ← mkCleanFieldAddr p off
        let focusFn := .lam `v beta (mkApp2 (mkConst ``Arm64.pointsTo128) addr (.bvar 0)) .default
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.slice 4 then
        let off := fld.getArg! 1
        let get := fld.getArg! 3
        let beta ← mkAppM ``List #[mkApp (mkConst ``BitVec) (mkNatLit 8)]
        let addr ← mkCleanFieldAddr p off
        let focusFn := mkApp (mkConst ``Arm64.pointsToBytes) addr
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.subArray 8 then
        let elemTy := fld.getArg! 1
        let off := fld.getArg! 2
        let stride := fld.getArg! 3
        let elemAt := fld.getArg! 5
        let get := fld.getArg! 7
        let beta ← mkAppM ``List #[elemTy]
        let addr ← mkCleanFieldAddr p off
        let focusFn ← mkAppOptM ``ProofLib.pointsToArray
          #[some elemTy, some stride, some elemAt, some addr]
        pure (some (beta, focusFn, get))
      else if fld.isAppOfArity ``StructField.dynArray 6 then
        let elemTy := fld.getArg! 1
        let off := fld.getArg! 2
        let stride := fld.getArg! 3
        let elemAt := fld.getArg! 4
        let get := fld.getArg! 5
        let beta ← mkAppM ``List #[elemTy]
        let addr ← mkCleanFieldAddr p off
        let focusFn ← mkAppOptM ``ProofLib.pointsToArray
          #[some elemTy, some stride, some elemAt, some addr]
        pure (some (beta, focusFn, get))
      else
        pure none
    if let some (beta, focusFn, get) := decoded? then
      if let some putFn ← mkStructPutFn? M beta get then
        let idxLit := mkNatLit idx
        let lenExpr ← mkAppM ``List.length #[fieldsExpr]
        let hidxTy ← mkAppM ``LT.lt #[idxLit, lenExpr]
        if let some hidxPrf ← (try some <$> mkDecideProof hidxTy catch _ => pure none) then
          let hgetPrf ← withLocalDeclD `m M fun mVar => do
            mkLambdaFVars #[mVar] (← mkEqRefl (mkApp focusFn (mkApp get mVar)))
          let hputPrf ← withLocalDeclD `m M fun mVar =>
            withLocalDeclD `v beta fun vVar => do
              mkLambdaFVars #[mVar, vVar] (← mkEqRefl (mkApp focusFn vVar))
          let holeFn := mkAppN (mkConst ``StructLayout.hole) #[M, L, idxLit, p]
          let hholePrf ← withLocalDeclD `m M fun mVar =>
            withLocalDeclD `v beta fun vVar => do
              mkLambdaFVars #[mVar, vVar]
                (← mkEqRefl (mkApp holeFn mVar))
          let prf := mkAppN (mkConst ``StructLayout.fieldLens)
            #[M, beta, L, idxLit, p, focusFn, get, putFn, hwfPrf, hidxPrf, hgetPrf, hputPrf, hholePrf]
          let pgBuilder : Expr → Option Expr → MetaM (Option Expr) := fun sVal _ => do
            let lhs := mkApp2 putFn sVal (mkApp get sVal)
            if ← isDefEq lhs sVal then
              return some (← mkExpectedTypeHint (← mkEqRefl sVal) (← mkEq lhs sVal))
            return none
          out := out.push {
            alpha := M
            beta := beta
            wholeFn := wholeFn
            focusFn := focusFn
            holeFn := holeFn
            getFn := get
            putFn := putFn
            guardFn? := none
            lensProof := prf
            putGetAt? := some pgBuilder
          }
  return (true, out)

/-- Candidate `WordCodec` carrier types for a given `LensAccessShape`. -/
def codecTypesForShape : LensAccessShape → Array Expr
  | .anyWidth 1 => #[mkApp (mkConst ``BitVec) (mkNatLit 8)]
  | .anyWidth 2 => #[mkApp (mkConst ``BitVec) (mkNatLit 16)]
  | .anyWidth 4 => #[mkApp (mkConst ``BitVec) (mkNatLit 32)]
  | .anyWidth 8 => #[mkApp (mkConst ``BitVec) (mkNatLit 64)]
  | .anyWidth 16 =>
    let bv128 := mkApp (mkConst ``BitVec) (mkNatLit 128)
    let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let pair64 := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bv64 bv64
    #[bv128, pair64]
  | .pair64 | .simd128 =>
    let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let pair64 := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bv64 bv64
    let bv128 := mkApp (mkConst ``BitVec) (mkNatLit 128)
    #[pair64, bv128]
  | .anyWidth 0 =>
    let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
    let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let bv16 := mkApp (mkConst ``BitVec) (mkNatLit 16)
    let bv128 := mkApp (mkConst ``BitVec) (mkNatLit 128)
    let pair64 := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bv64 bv64
    #[bv64, bv32, bv8, bv16, bv128, pair64]
  | .anyWidth _ => #[]

/-- Simplify `Core.betaReduce` + structure/typeclass field projections on constructor or
    `[reducible]`/`[instance]` terms (`(S.mk ...).f`, `WordCodec.pointsTo`, `WordCodec.encode`). -/
partial def simplifySnapExpr (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce e
  Core.transform e (pre := fun sub => do
    let fn := sub.getAppFn
    if let .const fnName _ := fn then
      if let some pinfo ← getProjectionFnInfo? fnName then
        if !pinfo.fromClass || pinfo.ctorName == ``WordCodec.mk then
          let args := sub.getAppArgs
          if h : pinfo.numParams < args.size then
            let instRed ← withReducibleAndInstances (whnf args[pinfo.numParams])
            if instRed.getAppFn.isConstOf pinfo.ctorName then
              let rebuilt := mkAppN fn (args.set pinfo.numParams instRed)
              if let some unf ← unfoldDefinition? rebuilt then
                let reduced ← whnfCore unf
                return .visit (← Core.betaReduce reduced)
    if let .proj sName idx sExpr := fn then
      if !(isClass (← getEnv) sName) || sName == ``WordCodec then
        let sRed ← withReducibleAndInstances (whnf sExpr)
        let rebuilt := mkAppN (.proj sName idx sRed) sub.getAppArgs
        let reduced ← whnfCore rebuilt
        if reduced != rebuilt then
          return .visit (← Core.betaReduce reduced)
    return .continue)

/-- Unfold thin lens focus wrappers (`WordCodec.pointsTo` on concrete instances and `slotPairAt`)
    to raw `↦` / `∗` atoms while preserving kernel definitional equality. -/
def reduceFocusCell (e : Expr) : MetaM Expr := do
  let mut cur ← simplifySnapExpr e
  if cur.isAppOfArity ``slotPairAt 2 then
    if let some unf ← unfoldDefinition? cur then
      cur ← simplifySnapExpr unf
  return cur

/-- Extract `(addr, widthBytes)` if `focusFn` is a leaf memory cell/pair predicate. -/
def extractFocusLeaf? (beta focusFn : Expr) : MetaM (Option (Expr × Nat)) := do
  withLocalDeclD `v beta fun vVar => do
    let fb ← reduceFocusCell (mkApp focusFn vVar)
    if fb.isAppOfArity ``Arm64.pointsTo8 2 && !(fb.getArg! 0).containsFVar vVar.fvarId! then
      return some (fb.getArg! 0, 1)
    if fb.isAppOfArity ``Arm64.pointsTo16 2 && !(fb.getArg! 0).containsFVar vVar.fvarId! then
      return some (fb.getArg! 0, 2)
    if fb.isAppOfArity ``Arm64.pointsTo32 2 && !(fb.getArg! 0).containsFVar vVar.fvarId! then
      return some (fb.getArg! 0, 4)
    if fb.isAppOfArity ``Arm64.pointsTo64 2 && !(fb.getArg! 0).containsFVar vVar.fvarId! then
      return some (fb.getArg! 0, 8)
    if fb.isAppOfArity ``Arm64.pointsTo128 2 && !(fb.getArg! 0).containsFVar vVar.fvarId! then
      return some (fb.getArg! 0, 16)
    if fb.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      let l ← whnfR (fb.getArg! 0)
      let r ← whnfR (fb.getArg! 1)
      if l.isAppOfArity ``Arm64.pointsTo64 2 && r.isAppOfArity ``Arm64.pointsTo64 2 &&
         !(l.getArg! 0).containsFVar vVar.fvarId! then
        return some (l.getArg! 0, 16)
    return none

partial def collectNatCandidatesVisit (ctx : CtxFacts) (e : Expr) (arr : Array Expr) : Array Expr :=
  let pushUniq (a : Array Expr) (x : Expr) : Array Expr :=
    if !x.hasLooseBVars && !a.contains x then a.push x else a
  let e := e.consumeMData
  let arr :=
    if e.isAppOfArity ``BitVec.ofNat 2 then pushUniq arr (e.getArg! 1)
    else if e.isAppOfArity ``BitVec.zeroExtend 3 || e.isAppOfArity ``BitVec.setWidth 3 then
      let srcW := e.getArg! 0
      let bv := e.getArg! 2
      pushUniq arr (mkApp2 (mkConst ``BitVec.toNat) srcW bv)
    else arr
  let arr :=
    if let .fvar fv := e then
      match ctx.letVals[fv]? with
      | some v => collectNatCandidatesVisit ctx v arr
      | none => arr
    else arr
  match e with
  | .app f a => collectNatCandidatesVisit ctx a (collectNatCandidatesVisit ctx f arr)
  | _ => arr

/-- Collect candidate `Nat` index/offset expressions from `targetEa` and optional `(base, stride?)`. -/
def collectNatCandidates (ctx : CtxFacts) (base? : Option Expr) (stride? : Option Nat := none)
    (targetEa : Expr) : MetaM (Array Expr) := do
  let mut cands : Array Expr := #[]
  let pushUniq (arr : Array Expr) (x : Expr) : Array Expr :=
    if !x.hasLooseBVars && !arr.contains x then arr.push x else arr
  cands := collectNatCandidatesVisit ctx targetEa cands
  if let some base := base? then
    let (rBase, oBase) := peelAddrRoot ctx.letVals base
    let (rTgt, oTgt) := peelAddrRoot ctx.letVals targetEa
    let sameRoot ← do
      if rBase == rTgt then pure true
      else
        let (b1, o1) ← ProofLib.sepAddrBaseOff base
        let (b2, o2) ← ProofLib.sepAddrBaseOff targetEa
        let _ := (o1, o2)
        if b1 == b2 then pure true else withReducibleAndInstances (isDefEq rBase rTgt)
    if sameRoot then
      if oTgt ≥ oBase then
        let d := (oTgt - oBase).toNat
        if let some st := stride? then
          if st > 0 then cands := pushUniq cands (mkNatLit (d / st))
        for div in #[1, 8, 4, 2, 16] do
          if d % div == 0 then
            cands := pushUniq cands (mkNatLit (d / div))
      else
        let dNeg := (oBase - oTgt).toNat
        if dNeg >= 16 && dNeg % 16 == 0 then
          cands := pushUniq cands (mkNatLit (dNeg / 16 - 1))
  cands := pushUniq cands (mkNatLit 0)
  return cands

/-- Find any unassigned `Nat`-typed metavariable occurring inside `e`. -/
partial def findUnassignedNatMVar? (e : Expr) : MetaM (Option MVarId) := do
  let e ← instantiateMVars e
  match e.find? (·.isMVar) with
  | none => return none
  | some mv =>
    let mvid := mv.mvarId!
    let ty ← instantiateMVars (← mvid.getType)
    if ty.isConstOf ``Nat then return some mvid
    return none

/-- Extract `(basePtr?, closedStride?)` hint from `wholeFn`. -/
def wholeBaseHint? (wholeFn : Expr) : MetaM (Option Expr × Option Nat) := do
  let wf ← whnfR wholeFn
  if wf.isAppOfArity ``ProofLib.pointsToArray 4 then
    let st? ← evalClosedNat? (wf.getArg! 1)
    return (some (wf.getArg! 3), st?)
  if wf.isAppOfArity ``Arm64.pointsToBytes 1 then return (some (wf.getArg! 0), none)
  if wf.isAppOfArity ``slotsDownFrom 1 then return (some (wf.getArg! 0), some 16)
  return (none, none)

/-- Discharge pure side-condition subgoals (`i < xs.length`, `off + w ≤ bs.length`, `dom`, etc.). -/
def dischargeLensSideGoal (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let savedGoals ← getGoals
  setGoals [g]
  let ok1 ← ProofLib.tryTacticCatchRuntimeBool <| evalTactic (← `(tactic| (
    try dsimp only [_root_.ProofLib.Sep.WordCodec.width, _root_.ProofLib.Sep.instWordCodec8,
      _root_.ProofLib.Sep.instWordCodec16, _root_.ProofLib.Sep.instWordCodec32,
      _root_.ProofLib.Sep.instWordCodec64, _root_.ProofLib.Sep.instWordCodec128,
      _root_.ProofLib.Sep.instWordCodecPair64]
    try simp_all only [List.length_set, List.length_cons, List.length_nil, Nat.zero_add,
      ProofLib.ByteSlice.write_length, ProofLib.ByteSlice.write8_length,
      _root_.ProofLib.Sep.WordCodec.encode_len]
    first
      | done
      | assumption
      | trivial
      | decide
      | omega
      | bv_omega
      | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | (constructor <;> first | assumption | trivial | decide | omega | bv_omega)
      | (intro i hi; first | assumption | solve_by_elim | (simp_all; try omega))
  )))
  if ok1 && (← getUnsolvedGoals).isEmpty then
    setGoals savedGoals
    Core.setMessageLog savedMsgs
    return true
  restoreState saved
  Core.setMessageLog savedMsgs
  setGoals [g]
  let ok2 ← ProofLib.tryTacticCatchRuntimeBool do
    evalTactic (← `(tactic| (
      try dsimp only [_root_.ProofLib.Sep.WordCodec.width, _root_.ProofLib.Sep.instWordCodec8,
        _root_.ProofLib.Sep.instWordCodec16, _root_.ProofLib.Sep.instWordCodec32,
        _root_.ProofLib.Sep.instWordCodec64, _root_.ProofLib.Sep.instWordCodec128,
        _root_.ProofLib.Sep.instWordCodecPair64]
      intro i hi
    )))
    let gCur ← getMainGoal
    let lctx ← gCur.withContext getLCtx
    let mut solved := false
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let sTry ← saveState
      let okApp ← ProofLib.tryTacticCatchRuntimeBool do
        let subgs ← gCur.apply (mkFVar ldecl.fvarId)
        setGoals subgs
        evalTactic (← `(tactic| all_goals (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)))
      if okApp && (← getUnsolvedGoals).isEmpty then
        solved := true
        break
      restoreState sTry
    if !solved then throwError "side goal unsolved"
  let done := ok2 && (← getUnsolvedGoals).isEmpty
  if !done then
    restoreState saved
    Core.setMessageLog savedMsgs
  else
    setGoals savedGoals
    Core.setMessageLog savedMsgs
  return done

/-- Synthesized `SepLensAt` bundle ready for `sepWP_open_lens` / `sepWP_switch_lens`. -/
structure FinalLensAt where
  beta     : Expr
  focusFn  : Expr
  holeExpr : Expr
  valExpr  : Expr
  putExpr  : Expr
  hLensAt  : Expr
  isLawful : Bool
  hPutGet  : Expr

/-- Turn a `RawLensCand` at concrete state `sVal` into a `FinalLensAt` bundle. -/
def finalizeLensAt? (c : RawLensCand) (sVal : Expr) : TacticM (Option FinalLensAt) := do
  let valExpr ← simplifySnapExpr (mkApp c.getFn sVal)
  let putExpr ← withLocalDeclD `v c.beta fun vVar => do
    let body ← simplifySnapExpr (mkApp2 c.putFn sVal vVar)
    mkLambdaFVars #[vVar] body
  let holeExpr ← Core.betaReduce (mkApp c.holeFn sVal)
  let (hLensAt, invPrf?) ← match c.guardFn? with
    | none =>
      let rawAt := mkAppN (mkConst ``SepLens.atState)
        #[c.alpha, c.beta, c.wholeFn, c.focusFn, c.holeFn, c.getFn, c.putFn, c.lensProof, sVal]
      let targetTy := mkAppN (mkConst ``SepLensAt)
        #[c.alpha, c.beta, c.wholeFn, c.focusFn, holeExpr, sVal, valExpr, putExpr]
      pure (← mkExpectedTypeHint rawAt targetTy, none)
    | some invFn =>
      let invGoalTy ← simplifySnapExpr (mkApp invFn sVal)
      let invMVar ← mkFreshExprMVar invGoalTy
      if !(← dischargeLensSideGoal invMVar.mvarId!) then
        return none
      let invPrf ← instantiateMVars invMVar
      let rawAt := mkAppN (mkConst ``SepLens.atGuarded)
        #[c.alpha, c.beta, invFn, c.wholeFn, c.focusFn, c.holeFn, c.getFn, c.putFn,
          c.lensProof, sVal, invPrf]
      let targetTy := mkAppN (mkConst ``SepLensAt)
        #[c.alpha, c.beta, c.wholeFn, c.focusFn, holeExpr, sVal, valExpr, putExpr]
      pure (← mkExpectedTypeHint rawAt targetTy, some invPrf)
  let putValGoalTy ← mkEq (mkApp putExpr valExpr) sVal
  let pgOpt : Option Expr ← do
    if let some builder := c.putGetAt? then
      if let some p ← (try builder sVal invPrf? catch _ => pure none) then
        if let some pTyped ← (try some <$> mkExpectedTypeHint p putValGoalTy catch _ => pure none) then
          pure (some pTyped)
        else
          pure none
      else
        pure none
    else if ← isDefEq (mkApp putExpr valExpr) sVal then
      pure (some (← mkExpectedTypeHint (← mkEqRefl sVal) putValGoalTy))
    else
      pure none
  let (isLawful, hPutGet) := match pgOpt with
    | some p => (true, p)
    | none => (false, mkConst ``True.intro)
  return some { beta := c.beta, focusFn := c.focusFn, holeExpr, valExpr, putExpr,
                hLensAt, isLawful, hPutGet }

/-- Build optional `put (get sVal) = sVal` proof builder for built-in guarded `@[sep_lens]` rules. -/
def builtinRulePutGetBuilder? (ruleName : Name) (alpha beta getFn putFn : Expr) :
    Option (Expr → Option Expr → MetaM (Option Expr)) :=
  if ruleName == ``pointsToArray_lens || ruleName == ``pointsToArray_shift_lens ||
     ruleName == ``slotsDownFrom_lens || ruleName == ``slotsDownFrom_neg_lens then
    some fun sVal _ => do
      let elemTy := alpha.getArg! 0
      let dflt ← synthInstance (mkApp (mkConst ``Inhabited [Level.zero]) elemTy)
      let dVal ← mkAppOptM ``default #[some elemTy, some dflt]
      -- Extract `i` from `getFn` (`fun xs => xs.getD i default`)
      let getBody ← Core.betaReduce (mkApp getFn sVal)
      if getBody.isAppOfArity ``List.getD 4 then
        let iExpr := getBody.getArg! 2
        let p := mkAppN (mkConst ``list_set_getD_self) #[elemTy, sVal, iExpr, dVal]
        let goalTy ← mkEq (mkApp2 putFn sVal (mkApp getFn sVal)) sVal
        return some (← mkExpectedTypeHint p goalTy)
      return none
  else if ruleName == ``sliceWindow_lens then
    some fun sVal invPrf? => do
      let some invPrf := invPrf? | return none
      let instVal ← synthInstance (mkApp (mkConst ``WordCodec) beta)
      let getBody ← Core.betaReduce (mkApp getFn sVal)
      -- `c.decode (ByteSlice.slice bs off c.width)`
      if getBody.appArg!.isAppOfArity ``ProofLib.ByteSlice.slice 3 then
        let offExpr := getBody.appArg!.getArg! 1
        let p := mkAppN (mkConst ``sliceWindow_put_get) #[beta, instVal, sVal, offExpr, invPrf]
        let goalTy ← mkEq (mkApp2 putFn sVal (mkApp getFn sVal)) sVal
        return some (← mkExpectedTypeHint p goalTy)
      return none
  else if ruleName == ``sliceWindow_zero_lens then
    some fun sVal invPrf? => do
      let some invPrf := invPrf? | return none
      let instVal ← synthInstance (mkApp (mkConst ``WordCodec) beta)
      let h0Ty ← mkAppM ``LE.le
        #[← mkAppM ``HAdd.hAdd #[mkNatLit 0, mkApp2 (mkConst ``WordCodec.width) beta instVal],
          ← mkAppM ``List.length #[sVal]]
      let p := mkAppN (mkConst ``sliceWindow_put_get)
        #[beta, instVal, sVal, mkNatLit 0, ← mkExpectedTypeHint invPrf h0Ty]
      let goalTy ← mkEq (mkApp2 putFn sVal (mkApp getFn sVal)) sVal
      return some (← mkExpectedTypeHint p goalTy)
  else
    none

/-- Instantiate ONE `@[sep_lens]` rule IN PLACE if it matches `wholeFn` (and optional leaf target
    or outer index `natIdx?`). Supports both `SepLens` and `LawfulSepLens` rules. -/
def matchSingleRuleInPlace? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (ruleName : Name) (wholeFn : Expr)
    (leafTarget? : Option (Expr × LensAccessShape))
    (outerNatIdx? : Option Expr := none) : TacticM (Option RawLensCand) := do
  let codecTypes : Array (Option Expr) := match leafTarget? with
    | some (_, sh) => (codecTypesForShape sh).map some
    | none => #[none]
  for codecTy? in codecTypes do
    let saved ← saveState
    let savedMsgs ← Core.getMessageLog
    let res? ← ProofLib.tryTacticCatchRuntime do
      let ruleConst ← mkConstWithFreshMVarLevels ruleName
      let (mvars, bis, retTy) ← forallMetaTelescopeReducing (← inferType ruleConst)
      let isLawfulRet := retTy.isAppOfArity ``LawfulSepLens 7
      if !retTy.isAppOfArity ``SepLens 7 && !isLawfulRet then
        throwError "not SepLens / LawfulSepLens"
      if let some codecTy := codecTy? then
        for i in [0 : mvars.size] do
          if bis[i]! == .instImplicit then
            let instTy ← instantiateMVars (← mvars[i]!.mvarId!.getType)
            if instTy.isAppOfArity ``WordCodec 1 && (instTy.getArg! 0).isMVar then
              let _ ← isDefEq (instTy.getArg! 0) codecTy
      let wfRed ← whnfR wholeFn
      if wfRed.isAppOfArity ``ProofLib.pointsToArray 4 then
        if let some strideNat ← evalClosedNat? (wfRed.getArg! 1) then
          let shiftOpt : Option Nat := match strideNat with
            | 1 => some 0 | 2 => some 1 | 4 => some 2 | 8 => some 3 | 16 => some 4
            | 32 => some 5 | 64 => some 6 | _ => none
          if let some sh := shiftOpt then
            for mv in mvars do
              let mvid := mv.mvarId!
              if !(← mvid.isAssigned) then
                let decl ← mvid.getDecl
                if decl.userName == `shift && decl.type.isConstOf ``Nat then
                  mvid.assign (mkNatLit sh)
      let rawWhole ← instantiateMVars (retTy.getArg! 2)
      let (candWhole, guardFn?) :=
        if rawWhole.isAppOfArity ``Guarded 3 then
          (rawWhole.getArg! 2, some (rawWhole.getArg! 1))
        else
          (rawWhole, none)
      unless ← withReducibleAndInstances (isDefEq candWhole wholeFn) do
        throwError "whole mismatch"
      for i in [0 : mvars.size] do
        if bis[i]! == .instImplicit && !(← mvars[i]!.mvarId!.isAssigned) then
          let instTy ← instantiateMVars (← mvars[i]!.mvarId!.getType)
          let instVal ← synthInstance instTy
          mvars[i]!.mvarId!.assign instVal
      if let some idxVal := outerNatIdx? then
        for mv in mvars do
          let mvid := mv.mvarId!
          if !(← mvid.isAssigned) then
            let mty ← instantiateMVars (← mvid.getType)
            if mty.isConstOf ``Nat then
              mvid.assign idxVal
              break
      let alpha ← instantiateMVars (retTy.getArg! 0)
      let beta ← instantiateMVars (retTy.getArg! 1)
      let focusFn ← instantiateMVars (retTy.getArg! 3)
      if let some (targetEa, shape) := leafTarget? then
        let reqW := shape.byteWidth
        let some (candAddr0, candW) ← extractFocusLeaf? beta focusFn
          | throwError "not leaf"
        if reqW != 0 && candW != reqW then throwError "width mismatch"
        let candAddr ← instantiateMVars candAddr0
        let matchedAddr ← do
          if candAddr.isMVar then
            isDefEq candAddr targetEa
          else if let some natMVar ← findUnassignedNatMVar? candAddr then
            if ← withReducibleAndInstances (isDefEq candAddr targetEa) then
              pure true
            else
              let (baseHint?, strideHint?) ← wholeBaseHint? wholeFn
              let natCands ← collectNatCandidates ctx baseHint? strideHint? targetEa
              let mut ok := false
              for nc in natCands do
                let sNat ← saveState
                natMVar.assign nc
                let ca ← instantiateMVars candAddr
                if (← proveLensAddrEq? ctx cacheRef ca targetEa).isSome then
                  ok := true
                  break
                restoreState sNat
              pure ok
          else
            pure (← proveLensAddrEq? ctx cacheRef candAddr targetEa).isSome
        if !matchedAddr then throwError "addr mismatch"
      let mut sideGoals : Array MVarId := #[]
      for mv in mvars do
        let mvid := mv.mvarId!
        if !(← mvid.isAssigned) then
          let mty ← instantiateMVars (← mvid.getType)
          if ← isProp mty then sideGoals := sideGoals.push mvid
          else throwError "unassigned non-Prop parameter"
      for sg in sideGoals do
        if !(← sg.isAssigned) then
          if !(← dischargeLensSideGoal sg) then throwError "side goal failed"
      let rawRuleApp ← instantiateMVars (mkAppN ruleConst mvars)
      let holeFn ← instantiateMVars (retTy.getArg! 4)
      let getFn ← instantiateMVars (retTy.getArg! 5)
      let putFn ← instantiateMVars (retTy.getArg! 6)
      let guardFnInst? ← guardFn?.mapM instantiateMVars
      let (sepLensPrf, pgBuilder?) ← do
        if isLawfulRet then
          let toSep := mkAppN (mkConst ``LawfulSepLens.toSepLens)
            #[alpha, beta, rawWhole, focusFn, holeFn, getFn, putFn, rawRuleApp]
          let pgB : Option (Expr → Option Expr → MetaM (Option Expr)) :=
            if guardFnInst?.isNone then
              some fun sVal _ => do
                return some (mkAppN (mkConst ``LawfulSepLens.put_get)
                  #[alpha, beta, rawWhole, focusFn, holeFn, getFn, putFn, rawRuleApp, sVal])
            else
              none
          pure (toSep, pgB)
        else
          pure (rawRuleApp, builtinRulePutGetBuilder? ruleName alpha beta getFn putFn)
      return ({
        alpha := alpha
        beta := beta
        wholeFn := wholeFn
        focusFn := focusFn
        holeFn := holeFn
        getFn := getFn
        putFn := putFn
        guardFn? := guardFnInst?
        lensProof := sepLensPrf
        putGetAt? := pgBuilder?
      } : RawLensCand)
    match res? with
    | some cand =>
      Core.setMessageLog savedMsgs
      return some cand
    | none =>
      restoreState saved
      Core.setMessageLog savedMsgs
  return none

/-- Compose outer lens `c1` with inner lens `c2` (`SepLens.trans` / `SepLens.trans_guarded` /
    `SepLens.trans_both_guarded`), propagating `put_get` when both `c1` and `c2` are lawful. -/
def composeRawLenses? (c1 c2 : RawLensCand) : TacticM (Option RawLensCand) := do
  let holeBase ← withLocalDeclD `s c1.alpha fun sVar => do
    let h1 := mkApp c1.holeFn sVar
    let h2 := mkApp c2.holeFn (mkApp c1.getFn sVar)
    mkLambdaFVars #[sVar] (mkApp2 (mkConst ``Arm64.SepProp.sepConj) h1 h2)
  let getComp ← withLocalDeclD `s c1.alpha fun sVar =>
    mkLambdaFVars #[sVar] (mkApp c2.getFn (mkApp c1.getFn sVar))
  let putComp ← withLocalDeclD `s c1.alpha fun sVar =>
    withLocalDeclD `v c2.beta fun vVar => do
      let inner := mkApp2 c2.putFn (mkApp c1.getFn sVar) vVar
      mkLambdaFVars #[sVar, vVar] (mkApp2 c1.putFn sVar inner)
  let mkCompPutGet (splitInv : Bool) : Option (Expr → Option Expr → MetaM (Option Expr)) :=
    match c1.putGetAt?, c2.putGetAt? with
    | some pg1, some pg2 =>
      some fun sVal invPrf? => do
        let (inv1?, inv2?) :=
          if splitInv then
            match invPrf? with
            | some p => (some (mkProj ``And 0 p), some (mkProj ``And 1 p))
            | none => (none, none)
          else if c1.guardFn?.isSome then (invPrf?, none)
          else (none, invPrf?)
        let midVal := mkApp c1.getFn sVal
        let some p2 ← pg2 midVal inv2? | return none
        let some p1 ← pg1 sVal inv1? | return none
        let fOuter ← withLocalDeclD `m c1.beta fun mVar =>
          mkLambdaFVars #[mVar] (mkApp2 c1.putFn sVal mVar)
        let step1 ← mkCongrArg fOuter p2
        return some (← mkEqTrans step1 p1)
    | _, _ => none
  match c1.guardFn?, c2.guardFn? with
  | none, none =>
    let prf := mkAppN (mkConst ``SepLens.trans)
      #[c1.alpha, c1.beta, c2.beta, c1.wholeFn, c1.focusFn, c2.focusFn,
        c1.holeFn, c2.holeFn, c1.getFn, c1.putFn, c2.getFn, c2.putFn,
        c1.lensProof, c2.lensProof]
    return some {
      alpha := c1.alpha, beta := c2.beta, wholeFn := c1.wholeFn, focusFn := c2.focusFn,
      holeFn := holeBase, getFn := getComp, putFn := putComp, guardFn? := none,
      lensProof := prf, putGetAt? := mkCompPutGet false
    }
  | some inv1, none =>
    let guardedWhole1 := mkApp3 (mkConst ``Guarded) c1.alpha inv1 c1.wholeFn
    let prf := mkAppN (mkConst ``SepLens.trans)
      #[c1.alpha, c1.beta, c2.beta, guardedWhole1, c1.focusFn, c2.focusFn,
        c1.holeFn, c2.holeFn, c1.getFn, c1.putFn, c2.getFn, c2.putFn,
        c1.lensProof, c2.lensProof]
    return some {
      alpha := c1.alpha, beta := c2.beta, wholeFn := c1.wholeFn, focusFn := c2.focusFn,
      holeFn := holeBase, getFn := getComp, putFn := putComp, guardFn? := some inv1,
      lensProof := prf, putGetAt? := mkCompPutGet false
    }
  | none, some inv2 =>
    let hgpOpt ← ProofLib.tryTacticCatchRuntime do
      withLocalDeclD `s c1.alpha fun sVar =>
        withLocalDeclD `m c1.beta fun mVar => do
          let lhs := mkApp c1.getFn (mkApp2 c1.putFn sVar mVar)
          unless ← isDefEq lhs mVar do throwError "not rfl"
          mkLambdaFVars #[sVar, mVar] (← mkEqRefl mVar)
    let some hgp := hgpOpt | return none
    let guardComp ← withLocalDeclD `s c1.alpha fun sVar =>
      mkLambdaFVars #[sVar] (mkApp inv2 (mkApp c1.getFn sVar))
    let prf := mkAppN (mkConst ``SepLens.trans_guarded)
      #[c1.alpha, c1.beta, c2.beta, inv2, c1.wholeFn, c1.focusFn, c2.focusFn,
        c1.holeFn, c2.holeFn, c1.getFn, c1.putFn, c2.getFn, c2.putFn,
        c1.lensProof, c2.lensProof, hgp]
    return some {
      alpha := c1.alpha, beta := c2.beta, wholeFn := c1.wholeFn, focusFn := c2.focusFn,
      holeFn := holeBase, getFn := getComp, putFn := putComp, guardFn? := some guardComp,
      lensProof := prf, putGetAt? := mkCompPutGet false
    }
  | some inv1, some inv2 =>
    let hgpOpt ← ProofLib.tryTacticCatchRuntime do
      withLocalDeclD `s c1.alpha fun sVar =>
        withLocalDeclD `m c1.beta fun mVar =>
          withLocalDeclD `h (mkApp inv1 sVar) fun hVar => do
            let goalTy ← mkEq (mkApp c1.getFn (mkApp2 c1.putFn sVar mVar)) mVar
            let mv ← mkFreshExprMVar goalTy
            let savedG ← getGoals
            setGoals [mv.mvarId!]
            evalTactic (← `(tactic| simp_all only [List.getD_eq_getElem?_getD,
              List.getElem?_set_self, Option.getD_some]))
            setGoals savedG
            mkLambdaFVars #[sVar, mVar, hVar] (← instantiateMVars mv)
    let some hgp := hgpOpt | return none
    let guardComp ← withLocalDeclD `s c1.alpha fun sVar =>
      mkLambdaFVars #[sVar] (mkAnd (mkApp inv1 sVar) (mkApp inv2 (mkApp c1.getFn sVar)))
    let holeGuarded ← withLocalDeclD `s c1.alpha fun sVar => do
      let pPure := mkApp (mkConst ``Arm64.SepProp.pure) (mkApp inv1 sVar)
      let h1 := mkApp c1.holeFn sVar
      let h2 := mkApp c2.holeFn (mkApp c1.getFn sVar)
      mkLambdaFVars #[sVar]
        (mkApp2 (mkConst ``Arm64.SepProp.sepConj) pPure
          (mkApp2 (mkConst ``Arm64.SepProp.sepConj) h1 h2))
    let prf := mkAppN (mkConst ``SepLens.trans_both_guarded)
      #[c1.alpha, c1.beta, c2.beta, inv1, inv2, c1.wholeFn, c1.focusFn, c2.focusFn,
        c1.holeFn, c2.holeFn, c1.getFn, c1.putFn, c2.getFn, c2.putFn,
        c1.lensProof, c2.lensProof, hgp]
    return some {
      alpha := c1.alpha, beta := c2.beta, wholeFn := c1.wholeFn, focusFn := c2.focusFn,
      holeFn := holeGuarded, getFn := getComp, putFn := putComp, guardFn? := some guardComp,
      lensProof := prf, putGetAt? := mkCompPutGet true
    }

/-- Synthesize a 1-deep or 2-deep composed `FinalLensAt` focusing `(targetEa, shape)` out of
    `wholeFn sVal`. Throws immediately if `wholeFn` is an ill-formed `StructLayout`. -/
def synthSepLensAtForWhole? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (wholeFn sVal targetEa : Expr) (shape : LensAccessShape) :
    TacticM (Option FinalLensAt) := do
  let reqW := shape.byteWidth
  let (structWf, structCands) ← enumStructLayoutCands wholeFn
  if !structWf then
    throwError m!"lens_open: StructLayout `{wholeFn}` is ill-formed (overlapping or out-of-bounds fields)"
  let ruleNames ← getSepLensRules
  -- 1. Try 1-deep StructLayout scalar fields
  for sc in structCands do
    if let some (candAddr, candW) ← extractFocusLeaf? sc.beta sc.focusFn then
      if (reqW == 0 || candW == reqW) && (← proveLensAddrEq? ctx cacheRef candAddr targetEa).isSome then
        if let some res ← finalizeLensAt? sc sVal then
          return some res
  -- 2. Try 1-deep `@[sep_lens]` rules
  for rn in ruleNames do
    let saved ← saveState
    if let some rc ← matchSingleRuleInPlace? ctx cacheRef rn wholeFn (some (targetEa, shape)) then
      if let some res ← finalizeLensAt? rc sVal then
        return some res
    restoreState saved
  -- 3. Try 2-deep composition (`SepLens.trans` / `SepLens.trans_guarded` / `SepLens.trans_both_guarded`):
  --    outer lens from StructLayout container fields, unindexed `@[sep_lens]` rules, OR
  --    symbolic-index `pointsToArray` rules instantiated at candidate indices from `targetEa`.
  let mut outerCands : Array RawLensCand := #[]
  for sc in structCands do
    if (← extractFocusLeaf? sc.beta sc.focusFn).isNone then
      outerCands := outerCands.push sc
  let (baseHint?, strideHint?) ← wholeBaseHint? wholeFn
  let idxCands ← collectNatCandidates ctx baseHint? strideHint? targetEa
  for rn in ruleNames do
    let saved1 ← saveState
    if let some rc ← matchSingleRuleInPlace? ctx cacheRef rn wholeFn none none then
      if (← extractFocusLeaf? rc.beta rc.focusFn).isNone then
        outerCands := outerCands.push rc
    else
      restoreState saved1
      for idxExpr in idxCands do
        let savedIdx ← saveState
        if let some rc ← matchSingleRuleInPlace? ctx cacheRef rn wholeFn none (some idxExpr) then
          if (← extractFocusLeaf? rc.beta rc.focusFn).isNone then
            outerCands := outerCands.push rc
        else
          restoreState savedIdx
  for c1 in outerCands do
    -- 3a. Inner lens from `StructLayout` fields of `c1.focusFn` (e.g. `pointsToArray` of structs!)
    let (innerWf, innerStructCands) ← enumStructLayoutCands c1.focusFn
    if !innerWf then
      throwError m!"lens_open: inner StructLayout `{c1.focusFn}` is ill-formed"
    for sc2 in innerStructCands do
      if let some (candAddr, candW) ← extractFocusLeaf? sc2.beta sc2.focusFn then
        if (reqW == 0 || candW == reqW) && (← proveLensAddrEq? ctx cacheRef candAddr targetEa).isSome then
          let savedComp ← saveState
          if let some cc ← composeRawLenses? c1 sc2 then
            if let some res ← finalizeLensAt? cc sVal then
              return some res
          restoreState savedComp
    -- 3b. Inner lens from `@[sep_lens]` rules
    for rn2 in ruleNames do
      let saved2 ← saveState
      if let some c2 ← matchSingleRuleInPlace? ctx cacheRef rn2 c1.focusFn (some (targetEa, shape)) then
        if let some cc ← composeRawLenses? c1 c2 then
          if let some res ← finalizeLensAt? cc sVal then
            return some res
      restoreState saved2
  return none

/-- Extract `(amExpr, shape)` from a load/store `Instr` expression. -/
def extractInstrMemAccess? (inst : Expr) : MetaM (Option (Expr × LensAccessShape)) := do
  let szBytes? (szExpr : Expr) : MetaM (Option Nat) := do
    let s ← whnf szExpr
    if s.isConstOf ``Arm64.MemWidth.B8 || s.isConstOf ``Arm64.SimdMemSize.B8 then return some 1
    if s.isConstOf ``Arm64.MemWidth.H16 || s.isConstOf ``Arm64.SimdMemSize.H16 then return some 2
    if s.isConstOf ``Arm64.MemWidth.W32 || s.isConstOf ``Arm64.RegWidth.W32 ||
       s.isConstOf ``Arm64.SimdMemSize.S32 then return some 4
    if s.isConstOf ``Arm64.MemWidth.X64 || s.isConstOf ``Arm64.RegWidth.W64 ||
       s.isConstOf ``Arm64.SimdMemSize.D64 then return some 8
    return none
  if inst.isAppOfArity ``Arm64.Instr.ldr 5 then
    if let some b ← szBytes? (inst.getArg! 1) then return some (inst.getArg! 4, .anyWidth b)
  if inst.isAppOfArity ``Arm64.Instr.str 3 then
    if let some b ← szBytes? (inst.getArg! 0) then return some (inst.getArg! 2, .anyWidth b)
  if inst.isAppOfArity ``Arm64.Instr.ldp 5 then
    if let some b ← szBytes? (inst.getArg! 1) then
      return some (inst.getArg! 4, if b == 8 then .pair64 else .anyWidth (2 * b))
  if inst.isAppOfArity ``Arm64.Instr.stp 4 then
    if let some b ← szBytes? (inst.getArg! 0) then
      return some (inst.getArg! 3, if b == 8 then .pair64 else .anyWidth (2 * b))
  if inst.isAppOfArity ``Arm64.Instr.ldrSimd 3 || inst.isAppOfArity ``Arm64.Instr.strSimd 3 then
    let sz ← whnf (inst.getArg! 0)
    if sz.isConstOf ``Arm64.SimdMemSize.Q128 then return some (inst.getArg! 2, .simd128)
    if let some b ← szBytes? sz then return some (inst.getArg! 2, .anyWidth b)
  return none

/-- Peek at the next `SepWP` instruction at `s.pc` and return `(effectiveAddr, shape)`. -/
def peekSepWPNextMemAccess? : TacticM (Option (Expr × LensAccessShape)) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let res? ← ProofLib.tryTacticCatchRuntime do
    let (progExpr, targetPcExpr, pcExpr) ← ProofLib.getSepWPStateAndPC
    if ← withReducibleAndInstances (isDefEq pcExpr targetPcExpr) then
      throwError "at target"
    let g0 ← getMainGoal
    let sExpr ← g0.withContext do
      let ty := (← instantiateMVars (← g0.getType)).consumeMData
      return ty.getArg! 2
    let instMVar ← g0.withContext <| mkFreshExprMVar (mkConst ``Arm64.Instr)
    let someInst ← g0.withContext <| mkAppM ``Option.some #[instMVar]
    let fetchLhs := mkApp2 (mkConst ``Arm64.Program.fetch) progExpr pcExpr
    let fetchGoal ← g0.withContext <| mkFreshExprMVar (← mkEq fetchLhs someInst)
    setGoals [fetchGoal.mvarId!]
    ProofLib.closeFetchSubgoal
    let inst ← instantiateMVars instMVar
    setGoals [g0]
    let some (amExpr, shape) ← g0.withContext <| extractInstrMemAccess? inst
      | throwError "not load/store"
    let evalReg64 (rExpr : Expr) : TacticM Expr := do
      let lhs := mkApp2 (mkConst ``Arm64.State.readReg64) sExpr rExpr
      let (rhs, _) ← g0.withContext <| ProofLib.wpNormSimpLhsExpr lhs
      return rhs
    let addrLhs := mkApp2 (mkConst ``Arm64.evalAddrMode) sExpr amExpr
    let (addrRhs, _) ← g0.withContext <| ProofLib.wpNormSimpLhsExpr addrLhs
    if addrRhs.isAppOfArity ``Prod.mk 4 then
      let ea := addrRhs.getArg! 2
      let (eaNorm, _) ← g0.withContext <| ProofLib.SepSolver.normAddrMeta ea
      return (eaNorm, shape)
    let am ← g0.withContext <| whnf amExpr
    if am.isAppOfArity ``Arm64.AddrMode.Offset 2 ||
       am.isAppOfArity ``Arm64.AddrMode.UnscaledOffset 2 ||
       am.isAppOfArity ``Arm64.AddrMode.PreIndex 2 then
      let baseVal ← evalReg64 (am.getArg! 0)
      let offExpr := am.getArg! 1
      let ea ← g0.withContext <| mkAppM ``HAdd.hAdd #[baseVal, offExpr]
      let (eaNorm, _) ← g0.withContext <| ProofLib.SepSolver.normAddrMeta ea
      return (eaNorm, shape)
    if am.isAppOfArity ``Arm64.AddrMode.PostIndex 2 then
      let baseVal ← evalReg64 (am.getArg! 0)
      let (eaNorm, _) ← g0.withContext <| ProofLib.SepSolver.normAddrMeta baseVal
      return (eaNorm, shape)
    if am.isAppOfArity ``Arm64.AddrMode.RegOffset 4 then
      let baseVal ← evalReg64 (am.getArg! 0)
      let idxVal ← evalReg64 (am.getArg! 1)
      let amtExpr ← g0.withContext <| whnf (am.getArg! 3)
      let scaled ← match amtExpr with
        | .lit (.natVal 0) => pure idxVal
        | _ => g0.withContext <| mkAppM ``HShiftLeft.hShiftLeft #[idxVal, amtExpr]
      let ea ← g0.withContext <| mkAppM ``HAdd.hAdd #[baseVal, scaled]
      let (eaNorm, _) ← g0.withContext <| ProofLib.SepSolver.normAddrMeta ea
      return (eaNorm, shape)
    throwError "no ea"
  restoreState saved
  Core.setMessageLog savedMsgs
  return res?

/-- Create a fresh value mvar for `beta`, eta-expanding `Prod γ₁ γ₂` to `(?v₁, ?v₂)`. -/
def mkFreshLensValMVar (beta : Expr) : MetaM Expr := do
  let bRed ← whnfR beta
  if bRed.isAppOfArity ``Prod 2 then
    let v1 ← mkFreshExprMVar (bRed.getArg! 0)
    let v2 ← mkFreshExprMVar (bRed.getArg! 1)
    mkAppM ``Prod.mk #[v1, v2]
  else
    mkFreshExprMVar beta

/-- Solve a `SepProp` framing equation `Full = Sub ∗ ?Frame` using `sep_focus` / `sep_frame`. -/
def solveSepSplitEq (eqTy : Expr) : TacticM Expr := do
  let gEq ← mkFreshExprMVar eqTy
  let savedGoals ← getGoals
  setGoals [gEq.mvarId!]
  evalTactic (← `(tactic| first | sep_focus | sep_frame))
  setGoals savedGoals
  instantiateMVars gEq

def isPointsTo2Const (e : Expr) : Bool :=
  e.isAppOfArity ``Arm64.pointsTo8 2 ||
  e.isAppOfArity ``Arm64.pointsTo16 2 ||
  e.isAppOfArity ``Arm64.pointsTo32 2 ||
  e.isAppOfArity ``Arm64.pointsTo64 2 ||
  e.isAppOfArity ``Arm64.pointsTo128 2

/-- Solve `restExpr = focusVPrime ∗ ?frameMVar`, automatically aligning equivalent addresses
    via `proveLensAddrEq?` when `wp_step` normalized an instruction address. -/
partial def solveFocusValEq (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (restExpr focusVPrime frameMVar : Expr) : TacticM Expr := do
  let rhs0 := mkApp2 (mkConst ``Arm64.SepProp.sepConj) focusVPrime frameMVar
  let eqTy0 ← mkEq restExpr rhs0
  let saved ← saveState
  if let some prf ← ProofLib.tryTacticCatchRuntime (solveSepSplitEq eqTy0) then
    return prf
  restoreState saved
  let fAtoms := ProofLib.SepSolver.atoms focusVPrime
  let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let rec alignTree (t : Expr) : MetaM (Expr × Expr) := do
    let ts := ProofLib.SepSolver.stripMData t
    if ts.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      let l := ts.getArg! 0
      let r := ts.getArg! 1
      let (l', hl) ← alignTree l
      let (r', hr) ← alignTree r
      if l' == l && r' == r then
        return (t, ← mkEqRefl t)
      let t' := mkApp2 (mkConst ``Arm64.SepProp.sepConj) l' r'
      let h1 ← mkCongrArg (mkConst ``Arm64.SepProp.sepConj) hl
      let ht ← mkCongr h1 hr
      return (t', ← mkExpectedTypeHint ht (← mkEq t t'))
    if isPointsTo2Const ts then
      let ptsFn := ts.getAppFn
      let rAddr := ts.getArg! 0
      let rVal := ts.getArg! 1
      for fa in fAtoms do
        let fas ← instantiateMVars (ProofLib.SepSolver.stripMData fa)
        if isPointsTo2Const fas && fas.getAppFn == ptsFn then
          let fAddr := fas.getArg! 0
          let fVal := fas.getArg! 1
          if fVal.isMVar then
            if let some hAddr ← proveLensAddrEq? ctx cacheRef rAddr fAddr then
              let _ ← isDefEq fVal rVal
              let t' := mkApp2 ptsFn fAddr rVal
              let lam := Expr.lam `a bv64Ty (mkApp2 ptsFn (.bvar 0) rVal) .default
              let ht ← mkExpectedTypeHint (← mkCongrArg lam hAddr) (← mkEq t t')
              return (t', ht)
    return (t, ← mkEqRefl t)
  let (restAligned, hAlign) ← alignTree restExpr
  let focusAssigned ← instantiateMVars focusVPrime
  let rhs1 := mkApp2 (mkConst ``Arm64.SepProp.sepConj) focusAssigned frameMVar
  let hSplit ← solveSepSplitEq (← mkEq restAligned rhs1)
  mkEqTrans hAlign hSplit

/-! ### `D3.A` Adaptive Small-Struct Fast Path (`StructLayout.isSmallFlatScalar`) -/

/-- Recorded state of an in-place unfolded small flat scalar `StructLayout.own L p m` during
    `wp_lens_step` or `wp_lens_auto` (`D3.A` fast path). -/
structure OpenSmallStruct where
  M         : Expr
  L         : Expr
  p         : Expr
  origSnap  : Expr
  fieldCands : Array RawLensCand

/-- Evaluate `StructLayout.own L p m` directly to its flat `↦` / `memRegion` / `emp` cell tree
    (preserving 100% kernel definitional equality with `StructLayout.own L p m`). -/
partial def evalSmallStructOwnCells (_M L p snap : Expr) : MetaM Expr := do
  let totalSzExpr ← mkAppM ``StructLayout.totalSz #[L]
  let some totalSz ← evalClosedNat? totalSzExpr
    | throwError "non-literal totalSz"
  let fieldsExpr ← mkAppM ``StructLayout.fields #[L]
  let flds ← peelListCons fieldsExpr
  let mkGap? (cur off : Nat) : MetaM (Option Expr) := do
    if cur < off then
      let ga ← mkCleanFieldAddr p (mkNatLit cur)
      return some (mkApp2 (mkConst ``Arm64.memRegion) ga (mkNatLit (off - cur)))
    return none
  let rec go (idx cur : Nat) : MetaM Expr := do
    if h : idx < flds.size then
      let fld ← whnfR flds[idx]
      let offExpr := fld.getArg! 1
      let get := fld.getArg! 2
      let some off ← evalClosedNat? offExpr | throwError "non-literal field offset"
      let addr ← mkCleanFieldAddr p offExpr
      let val ← simplifySnapExpr (mkApp get snap)
      let (cell, sz) ←
        if fld.isAppOfArity ``StructField.field8 3 then
          pure (mkApp2 (mkConst ``Arm64.pointsTo8) addr val, 1)
        else if fld.isAppOfArity ``StructField.field16 3 then
          pure (mkApp2 (mkConst ``Arm64.pointsTo16) addr val, 2)
        else if fld.isAppOfArity ``StructField.field32 3 then
          pure (mkApp2 (mkConst ``Arm64.pointsTo32) addr val, 4)
        else if fld.isAppOfArity ``StructField.field64 3 then
          pure (mkApp2 (mkConst ``Arm64.pointsTo64) addr val, 8)
        else if fld.isAppOfArity ``StructField.field128 3 then
          pure (mkApp2 (mkConst ``Arm64.pointsTo128) addr val, 16)
        else
          throwError "not fixed scalar field"
      let withGap := match (← mkGap? cur off) with
        | some g => mkApp2 (mkConst ``Arm64.SepProp.sepConj) g cell
        | none => cell
      let rest ← go (idx + 1) (off + sz)
      return mkApp2 (mkConst ``Arm64.SepProp.sepConj) withGap rest
    else
      if cur < totalSz then
        let ga ← mkCleanFieldAddr p (mkNatLit cur)
        return mkApp2 (mkConst ``Arm64.memRegion) ga (mkNatLit (totalSz - cur))
      else
        return mkConst ``Arm64.SepProp.emp
  go 0 0

/-- If `targetEa` belongs to a small flat scalar `StructLayout.own L p sVal` (`isSmallFlatScalar == true`)
    in the current `SepWP` precondition, unfold it in place via a single definitional `SepWP.congr_pre`
    without creating any `LensOpen` or `SepLensAt` wrapper! -/
def tryUnfoldSmallStructForAddr? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (targetEa : Expr) (shape : LensAccessShape) : TacticM (Option OpenSmallStruct) := do
  let reqW := shape.byteWidth
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``ProofLib.SepWP 6 then return none
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let st := ty.getArg! 2
    let P := ProofLib.SepSolver.stripMData (ty.getArg! 3)
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    for atom in ProofLib.SepSolver.atoms P do
      if !atom.isApp then continue
      let ar ← whnfR atom.appFn!
      if !ar.isAppOfArity ``StructLayout.own 3 then continue
      let M := ar.getArg! 0
      let L := ar.getArg! 1
      let p := ar.getArg! 2
      let sVal := atom.appArg!
      let isSmallExpr := mkApp2 (mkConst ``StructLayout.isSmallFlatScalar) M L
      if !(← whnf isSmallExpr).isConstOf ``Bool.true then continue
      let wholeFn := atom.appFn!
      let (wfOk, cands) ← enumStructLayoutCands wholeFn
      if !wfOk || cands.size != (← peelListCons (← mkAppM ``StructLayout.fields #[L])).size then
        continue
      let mut ownsAddr := false
      for sc in cands do
        if let some (candAddr, candW) ← extractFocusLeaf? sc.beta sc.focusFn then
          if (reqW == 0 || candW == reqW) &&
             (← proveLensAddrEq? ctx cacheRef candAddr targetEa).isSome then
            ownsAddr := true
            break
      if !ownsAddr then continue
      let saved ← saveState
      let ok? ← ProofLib.tryTacticCatchRuntime do
        let expanded ← evalSmallStructOwnCells M L p sVal
        unless ← isDefEq atom expanded do throwError "not defEq"
        let frameMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
        let hfocus ← solveSepSplitEq
          (← mkEq P (mkApp2 (mkConst ``Arm64.SepProp.sepConj) atom frameMVar))
        let frameExpr ← instantiateMVars frameMVar
        let newP := mkApp2 (mkConst ``Arm64.SepProp.sepConj) expanded frameExpr
        let heqSymm ← mkExpectedTypeHint (← mkEqSymm hfocus) (← mkEq newP P)
        let nextGoal ← mkFreshExprMVar (mkAppN (mkConst ``ProofLib.SepWP)
          #[prog, targetPc, st, newP, post, oom])
        let prf := mkAppN (mkConst ``ProofLib.SepWP.congr_pre)
          #[prog, targetPc, st, newP, P, post, oom, heqSymm, nextGoal]
        return (prf, nextGoal.mvarId!)
      match ok? with
      | some (prf, nextId) =>
        g.assign prf
        replaceMainGoal [nextId]
        return some { M, L, p, origSnap := sVal, fieldCands := cands }
      | none =>
        restoreState saved
    return none

/-- Refold an unfolded `OpenSmallStruct` back into `StructLayout.own L p m'` in one `SepWP.congr_pre`
    step (keeping `m' := origSnap` when unchanged via structure eta). -/
def refoldSmallStructInPlace (entry : OpenSmallStruct) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let saved ← saveState
    let ok? ← ProofLib.tryTacticCatchRuntime do
      let ctx ← collectCtxFacts
      let cacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``ProofLib.SepWP 6 then throwError "not SepWP"
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let st := ty.getArg! 2
      let P := ProofLib.SepSolver.stripMData (ty.getArg! 3)
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let mut mvars : Array Expr := #[]
      for sc in entry.fieldCands do
        mvars := mvars.push (← mkFreshExprMVar sc.beta)
      let mut snapMVar := entry.origSnap
      for (sc, mv) in entry.fieldCands.zip mvars do
        snapMVar ← simplifySnapExpr (mkApp2 sc.putFn snapMVar mv)
      let patCells ← evalSmallStructOwnCells entry.M entry.L entry.p snapMVar
      let frameMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
      let hSplit ← solveFocusValEq ctx cacheRef P patCells frameMVar
      let frameExpr ← instantiateMVars frameMVar
      let mut finalSnap ← simplifySnapExpr (← instantiateMVars snapMVar)
      if ← isDefEq finalSnap entry.origSnap then
        finalSnap := entry.origSnap
      let wholeAfter := mkApp3 (mkConst ``StructLayout.own) entry.M entry.L entry.p |> (mkApp · finalSnap)
      let patInst ← instantiateMVars patCells
      unless ← isDefEq wholeAfter patInst do throwError "refold not defEq"
      let newP := mkApp2 (mkConst ``Arm64.SepProp.sepConj) wholeAfter frameExpr
      let heqSymm ← mkExpectedTypeHint (← mkEqSymm hSplit) (← mkEq newP P)
      let nextGoal ← mkFreshExprMVar (mkAppN (mkConst ``ProofLib.SepWP)
        #[prog, targetPc, st, newP, post, oom])
      let prf := mkAppN (mkConst ``ProofLib.SepWP.congr_pre)
        #[prog, targetPc, st, newP, P, post, oom, heqSymm, nextGoal]
      return (prf, nextGoal.mvarId!)
    match ok? with
    | some (prf, nextId) =>
      g.assign prf
      replaceMainGoal [nextId]
      return true
    | none =>
      restoreState saved
      return false

def isLensOpenAtom (e : Expr) : Bool :=
  e.isAppOfArity ``LensOpen 11

/-- Core `lens_open` implementation on `SepWP`. -/
def lensOpenCore (targetEa : Expr) (shape : LensAccessShape) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ctx ← collectCtxFacts
    let cacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``ProofLib.SepWP 6 then
      throwError "lens_open: expected a `SepWP` goal"
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let st := ty.getArg! 2
    let P := ProofLib.SepSolver.stripMData (ty.getArg! 3)
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let atoms := ProofLib.SepSolver.atoms P
    for atom in atoms do
      if isLensOpenAtom atom then continue
      if !atom.isApp then continue
      let wholeFn := atom.appFn!
      let sVal := atom.appArg!
      if let some fl ← synthSepLensAtForWhole? ctx cacheRef wholeFn sVal targetEa shape then
        let alpha ← inferType sVal
        let frameMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
        let wholeAtom := mkApp wholeFn sVal
        let rhsFocus := mkApp2 (mkConst ``Arm64.SepProp.sepConj) wholeAtom frameMVar
        let hfocus ← solveSepSplitEq (← mkEq P rhsFocus)
        let frameExpr ← instantiateMVars frameMVar
        let isLawfulExpr := toExpr fl.isLawful
        let openTok := mkAppN (mkConst ``LensOpen)
          #[alpha, fl.beta, wholeFn, fl.focusFn, fl.holeExpr, sVal, fl.valExpr, fl.putExpr,
            fl.hLensAt, isLawfulExpr, fl.hPutGet]
        let focusCell ← reduceFocusCell (mkApp fl.focusFn fl.valExpr)
        let newP := mkApp2 (mkConst ``Arm64.SepProp.sepConj) focusCell
          (mkApp2 (mkConst ``Arm64.SepProp.sepConj) openTok frameExpr)
        let nextGoal ← mkFreshExprMVar (mkAppN (mkConst ``ProofLib.SepWP)
          #[prog, targetPc, st, newP, post, oom])
        let prf := mkAppN (mkConst ``sepWP_open_lens)
          #[alpha, fl.beta, prog, targetPc, st, P, frameExpr, post, oom,
            wholeFn, fl.focusFn, fl.holeExpr, sVal, fl.valExpr, fl.putExpr,
            isLawfulExpr, fl.hLensAt, fl.hPutGet, hfocus, nextGoal]
        g.assign prf
        replaceMainGoal [nextGoal.mvarId!]
        return
    throwError m!"lens_open: no composite predicate in spine owns address `{targetEa}`"

/-- Compute `(sNext, heqPrf : putExpr vPrime = sNext)` using `hPutGet` when `vPrime` is unchanged,
    or `simplifySnapExpr (putExpr vPrime)` otherwise. -/
def computeUpdatedSnapshot (sVal val0 vPrime putExpr isLawfulExpr hPutGet : Expr) :
    MetaM (Expr × Expr) := do
  if isLawfulExpr.isConstOf ``Bool.true then
    if vPrime == val0 || (← withReducibleAndInstances (isDefEq vPrime val0)) then
      let hvEq ← mkExpectedTypeHint (← mkEqRefl val0) (← mkEq vPrime val0)
      let hCongr ← mkCongrArg putExpr hvEq
      let hPgTyped ← mkExpectedTypeHint hPutGet (← mkEq (mkApp putExpr val0) sVal)
      let hTot ← mkEqTrans hCongr hPgTyped
      return (sVal, hTot)
  let updatedS ← simplifySnapExpr (mkApp putExpr vPrime)
  if ← isDefEq updatedS sVal then
    let hEq ← mkExpectedTypeHint (← mkEqRefl sVal) (← mkEq (mkApp putExpr vPrime) sVal)
    return (sVal, hEq)
  let hEq ← mkExpectedTypeHint (← mkEqRefl updatedS) (← mkEq (mkApp putExpr vPrime) updatedS)
  return (updatedS, hEq)

/-- Core `lens_close` implementation folding one active `LensOpen` token back into `Whole`
    (automatically restoring unchanged `Whole s` via `put_get` when read-only). -/
def lensCloseCore : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ctx ← collectCtxFacts
    let cacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``ProofLib.SepWP 6 then
      throwError "lens_close: expected a `SepWP` goal"
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let st := ty.getArg! 2
    let P := ProofLib.SepSolver.stripMData (ty.getArg! 3)
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let atoms := ProofLib.SepSolver.atoms P
    for atom in atoms do
      if isLensOpenAtom atom then
        let alpha := atom.getArg! 0
        let beta := atom.getArg! 1
        let wholeFn := atom.getArg! 2
        let focusFn := atom.getArg! 3
        let holeExpr := atom.getArg! 4
        let sVal := atom.getArg! 5
        let val0 := atom.getArg! 6
        let putExpr := atom.getArg! 7
        let hL := atom.getArg! 8
        let isLawfulExpr := atom.getArg! 9
        let hpg := atom.getArg! 10
        let restMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
        let hopen ← solveSepSplitEq
          (← mkEq P (mkApp2 (mkConst ``Arm64.SepProp.sepConj) atom restMVar))
        let restExpr ← instantiateMVars restMVar
        let vPrimeMVar ← mkFreshLensValMVar beta
        let frameMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
        let focusVPrime ← reduceFocusCell (mkApp focusFn vPrimeMVar)
        let hval ← solveFocusValEq ctx cacheRef restExpr focusVPrime frameMVar
        let vPrime ← instantiateMVars vPrimeMVar
        let frameExpr ← instantiateMVars frameMVar
        let (updatedS, heqPrf) ←
          computeUpdatedSnapshot sVal val0 vPrime putExpr isLawfulExpr hpg
        let newP := mkApp2 (mkConst ``Arm64.SepProp.sepConj) (mkApp wholeFn updatedS) frameExpr
        let nextGoal ← mkFreshExprMVar (mkAppN (mkConst ``ProofLib.SepWP)
          #[prog, targetPc, st, newP, post, oom])
        let prf := mkAppN (mkConst ``sepWP_close_lens_eq)
          #[alpha, beta, prog, targetPc, st, P, restExpr, frameExpr, post, oom,
            wholeFn, focusFn, holeExpr, sVal, updatedS, val0, vPrime, putExpr, hL,
            isLawfulExpr, hpg, hopen, hval, heqPrf, nextGoal]
        g.assign prf
        replaceMainGoal [nextGoal.mvarId!]
        return
    throwError "lens_close: no active `LensOpen` token found in `SepWP` precondition"

/-- Core `lens_switch` implementation switching an active `LensOpen` to `(targetEa, shape)`. -/
def lensSwitchCore (targetEa : Expr) (shape : LensAccessShape) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ctx ← collectCtxFacts
    let cacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``ProofLib.SepWP 6 then
      throwError "lens_switch: expected a `SepWP` goal"
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let st := ty.getArg! 2
    let P := ProofLib.SepSolver.stripMData (ty.getArg! 3)
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let atoms := ProofLib.SepSolver.atoms P
    for atom in atoms do
      if isLensOpenAtom atom then
        let alpha := atom.getArg! 0
        let beta1 := atom.getArg! 1
        let wholeFn := atom.getArg! 2
        let focus1 := atom.getArg! 3
        let hole1 := atom.getArg! 4
        let sVal := atom.getArg! 5
        let val1 := atom.getArg! 6
        let put1 := atom.getArg! 7
        let hL1 := atom.getArg! 8
        let isLawful1 := atom.getArg! 9
        let hpg1 := atom.getArg! 10
        let saved ← saveState
        let mut innerErr : Option MessageData := none
        let res? ← try
          let restMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
          let hopen ← solveSepSplitEq
            (← mkEq P (mkApp2 (mkConst ``Arm64.SepProp.sepConj) atom restMVar))
          let restExpr ← instantiateMVars restMVar
          let v1PrimeMVar ← mkFreshLensValMVar beta1
          let frameMVar ← mkFreshExprMVar (mkConst ``Arm64.SepProp)
          let focus1VPrime ← reduceFocusCell (mkApp focus1 v1PrimeMVar)
          let hval ← solveFocusValEq ctx cacheRef restExpr focus1VPrime frameMVar
          let v1Prime ← instantiateMVars v1PrimeMVar
          let frameExpr ← instantiateMVars frameMVar
          let (sMid, heqPrf) ←
            computeUpdatedSnapshot sVal val1 v1Prime put1 isLawful1 hpg1
          let some fl2 ← synthSepLensAtForWhole? ctx cacheRef wholeFn sMid targetEa shape
            | throwError m!"no target lens on `{wholeFn}` at `{sMid}` for `{targetEa}`"
          let isLawful2Expr := toExpr fl2.isLawful
          let openTok2 := mkAppN (mkConst ``LensOpen)
            #[alpha, fl2.beta, wholeFn, fl2.focusFn, fl2.holeExpr, sMid, fl2.valExpr, fl2.putExpr,
              fl2.hLensAt, isLawful2Expr, fl2.hPutGet]
          let focusCell2 ← reduceFocusCell (mkApp fl2.focusFn fl2.valExpr)
          let newP := mkApp2 (mkConst ``Arm64.SepProp.sepConj) focusCell2
            (mkApp2 (mkConst ``Arm64.SepProp.sepConj) openTok2 frameExpr)
          let nextGoal ← mkFreshExprMVar (mkAppN (mkConst ``ProofLib.SepWP)
            #[prog, targetPc, st, newP, post, oom])
          let prf := mkAppN (mkConst ``sepWP_switch_lens_eq)
            #[alpha, beta1, fl2.beta, prog, targetPc, st, P, restExpr, frameExpr, post, oom,
              wholeFn, focus1, fl2.focusFn, hole1, fl2.holeExpr, sVal, sMid, val1, v1Prime, put1,
              hL1, isLawful1, hpg1, fl2.valExpr, fl2.putExpr, isLawful2Expr,
              hopen, hval, heqPrf, fl2.hLensAt, fl2.hPutGet, nextGoal]
          pure (some (prf, nextGoal.mvarId!))
        catch ex =>
          innerErr := some ex.toMessageData
          pure none
        match res? with
        | some (prf, nextId) =>
          g.assign prf
          replaceMainGoal [nextId]
          return
        | none =>
          restoreState saved
          if let some ie := innerErr then
            throwError m!"lens_switch failed on `{wholeFn}` for `{targetEa}`: {ie}"
    throwError m!"lens_switch: no active `LensOpen` root owns target address `{targetEa}`"

/-- Step a single instruction with `wp_step`; if `focusCell` holds a `↦₁₂₈` atom and `wp_step`
    needs two `↦₆₄` halves (`ldrSimd`/`strSimd` `.Q128` or `ldp`/`stp`), split via `pointsTo128_split64`
    and merge back via `pointsTo64_pair`. -/
def stepFocusedInstr : TacticM Unit := do
  if ← ProofLib.tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_step))) then
    return
  let s0 ← saveState
  let ok128 ← ProofLib.tryTacticCatchRuntimeBool do
    evalTactic (← `(tactic| (
      rw [_root_.ProofLib.pointsTo128_split64]
      wp_step
      try rw [_root_.ProofLib.pointsTo64_pair]
    )))
  if ok128 then return
  restoreState s0
  evalTactic (← `(tactic| wp_step))

/-- `lens_open` (or `lens_open at addr` / `lens_open at addr width w`): demand-driven opening of
    1-deep or 2-deep composed `SepLens` on a `SepWP` goal. -/
syntax "lens_open" (" at " term)? (" width " num)? : tactic
elab_rules : tactic
  | `(tactic| lens_open $[at $addrStx?]? $[width $wStx?]?) => do
    let wOpt := wStx?.map (·.getNat) |>.getD 0
    match addrStx? with
    | some addrStx =>
      let ea ← elabTerm addrStx (some (mkApp (mkConst ``BitVec) (mkNatLit 64)))
      let (eaNorm, _) ← ProofLib.SepSolver.normAddrMeta ea
      lensOpenCore eaNorm (.anyWidth wOpt)
    | none =>
      let some (ea, shape) ← peekSepWPNextMemAccess?
        | throwError "lens_open: could not infer load/store address at current PC; pass `at <addr>`"
      lensOpenCore ea (if wOpt == 0 then shape else .anyWidth wOpt)

/-- `lens_switch` (or `lens_switch at addr` / `lens_switch at addr width w`): switches active focus
    on an already-open `LensOpen` root to another field, index, or slice offset. -/
syntax "lens_switch" (" at " term)? (" width " num)? : tactic
elab_rules : tactic
  | `(tactic| lens_switch $[at $addrStx?]? $[width $wStx?]?) => do
    let wOpt := wStx?.map (·.getNat) |>.getD 0
    match addrStx? with
    | some addrStx =>
      let ea ← elabTerm addrStx (some (mkApp (mkConst ``BitVec) (mkNatLit 64)))
      let (eaNorm, _) ← ProofLib.SepSolver.normAddrMeta ea
      lensSwitchCore eaNorm (.anyWidth wOpt)
    | none =>
      let some (ea, shape) ← peekSepWPNextMemAccess?
        | throwError "lens_switch: could not infer load/store address at current PC; pass `at <addr>`"
      lensSwitchCore ea (if wOpt == 0 then shape else .anyWidth wOpt)

/-- `lens_close`: folds an active `LensOpen` token and its focus cell back into `Whole`. -/
elab "lens_close" : tactic => lensCloseCore

/-- `wp_lens_step`: demand-driven single-instruction step on `SepWP`. Uses the adaptive small-struct
    fast path (`StructLayout.isSmallFlatScalar`) for `≤ 6`-field scalar structs, and opens/switches
    `LensOpen` spine tokens on demand for large structs, symbolic arrays, slices, and byte maps. -/
elab "wp_lens_step" : tactic => do
  if ← ProofLib.tryTacticCatchRuntimeBool
      (withOptions (fun o => o.set `proofLib.wpAutoSubwordFocus false) <|
        evalTactic (← `(tactic| wp_step))) then
    return
  let some (ea, shape) ← peekSepWPNextMemAccess?
    | throwError "wp_lens_step: `wp_step` failed and next instruction is not a load/store"
  let g ← getMainGoal
  let (ctx, cacheRef) ← g.withContext do
    pure (← collectCtxFacts, ← IO.mkRef ({} : Std.HashMap Expr LinAddr64))
  -- 1. Try adaptive small-struct fast path (`StructLayout.isSmallFlatScalar = true`)
  if let some entry ← tryUnfoldSmallStructForAddr? ctx cacheRef ea shape then
    stepFocusedInstr
    let _ ← refoldSmallStructInPlace entry
    return
  -- 2. Try switching an active `LensOpen` token, else open a new `LensOpen` token
  let mut switchErr? : Option MessageData := none
  let switched ← do
    let s0 ← saveState
    try
      lensSwitchCore ea shape
      pure true
    catch ex =>
      restoreState s0
      switchErr? := some ex.toMessageData
      pure false
  if !switched then
    try
      lensOpenCore ea shape
    catch exOpen =>
      if let some se := switchErr? then
        throwError m!"{exOpen.toMessageData}\n(prior lens_switch attempt: {se})"
      else
        throw exOpen
  stepFocusedInstr

/-- `wp_lens_auto`: automatic open-step-switch-close symbolic execution loop over straight-line
    blocks. Unfolds accessed small flat scalar structs (`StructLayout.isSmallFlatScalar`) once for
    the block, opens/switches `LensOpen` tokens on demand for large structs, arrays, slices, and
    byte maps, re-closes all open lenses at the end of the block, and attempts `wp_done`. -/
elab "wp_lens_auto" : tactic => do
  let mut openSmallStructs : Array OpenSmallStruct := #[]
  for _ in [0:64] do
    if (← getUnsolvedGoals).isEmpty then return
    let (_, targetPc, curPc) ← ProofLib.getSepWPStateAndPC
    if ← withReducibleAndInstances (isDefEq curPc targetPc) then
      break
    if ← ProofLib.tryTacticCatchRuntimeBool
        (withOptions (fun o => o.set `proofLib.wpAutoSubwordFocus false) <|
          evalTactic (← `(tactic| wp_step))) then
      continue
    let some (ea, shape) ← peekSepWPNextMemAccess?
      | throwError "wp_lens_auto: `wp_step` failed and next instruction is not a load/store"
    let g ← getMainGoal
    let (ctx, cacheRef) ← g.withContext do
      pure (← collectCtxFacts, ← IO.mkRef ({} : Std.HashMap Expr LinAddr64))
    if let some entry ← tryUnfoldSmallStructForAddr? ctx cacheRef ea shape then
      openSmallStructs := openSmallStructs.push entry
      stepFocusedInstr
      continue
    let mut switchErr? : Option MessageData := none
    let switched ← do
      let s0 ← saveState
      try
        lensSwitchCore ea shape
        pure true
      catch ex =>
        restoreState s0
        switchErr? := some ex.toMessageData
        pure false
    if !switched then
      try
        lensOpenCore ea shape
      catch exOpen =>
        if let some se := switchErr? then
          throwError m!"{exOpen.toMessageData}\n(prior lens_switch attempt: {se})"
        else
          throw exOpen
    stepFocusedInstr
  for entry in openSmallStructs.reverse do
    let _ ← refoldSmallStructInPlace entry
  for _ in [0:16] do
    if !(← ProofLib.tryTacticCatchRuntimeBool lensCloseCore) then
      break
  let _ ← ProofLib.tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_done)))

end

end ProofLib.Sep
