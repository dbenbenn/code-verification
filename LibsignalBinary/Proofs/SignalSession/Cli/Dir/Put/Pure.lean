/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Pure, memory, stack, epilogue, and callee-bridge helpers for `Dir::put::<String>`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Put.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Layout-independent instruction decodes (`0 .. 288`, 73 instructions) -/

theorem setOrPush_append_of_forall_ne {name bs : List (BitVec 8)}
    {pre suf : List (List (BitVec 8) × List (BitVec 8))}
    (hpre : ∀ e ∈ pre, e.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ suf) = pre ++ DirGhost.setOrPush name bs suf := by
  induction pre with
  | nil => rfl
  | cons e es ih =>
    have he : e.1 ≠ name := hpre e (List.Mem.head _)
    have hes : ∀ x ∈ es, x.1 ≠ name := fun x hx => hpre x (List.Mem.tail _ hx)
    simp only [List.cons_append, DirGhost.setOrPush, he, ↓reduceIte, ih hes]

theorem setOrPush_miss {name bs : List (BitVec 8)}
    {xs : List (List (BitVec 8) × List (BitVec 8))}
    (hxs : ∀ e ∈ xs, e.1 ≠ name) :
    DirGhost.setOrPush name bs xs = xs ++ [(name, bs)] := by
  simpa only [List.append_nil, DirGhost.setOrPush] using
    setOrPush_append_of_forall_ne (name := name) (bs := bs) (pre := xs) (suf := []) hxs

theorem setOrPush_hit {name bs oldBs : List (BitVec 8)}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    (hpre : ∀ e ∈ pre, e.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ (name, oldBs) :: rest) =
      pre ++ (name, bs) :: rest := by
  rw [setOrPush_append_of_forall_ne hpre]
  simp only [DirGhost.setOrPush, ↓reduceIte]

/-! ## 3. Callee-saved / `ImgCallInv` invariant across basic blocks and calls -/

/-- Untouched callee-saved state across `Dir::put::<String>` (`x28`, `v8..v15`, and `StepInv`),
while `x19..x27` and `x29, x30` live in the `0x60`-byte stack frame. -/
@[expose] def PutCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem PutCalleeSaved.refl (s0 : State) : PutCalleeSaved s0 s0 :=
  ⟨rfl, rfl, StepInv.refl s0⟩

theorem PutCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : PutCalleeSaved s0 s1) (h12 : PutCalleeSaved s1 s2) :
    PutCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h01.2.2.trans h12.2.2⟩

theorem PutCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : PutCalleeSaved s1 s2 := by
  rcases hcs with ⟨_, _, _, _, _, _, _, _, _, hx28, _, hv⟩
  exact ⟨hx28, hv, hinv⟩

theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  simp only [CalleeSavedPreserved] at h01 h12 ⊢
  simp_all

theorem PutCalleeSaved.step {s0 s1 s2 : State}
    (h01 : PutCalleeSaved s0 s1)
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    PutCalleeSaved s0 s2 :=
  h01.trans ⟨hx28, hvregs, hinv⟩

/-- Wrap a `Spec α` with `⌜PutCalleeSaved s0 s⌝` so `ImgCallInv img s` propagates automatically. -/
@[expose] def withPutCS {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜PutCalleeSaved s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withPutCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPutCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withPutCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

/-- Raw (pre-`inImage`) `grow_one` specification matching `growOneDirSpec A img growStk`. -/
@[expose] def growOneDirRawSpec (A : RustAlloc) (stk : Nat) : Spec GrowOneDirGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32⌝ ∗
      RustHeap.vecAt A 48 8 (dirEntryAt A) x.v x.cap x.ptr x.xs ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ ptr' : BitVec 64, RustHeap.vecAt A 48 8 (dirEntryAt A) x.v
        (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 4. Layout-independent callee resolution via `ls_rel%` -/

/-- Heap allocation payload of `vecU8At A v cap ptr bs` without its 24-byte header or pure invariant. -/
@[expose] def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_eq_header_rest' (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        vecU8Rest A cap ptr bs := by
  unfold vecU8At vecU8Rest
  ac_rfl

/-- Any state simultaneously owning a 64-bit word `a ↦₆₄ v` and positive `stackAt sp stk`
has `stk < 2 ^ 64`. -/
theorem stk_lt_two_pow_64 {m : Memory} {a v sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hpos : 0 < stk) (hm : m ⊨ (a ↦₆₄ v) ∗ (stackAt sp stk ∗ R)) :
    stk < 2 ^ 64 := by
  have hdisj := (IsBlock.pointsTo64 a v).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) (by decide) hpos hm
  have h2 := hdisj.2
  have hlt := (a - (sp - BitVec.ofNat 64 stk)).isLt
  omega

/-- Split `stackAt sp stk` (`96 ≤ stk ≤ 2 ^ 64`) into `stackAt (sp - 96#64) (stk - 96)` and the
12 saved frame slots of `Dir::put::<String>`. -/
theorem stackAt_put_frame {stk : Nat} (h96 : 0x60 ≤ stk) (hle : stk ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp stk =
      stackAt (sp - 96#64) (stk - 96) ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp (stk - 96) 12 (by omega)
  have heq : (stk - 96) + 8 * 12 = stk := by omega
  rw [heq] at h1
  change stackAt sp stk =
    stackAt (sp - 96#64) (stk - 96) ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

theorem stackAt_sub_split {sub N : Nat} (hsub : sub ≤ N) (hN : N ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp N =
      stackAt sp sub ∗ memRegion (sp - BitVec.ofNat 64 N) (N - sub) := by
  have hsum : (N - sub) + sub = N := by omega
  have hsplit := ProofLib.memRegion_split (sp - BitVec.ofNat 64 N) (N - sub) sub (by omega)
  have hadj : sp - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - sub) = sp - BitVec.ofNat 64 sub := by
    have hN_eq : BitVec.ofNat 64 N = BitVec.ofNat 64 sub + BitVec.ofNat 64 (N - sub) := by
      rw [← BitVec.ofNat_add]; congr 1; omega
    rw [hN_eq, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [hsum, hadj, sepConj_comm] at hsplit
  exact hsplit

theorem sp_sub_96_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 96#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem pointsTo64_pair_eq_128 (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by
    ext i hi
    simp
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by
    ext i hi
    simp
  rw [h0, h1]

theorem vecHeader_eq_q128 (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = (v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ len) := by
  unfold vecHeader
  rw [← sepConj_assoc, pointsTo64_pair_eq_128 v cap ptr]

theorem q128_word_entails_memRegion_24 (v : BitVec 64) (q : BitVec 128) (w : BitVec 64) :
    ((v ↦₁₂₈ q) ∗ ((v + 16#64) ↦₆₄ w)) ⊢ memRegion v 24 := by
  unfold pointsTo128
  rw [sepConj_assoc]
  exact vecHeader_entails_memRegion v (q.extractLsb' 0 64) (q.extractLsb' 64 64) w

theorem vecU8At_eq_q128_rest (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Rest A cap ptr bs := by
  rw [vecU8At_eq_header_rest' A v cap ptr bs, vecHeader_eq_q128, sepConj_assoc]

theorem vecU8_of_vecU8At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecU8_intro_header_rest {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Rest A cap ptr bs) ⊢ vecU8 A v bs := by
  refine Entails.trans ?_ (vecU8_of_vecU8At A v cap ptr bs)
  rw [vecU8At_eq_header_rest' A v cap ptr bs, pure_sepConj_of_true ⟨hle, hlt, hptr⟩]
  exact Entails.refl _

theorem vecU8_intro_q128_rest {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Rest A cap ptr bs) ⊢ vecU8 A v bs := by
  rw [← sepConj_assoc, ← vecHeader_eq_q128 v cap ptr (BitVec.ofNat 64 bs.length)]
  exact vecU8_intro_header_rest hle hlt hptr

theorem dirAt_of_vecAt (A : RustAlloc) (d cap ptr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) (path : List (BitVec 8)) :
    (RustHeap.vecAt A 48 8 (dirEntryAt A) d cap ptr xs ∗ strRefAt (d + 0x18#64) path) ⊢
      dirAt A d { changed := xs, path := path } :=
  sepConj_mono_left
    (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))

/-- Convert a non-empty-capacity `vecU8Rest` heap allocation into the exact deallocator input
`A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat` together with `LayoutOk cap.toNat 1`. -/
theorem vecU8Rest_dealloc {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hcap0 : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 ∧
      (vecU8Rest A cap ptr bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  have hpos : 0 < cap.toNat := by
    by_contra h0
    apply hcap0
    apply BitVec.eq_of_toNat_eq
    change cap.toNat = 0
    omega
  refine ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
  simp only [vecU8Rest, hcap0, ↓reduceIte]
  have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
  rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
  rw [hsplit]
  exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))

/-- Expose `(ptr ↦ₛ bs)` out of `vecU8Rest` for any `cap` (including `cap = 0` when `bs = []`). -/
theorem vecU8Rest_expose_bytes {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) :
    vecU8Rest A cap ptr bs =
      (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [vecU8Rest, ↓reduceIte, pointsToBytes_nil, emp_sepConj]
  · simp only [vecU8Rest, hcap, ↓reduceIte]
    ac_rfl

/-- Split a 48-byte uninitialized slot into the exact cells written by `step_miss` (`+232..+244`). -/
theorem memRegion_48_split_entry (p : BitVec 64) :
    memRegion p 48 =
      (∃∗ l1 : BitVec 64, ∃∗ q1 : BitVec 128, ∃∗ l0 : BitVec 64,
       ∃∗ p0 : BitVec 64, ∃∗ c0 : BitVec 64,
        (p ↦₆₄ c0) ∗ ((p + 8#64) ↦₆₄ p0) ∗ ((p + 16#64) ↦₆₄ l0) ∗
        ((p + 24#64) ↦₁₂₈ q1) ∗ ((p + 40#64) ↦₆₄ l1)) := by
  have hs1 := ProofLib.memRegion_split p 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split (p + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (p + 8#64 + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split (p + 8#64 + 8#64 + 8#64) 16 8 (by decide)
  change memRegion p 48 = memRegion p 8 ∗ memRegion (p + 8#64) 40 at hs1
  change memRegion (p + 8#64) 40 = memRegion (p + 8#64) 8 ∗ memRegion (p + 8#64 + 8#64) 32 at hs2
  change memRegion (p + 8#64 + 8#64) 32 =
    memRegion (p + 8#64 + 8#64) 8 ∗ memRegion (p + 8#64 + 8#64 + 8#64) 24 at hs3
  change memRegion (p + 8#64 + 8#64 + 8#64) 24 =
    memRegion (p + 8#64 + 8#64 + 8#64) 16 ∗ memRegion (p + 8#64 + 8#64 + 8#64 + 16#64) 8 at hs4
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_arith
  rw [hs1, hs2, hs3, hs4, h16, h24, h40,
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64), ProofLib.memRegion_sixteen (p + 24#64),
      ProofLib.memRegion_eight (p + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

/-! ## 6. Saved-frame bundle and reusable `SepWPp` combinators -/

/-- Saved callee-saved registers in `Dir::put::<String>`'s `0x60`-byte stack frame. -/
@[expose] def putSavedCells (s0 : State) (v3 : BitVec 64) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ v3) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem putSavedCells_pack {stk : Nat} (h96 : 0x60 ≤ stk) (hle : stk ≤ 2 ^ 64)
    (s0 : State) (v3 : BitVec 64) :
    stackAt (s0.sp - 96#64) (stk - 96) ∗ putSavedCells s0 v3 ⊢ stackAt s0.sp stk := by
  rw [stackAt_put_frame h96 hle s0.sp, putSavedCells]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _))))))))))))

private abbrev stepDst {a b : State} (_ : StepInv a b) : State := b

end CryptoVerification.SignalSession.Cli.Put.Helpers
