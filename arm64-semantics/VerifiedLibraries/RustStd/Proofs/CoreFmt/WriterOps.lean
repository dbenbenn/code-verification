/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.CoreFmtSym

/-!
# Writer-Operation and Budget-Event Lemmas

Composition lemmas for `FmtOpsRun` and `FmtOpsAbort`, default `FmtOptions` identities,
`VmPreserved`/`FmtWriteFrame` transport, and `RustAllocBudget` event-log composition.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)
open VerifiedLibraries.RustStd.CoreFmt (PureSegPreserved)

/-! ## `FmtOpsRun` and `FmtOpsAbort` Composition -/

namespace FmtOpsRun

variable {σ : Type} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
  {CharStep : σ → BitVec 32 → Bool → σ → Prop}

theorem append_ok {ops₁ ops₂ : List FmtOp} {st st' st'' : σ} {b : Bool}
    (h₁ : FmtOpsRun StrStep CharStep ops₁ st true st')
    (h₂ : FmtOpsRun StrStep CharStep ops₂ st' b st'') :
    FmtOpsRun StrStep CharStep (ops₁ ++ ops₂) st b st'' := by
  generalize hb : true = b₁ at h₁
  induction h₁ with
  | nil => exact h₂
  | str_ok hs _ ih => exact .str_ok hs (ih h₂ hb)
  | str_err => cases hb
  | char_ok hc _ ih => exact .char_ok hc (ih h₂ hb)
  | char_err => cases hb

theorem append_err {ops₁ : List FmtOp} (ops₂ : List FmtOp) {st st' : σ}
    (h₁ : FmtOpsRun StrStep CharStep ops₁ st false st') :
    FmtOpsRun StrStep CharStep (ops₁ ++ ops₂) st false st' := by
  generalize hb : false = b₁ at h₁
  induction h₁ with
  | nil => cases hb
  | str_ok hs _ ih => exact .str_ok hs (ih hb)
  | str_err hs => exact .str_err hs
  | char_ok hc _ ih => exact .char_ok hc (ih hb)
  | char_err hc => exact .char_err hc

theorem single_str {bs : List (BitVec 8)} {st st' : σ} {ok : Bool}
    (h : StrStep st bs ok st') : FmtOpsRun StrStep CharStep [.str bs] st ok st' := by
  cases ok
  · exact .str_err h
  · exact .str_ok h (.nil _)

theorem single_char {c : BitVec 32} {st st' : σ} {ok : Bool}
    (h : CharStep st c ok st') : FmtOpsRun StrStep CharStep [.char c] st ok st' := by
  cases ok
  · exact .char_err h
  · exact .char_ok h (.nil _)

theorem snoc {ops₁ : List FmtOp} {op : FmtOp} {st st' st'' : σ} {b : Bool}
    (h₁ : FmtOpsRun StrStep CharStep ops₁ st true st')
    (h₂ : FmtOpsRun StrStep CharStep [op] st' b st'') :
    FmtOpsRun StrStep CharStep (ops₁ ++ [op]) st b st'' :=
  append_ok h₁ h₂

end FmtOpsRun

abbrev fmtFill (n : Nat) (c : BitVec 32) : List FmtOp := List.replicate n (.char c)

theorem fmtFill_succ (n : Nat) (c : BitVec 32) :
    fmtFill (n + 1) c = fmtFill n c ++ [.char c] := by
  simp [fmtFill, List.replicate_succ']

namespace FmtOpsAbort

variable {σ : Type} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
  {CharStep : σ → BitVec 32 → Bool → σ → Prop}
  {Abort : σ → Nat → State → Prop}

theorem of_head {op : FmtOp} {ops : List FmtOp} {st : σ} {sf : State}
    (h : Abort st op.byteLen sf) :
    FmtOpsAbort StrStep CharStep Abort (op :: ops) st sf :=
  ⟨[], op, ops, st, rfl, .nil st, h⟩

theorem single_str {bs : List (BitVec 8)} {st : σ} {sf : State}
    (h : Abort st bs.length sf) :
    FmtOpsAbort StrStep CharStep Abort [.str bs] st sf :=
  of_head (op := .str bs) (ops := []) h

theorem single_char {c : BitVec 32} {st : σ} {sf : State}
    (h : Abort st (charUtf8Len c) sf) :
    FmtOpsAbort StrStep CharStep Abort [.char c] st sf :=
  of_head (op := .char c) (ops := []) h

theorem of_left {ops₁ : List FmtOp} (ops₂ : List FmtOp) {st : σ} {sf : State}
    (h : FmtOpsAbort StrStep CharStep Abort ops₁ st sf) :
    FmtOpsAbort StrStep CharStep Abort (ops₁ ++ ops₂) st sf := by
  rcases h with ⟨pre, op, post, st_i, heq, hrun, habort⟩
  refine ⟨pre, op, post ++ ops₂, st_i, ?_, hrun, habort⟩
  simp [heq, List.append_assoc]

theorem of_right {ops₁ ops₂ : List FmtOp} {st st' : σ} {sf : State}
    (h₁ : FmtOpsRun StrStep CharStep ops₁ st true st')
    (h₂ : FmtOpsAbort StrStep CharStep Abort ops₂ st' sf) :
    FmtOpsAbort StrStep CharStep Abort (ops₁ ++ ops₂) st sf := by
  rcases h₂ with ⟨pre, op, post, st_i, heq, hrun, habort⟩
  refine ⟨ops₁ ++ pre, op, post, st_i, ?_, FmtOpsRun.append_ok h₁ hrun, habort⟩
  simp [heq, List.append_assoc]

theorem of_cons_str_ok {bs : List (BitVec 8)} {ops : List FmtOp} {st st' : σ} {sf : State}
    (hs : StrStep st bs true st')
    (h : FmtOpsAbort StrStep CharStep Abort ops st' sf) :
    FmtOpsAbort StrStep CharStep Abort (.str bs :: ops) st sf :=
  of_right (ops₁ := [.str bs]) (FmtOpsRun.single_str hs) h

theorem of_cons_char_ok {c : BitVec 32} {ops : List FmtOp} {st st' : σ} {sf : State}
    (hc : CharStep st c true st')
    (h : FmtOpsAbort StrStep CharStep Abort ops st' sf) :
    FmtOpsAbort StrStep CharStep Abort (.char c :: ops) st sf :=
  of_right (ops₁ := [.char c]) (FmtOpsRun.single_char hc) h

end FmtOpsAbort

/-! ## Default Formatting Option Identities -/

theorem fmtPadFastOpts_default : FmtPadFastOpts defaultFmtOptions := by
  unfold FmtPadFastOpts; decide

theorem defaultFmtOptions_noAlt : defaultFmtOptions.flags.getLsbD 23 = false := by
  decide

theorem padIntegralNoAltOps_default (ds : List (BitVec 8)) :
    padIntegralNoAltOps defaultFmtOptions true ds = [.str ds] := by
  have h21 : defaultFmtOptions.flags[21] = false := by decide
  have h24 : defaultFmtOptions.flags[24] = false := by decide
  have hw : defaultFmtOptions.width.toNat = 0 := by decide
  have hsh : defaultFmtOptions.flags.toNat / 536870912 % 4 = 3 := by decide
  simp [padIntegralNoAltOps, fmtSignOp, fmtPadSplit, h21, h24, hw, hsh]

/-! ## `VmPreserved` and `FmtWriteFrame` Transport -/

theorem VmPreserved.refl (s : State) : VmPreserved s s :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩

theorem VmPreserved.trans {s0 s1 s2 : State}
    (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) : VmPreserved s0 s2 :=
  ⟨⟨h12.1.1.trans h01.1.1, h12.1.2.1.trans h01.1.2.1, h12.1.2.2.trans h01.1.2.2⟩,
   h12.2.1.trans h01.2.1,
   fun a => (h12.2.2 a).trans (h01.2.2 a)⟩

theorem VmPreserved.of_fmtWriteFrame {s s' : State} (h : FmtWriteFrame s s') :
    VmPreserved s s' := by
  rcases h with ⟨_, _, _, htpidr, hbrk, hbrkS, hphys, _, _, _, hperm⟩
  exact ⟨⟨hbrkS, hbrk, htpidr⟩, hphys, hperm⟩

theorem fmtWriteFrame_of_pureSeg {s sm : State}
    (hp : PureSegPreserved s sm)
    (hsig : sm.sigActions = s.sigActions)
    (htp : sm.tpidrEl0 = s.tpidrEl0) :
    FmtWriteFrame s sm := by
  rcases hp with ⟨⟨htrace, hperm, hbrk, hbrkS, hphys, ⟨hoidx, _⟩, hfs⟩, horacle, hsym⟩
  exact ⟨htrace, hfs, hsig, htp, hbrk, hbrkS, hphys, horacle, hoidx, hsym,
    fun a => congrFun hperm a⟩

/-! ## `RustAllocBudget` Event-Log Algebra and Pool Transport -/

namespace RustAllocBudget

@[simp] theorem stepEvents_nil (A : RustAllocBudget) (st : A.σ) :
    A.stepEvents [] st = st := rfl

@[simp] theorem stepEvents_cons (A : RustAllocBudget) (ev : AllocEvent)
    (evs : List AllocEvent) (st : A.σ) :
    A.stepEvents (ev :: evs) st = A.stepEvents evs (A.step ev st) := rfl

theorem stepEvents_append (A : RustAllocBudget) (evs₁ evs₂ : List AllocEvent) (st : A.σ) :
    A.stepEvents (evs₁ ++ evs₂) st = A.stepEvents evs₂ (A.stepEvents evs₁ st) := by
  induction evs₁ generalizing st with
  | nil => rfl
  | cons ev evs₁ ih => exact ih (A.step ev st)

@[simp] theorem fitsEvents_nil (A : RustAllocBudget) (st : A.σ) :
    A.FitsEvents st [] ↔ True := Iff.rfl

@[simp] theorem fitsEvents_cons (A : RustAllocBudget) (st : A.σ) (ev : AllocEvent)
    (evs : List AllocEvent) :
    A.FitsEvents st (ev :: evs) ↔ A.FitsEvent st ev ∧ A.FitsEvents (A.step ev st) evs :=
  Iff.rfl

theorem fitsEvents_append (A : RustAllocBudget) (st : A.σ) (evs₁ evs₂ : List AllocEvent) :
    A.FitsEvents st (evs₁ ++ evs₂) ↔
      A.FitsEvents st evs₁ ∧ A.FitsEvents (A.stepEvents evs₁ st) evs₂ := by
  induction evs₁ generalizing st with
  | nil => simp [FitsEvents, stepEvents]
  | cons ev evs₁ ih =>
    simp only [List.cons_append, FitsEvents, stepEvents, ih, and_assoc]

theorem fitsEvents_of_prefix_env (A : RustAllocBudget) {st0 : A.σ}
    {E : List AllocEvent → Prop} {evs : List AllocEvent}
    (hfit : FitsEnv A st0 E) (hpfx : ∃ suf, E (evs ++ suf)) :
    A.FitsEvents st0 evs := by
  rcases hpfx with ⟨suf, hE⟩
  exact ((A.fitsEvents_append st0 evs suf).mp (hfit _ hE)).1

theorem fitsEvents_ext_of_prefix_env (A : RustAllocBudget) {st0 : A.σ}
    {E : List AllocEvent → Prop} {evs δ : List AllocEvent}
    (hfit : FitsEnv A st0 E) (hpfx : ∃ suf, E ((evs ++ δ) ++ suf)) :
    A.FitsEvents (A.stepEvents evs st0) δ := by
  have h12 : A.FitsEvents st0 (evs ++ δ) := A.fitsEvents_of_prefix_env hfit hpfx
  exact ((A.fitsEvents_append st0 evs δ).mp h12).2

theorem pool_of_fmtWriteFrame (A : RustAllocBudget) (st : A.σ) {s s' : State}
    (h : FmtWriteFrame s s') : A.pool st s' = A.pool st s :=
  A.pool_transport st s s' (VmPreserved.of_fmtWriteFrame h)

theorem pool_of_pureSeg (A : RustAllocBudget) (st : A.σ) {s sm : State}
    (hp : PureSegPreserved s sm)
    (hsig : sm.sigActions = s.sigActions)
    (htp : sm.tpidrEl0 = s.tpidrEl0) :
    A.pool st sm = A.pool st s :=
  A.pool_of_fmtWriteFrame st (fmtWriteFrame_of_pureSeg hp hsig htp)

theorem fits_not_nullAllowed_alloc (A : RustAllocBudget) {st : A.σ} {size align : Nat}
    (hal : align ≤ 2 ^ 31) (hfit : A.FitsEvents st (rustAllocEvents size align)) :
    ¬ NullAllowed size align := by
  unfold rustAllocEvents at hfit
  split at hfit
  · exact A.fits_not_nullAllowed st size align hal (Or.inl hfit.1)
  · exact A.fits_not_nullAllowed st size align hal (Or.inr (Or.inl hfit.1))

theorem fits_not_nullAllowed_realloc (A : RustAllocBudget) {st : A.σ} {old new align : Nat}
    (hal : align ≤ 2 ^ 31) (hfit : A.FitsEvents st (rustReallocEvents old new align)) :
    ¬ NullAllowed new align := by
  unfold rustReallocEvents at hfit
  split at hfit
  · exact A.fits_not_nullAllowed st new align hal (Or.inr (Or.inr ⟨old, hfit.1⟩))
  · exact A.fits_not_nullAllowed st new align hal (Or.inr (Or.inl hfit.1))

end RustAllocBudget

theorem fmtBufVecAt_zero_eq_emp (A : RustAllocBudget) {ptr : BitVec 64} (hne : ptr ≠ 0#64) :
    fmtBufVecAt A 0#64 ptr [] = emp := by
  unfold fmtBufVecAt
  have hp : (([] : List (BitVec 8)).length ≤ (0#64).toNat ∧
      (0#64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨by decide, by decide, hne⟩⟩
  simp only [hp, ↓reduceIte, pure_true, emp_sepConj]

end VerifiedLibraries.RustStd
