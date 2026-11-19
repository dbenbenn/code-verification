/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerStage
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.WriterOps

/-!
# Budget-Threaded `format_inner` Stage Lemmas

Proves `subroutine_ok_strengthen_inv` for propagating precondition invariants into panic outcomes,
discharges reachable panic and out-of-memory side conditions under `FitsEnv` and
`FormatInnerBudgetSafe`, and collects stack-frame and `Vec` header helpers for budgeted
`format_inner` stages.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)

/-! ## Consequence Rule for Panic Invariants -/

section Helpers
arm64_proof_prelude

/-- If every satisfying precondition memory yields the pure fact `I x s0`, the panic outcome may
    additionally assert `I x s0`. -/
theorem subroutine_ok_strengthen_inv {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec spec' : Spec α} (I : α → State → Prop)
    (h : subroutine_ok prog entry_pc spec)
    (hinv : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → I x s0)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec'.pre x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec.post x s0 sf ∗ R) → (sf.mem ⊨ spec'.post x s0 sf ∗ R))
    (hpanic : ∀ x R s0 sf, I x s0 → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) →
      (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R))
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) →
      (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R)) :
    subroutine_ok prog entry_pc spec' := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hp hsp_align _ => ?_
  have hp' := hpre x R s0 hp
  have hI := hinv x R s0 hp'
  refine h.mono_outcome x R s0 hpc hrun hp' hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hpanic x R s0 sf hI hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexit x code R s0 sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x R s0 sf hq⟩))

def FmtBufInv (st : FmtBuf) : Prop :=
  st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63

def fmtInnerBudgetPanicInv (t0 : State) (ArgPanic : FmtCall → FmtBuf → State → Prop)
    (c : FmtCall) (st : FmtBuf) (sf : State) : Prop :=
  fmtInnerBudgetPanic t0 ArgPanic c st sf ∧ FmtBufInv st

theorem fmtInnerBudgetW_inv (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs)
    (R : SepProp) (t0 : State) (out : BitVec 64) (st : FmtBuf) (s : State) (F : SepProp)
    {m : Memory} (h : m ⊨ fmtInnerBudgetW A st0 va R t0 out st s ∗ F) : FmtBufInv st := by
  dsimp only [fmtInnerBudgetW, fmtBufVecAt] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  obtain ⟨hio, h⟩ := h
  have h' : m ⊨ ⌜st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63 ∧ st.ptr ≠ 0#64⌝ ∗
      ((vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        (if st.cap = 0#64 then emp
         else A.live st.ptr st.cap.toNat 1 ∗ (st.ptr ↦ₛ st.bytes) ∗
           memRegion (st.ptr + BitVec.ofNat 64 st.bytes.length) (st.cap.toNat - st.bytes.length)) ∗
        A.pool (A.stepEvents st.evs st0) s ∗ stringWriteVtableAt va ∗ R) ∗ F) := by
    revert h; intro h; sep_frame
  rw [satisfies_pure_sepConj] at h'
  exact ⟨h'.1.1, h'.1.2.1⟩

theorem fmtWriteStrCall_inv {P : Program} {wsFn : BitVec 64} (A : RustAllocBudget)
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (Step : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic Oom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (out ptr : BitVec 64) (bs : List (BitVec 8))
    (h : subroutine_ok P wsFn
      (fmtWriteStrCallSpec (fmtInnerBudgetW A st0 va R t0 out) Step
        (fmtInnerBudgetPanic t0 ArgPanic) Oom stackBytes out ptr bs)) :
    subroutine_ok P wsFn
      (fmtWriteStrCallSpec (fmtInnerBudgetW A st0 va R t0 out) Step
        (fmtInnerBudgetPanicInv t0 ArgPanic) Oom stackBytes out ptr bs) := by
  refine subroutine_ok_strengthen_inv (fun st _ => FmtBufInv st) h ?_ (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => hq) ?_ (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · intro st R' s0 hp
    dsimp only [fmtWriteStrCallSpec] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp2 : s0.mem ⊨ fmtInnerBudgetW A st0 va R t0 out st s0 ∗
        ((ptr ↦ᵣ bs) ∗ stackFrameAt s0.sp stackBytes ∗ R') := by
      have := hp.2; revert this; intro this; sep_frame
    exact fmtInnerBudgetW_inv A st0 va R t0 out st s0 _ hp2
  · intro st R' s0 sf hI hq
    dsimp only [fmtWriteStrCallSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1, hI⟩, hq.2⟩

theorem fmtArgCall_inv {P : Program} {fn : BitVec 64} (A : RustAllocBudget)
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (Step : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic Oom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (idx : Nat) (value : BitVec 64) (opts : FmtOptions)
    (h : subroutine_ok P fn
      (fmtArgCallSpec (fmtInnerBudgetW A st0 va R t0 out) Step
        (fmtInnerBudgetPanic t0 ArgPanic) Oom stackBytes out vt idx value fn opts)) :
    subroutine_ok P fn
      (fmtArgCallSpec (fmtInnerBudgetW A st0 va R t0 out) Step
        (fmtInnerBudgetPanicInv t0 ArgPanic) Oom stackBytes out vt idx value fn opts) := by
  refine subroutine_ok_strengthen_inv (fun x _ => FmtBufInv x.1) h ?_ (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => hq) ?_ (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · intro ⟨st, f⟩ R' s0 hp
    dsimp only [fmtArgCallSpec] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp2 : s0.mem ⊨ fmtInnerBudgetW A st0 va R t0 out st s0 ∗
        (formatterAt f out vt opts ∗ stackFrameAt s0.sp stackBytes ∗ R') := by
      have := hp.2; revert this; intro this; sep_frame
    exact fmtInnerBudgetW_inv A st0 va R t0 out st s0 _ hp2
  · intro ⟨st, f⟩ R' s0 sf hI hq
    dsimp only [fmtArgCallSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1, hI⟩, hq.2⟩

end Helpers

/-! ## Refutation of Reachable Panics and Out-of-Memory Outcomes -/

theorem fmtLiteralLen_append (xs ys : List FmtCall) :
    fmtLiteralLen (xs ++ ys) = fmtLiteralLen xs + fmtLiteralLen ys := by
  induction xs with
  | nil => simp [fmtLiteralLen]
  | cons c xs ih =>
    cases c <;> simp only [List.cons_append, fmtLiteralLen, ih] <;> omega

theorem writeStr_len_le_of_reaches {Step : FmtCall → FmtBuf → Bool → FmtBuf → Prop}
    {cs : List FmtCall} {st₀ st : FmtBuf} {p : BitVec 64} {bs : List (BitVec 8)}
    (h : FmtReaches Step cs st₀ (.writeStr p bs) st) : bs.length ≤ fmtLiteralLen cs := by
  obtain ⟨pre, post, rfl, _⟩ := h
  rw [fmtLiteralLen_append]
  simp only [fmtLiteralLen]
  omega

theorem not_stringBufAppendPanics (A : RustAllocBudget) (st0 : A.σ)
    (E : List AllocEvent → Prop) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (x1 : BitVec 64) (cs : List FmtCall)
    (hfit : FitsEnv A st0 E) (hsafe : FormatInnerBudgetSafe A st0 E ArgStep ArgPanic ArgOom x1 cs)
    {st₀ st : FmtBuf} {p : BitVec 64} {bs : List (BitVec 8)} {sf : State}
    (hstart : FmtBufStart (fmtEstimatedCapacity x1 cs) st₀)
    (hreach : FmtReaches (fmtInnerBudgetStep ArgStep) cs st₀ (.writeStr p bs) st)
    (hinv : FmtBufInv st) : ¬ StringBufAppendPanics st bs.length := by
  rintro ⟨hlt, hcase⟩
  have hbs := writeStr_len_le_of_reaches hreach
  have hlit := hsafe.1
  obtain ⟨hlen, hcap⟩ := hinv
  rcases hcase with hov | hnull
  · omega
  · have hoom0 := (hsafe.2.2.2.2 hfit st₀ (.writeStr p bs) st sf hstart hreach).2
    have hoom : A.FitsEvents st0 (stringAppendEvents st bs.length) :=
      Classical.not_not.mp hoom0
    have hnot : ¬ st.bytes.length + bs.length ≤ st.cap.toNat := by omega
    unfold stringAppendEvents at hoom
    simp only [hnot, ↓reduceIte] at hoom
    rw [A.fitsEvents_append] at hoom
    split at hoom
    · exact A.fits_not_nullAllowed_alloc (by decide) hoom.2 hnull
    · exact A.fits_not_nullAllowed_realloc (by decide) hoom.2 hnull

theorem not_fmtInnerBudgetPanicInv (A : RustAllocBudget) (st0 : A.σ)
    (E : List AllocEvent → Prop) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (x1 : BitVec 64) (cs : List FmtCall)
    (t0 : State)
    (hfit : FitsEnv A st0 E) (hsafe : FormatInnerBudgetSafe A st0 E ArgStep ArgPanic ArgOom x1 cs)
    {st₀ st : FmtBuf} {c : FmtCall} {sf : State}
    (hstart : FmtBufStart (fmtEstimatedCapacity x1 cs) st₀)
    (hreach : FmtReaches (fmtInnerBudgetStep ArgStep) cs st₀ c st) :
    ¬ fmtInnerBudgetPanicInv t0 ArgPanic c st sf := by
  rintro ⟨hpan, hinv⟩
  cases c with
  | writeStr p bs =>
    exact not_stringBufAppendPanics A st0 E ArgStep ArgPanic ArgOom x1 cs hfit hsafe
      (sf := sf) hstart hreach hinv hpan.2.2
  | fmtArg idx value fmtFn opts =>
    exact (hsafe.2.2.2.2 hfit st₀ _ st sf hstart hreach).1 idx value fmtFn opts rfl hpan

theorem not_fmtInnerBudgetOom (A : RustAllocBudget) (st0 : A.σ)
    (E : List AllocEvent → Prop) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (x1 : BitVec 64) (cs : List FmtCall)
    (hfit : FitsEnv A st0 E) (hsafe : FormatInnerBudgetSafe A st0 E ArgStep ArgPanic ArgOom x1 cs)
    {st₀ st : FmtBuf} {c : FmtCall} {sf : State}
    (hstart : FmtBufStart (fmtEstimatedCapacity x1 cs) st₀)
    (hreach : FmtReaches (fmtInnerBudgetStep ArgStep) cs st₀ c st) :
    ¬ fmtInnerBudgetOom A st0 ArgOom c st sf :=
  (hsafe.2.2.2.2 hfit st₀ c st sf hstart hreach).2

/-! ## Frame, Stack, and Buffer Helpers -/

namespace FormatInnerBudget

section FrameHelpers
arm64_proof_prelude

theorem cells12_eq (a : BitVec 64) :
    cells a 12 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗
        ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗
        ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) := by
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right]
  simp only [bv_lin_norm]

theorem stackFrameAt96_eq_cells12 (sp : BitVec 64) :
    stackFrameAt sp 96 = cells (sp - 96#64) 12 := by
  rw [← stackAt_eq_stackFrameAt sp 96 (by decide),
    show (96 : Nat) = 8 * 12 from rfl,
    stackAt_eq_cells sp 12 (by decide)]

theorem pts12_entails_stackFrameAt96 (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    let a := sp - 96#64
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
    ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗
    ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗
    ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ⊢
      stackFrameAt sp 96 := by
  dsimp only
  rw [stackFrameAt96_eq_cells12 sp, cells12_eq]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _

theorem fmtCalleeStack_eq_hook (sp1 : BitVec 64) (stackBytes : Nat)
    (hmin : stringWriterStack ≤ stackBytes)
    (hfit : 0x70 + stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp1 (0x70 + stackBytes) =
      (Rust.hookFrame sp1 ∗ stackFrameAt (sp1 - 4096#64) (0x70 + stackBytes - 4096)) := by
  have hge : 4096 ≤ 0x70 + stackBytes := by dsimp only [stringWriterStack] at hmin; omega
  have heq : 0x70 + stackBytes = 4096 + (0x70 + stackBytes - 4096) := by omega
  conv => lhs; rw [heq]
  rw [stackFrameAt_split sp1 4096 (0x70 + stackBytes - 4096) (by omega),
    ← stackAt_eq_stackFrameAt sp1 4096 (by decide)]

theorem vecHeader_def (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) :=
  rfl

theorem rustLayoutOk_one {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) : RustLayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega, by decide⟩

theorem bl_target_eq (base off target : BitVec 64) :
    base + off + (target - base - off) = target := by
  bv_arith

theorem ioCallFrame_trans {s0 s1 s2 : State}
    (h01 : IoCallFrame s0 s1 ∧ s1.fs = s0.fs ∧ s1.trace = s0.trace)
    (h12 : IoCallFrame s1 s2 ∧ s2.fs = s1.fs ∧ s2.trace = s1.trace) :
    IoCallFrame s0 s2 ∧ s2.fs = s0.fs ∧ s2.trace = s0.trace :=
  ⟨⟨h12.1.1.trans h01.1.1, h12.1.2.1.trans h01.1.2.1, h12.1.2.2.1.trans h01.1.2.2.1,
    h12.1.2.2.2.1.trans h01.1.2.2.2.1, h12.1.2.2.2.2.trans h01.1.2.2.2.2⟩,
   h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

theorem ioCallFrame_of_allocCallPreserved {s0 s1 : State}
    (h : AllocCallPreserved s0 s1) :
    IoCallFrame s0 s1 ∧ s1.fs = s0.fs ∧ s1.trace = s0.trace :=
  ⟨⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, h.1, h.2.1⟩

theorem pull_pure_after_two (A1 A2 : SepProp) (P : Prop) (Rest F : SepProp) :
    (A1 ∗ A2 ∗ (⌜P⌝ ∗ Rest)) ∗ F = ⌜P⌝ ∗ ((A1 ∗ A2 ∗ Rest) ∗ F) := by
  rw [← sepConj_assoc A2 ⌜P⌝ Rest, sepConj_comm A2 ⌜P⌝, sepConj_assoc ⌜P⌝ A2 Rest,
    ← sepConj_assoc A1 ⌜P⌝ (A2 ∗ Rest), sepConj_comm A1 ⌜P⌝,
    sepConj_assoc ⌜P⌝ A1 (A2 ∗ Rest), sepConj_assoc ⌜P⌝ _ F]

theorem fmtBufVecAt_empty_alloc (A : RustAllocBudget) {cap0 : Nat} {p : BitVec 64}
    (hpos : 0 < cap0) (hlt : cap0 < 2 ^ 63) (hp0 : p ≠ 0#64) :
    fmtBufVecAt A (BitVec.ofNat 64 cap0) p [] = (A.live p cap0 1 ∗ memRegion p cap0) := by
  unfold fmtBufVecAt
  have hcap_tn : (BitVec.ofNat 64 cap0).toNat = cap0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 cap0 ≠ 0#64 := by bv_omega
  simp only [hcap_ne, ↓reduceIte, hcap_tn, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, pointsToBytes_nil, emp_sepConj]
  rw [pure_sepConj_of_true ⟨Nat.zero_le _, hlt, hp0⟩]

end FrameHelpers

end FormatInnerBudget

end VerifiedLibraries.RustStd
