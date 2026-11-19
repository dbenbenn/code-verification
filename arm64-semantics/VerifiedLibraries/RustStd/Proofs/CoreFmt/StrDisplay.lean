/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.CoreFmtSym
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.WriterOps

/-!
# `Formatter::write_str`, `Formatter::pad`, and `str` / `&str` / `String` `Display` Proofs

Placement-generic correctness proofs over `Spec.CoreFmtDisplay` and `Spec.CoreFmtWrite` for
`<Formatter>::write_str` (`formatterWriteStr_ok`), `<Formatter>::pad` on the `FmtPadFastOpts` fast
path (`formatterPad_ok`), `<str as Display>::fmt` (`strDisplayFmt_ok`), `<&str as Display>::fmt`
(`strRefDisplayFmt_ok`), crate-local 20-byte `<&str as Display>::fmt` and `<String as Display>::fmt`
shims (`strRefDisplayShim_ok`, `stringDisplayShim_ok`), and `fmtArgCallSpec` callback lifting
(`strRefDisplayFmt_fmtArg_ok`, `stringDisplayFmt_fmtArg_ok`).
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.RustStd.CoreFmt

/-- Extract `(vt + 0x18#64) ↦₆₄ᵣ wsFn` from `FmtWriterOk.slots`. -/
theorem FmtWriterOk.slot_write_str {σ : Type} {P : Program} {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (st : σ) (s : State) :
    W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s := by
  conv => rhs; arg 2; rw [hw.slots st s]
  rw [← sepConj_assoc, pointsTo64RO_dup]
  exact hw.slots st s

/-! ## Internal frame and stack-bound helpers -/

private theorem satisfies_of_eq {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem panic_frame_anyHeap {φ : Prop} {F : SepProp} :
    ((⌜φ⌝ ∗ anyHeap) ∗ F) ⊢ ⌜φ⌝ ∗ anyHeap := by
  rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _)

private theorem ownsRW_formatterAt (f out vt : BitVec 64) (opts : FmtOptions) :
    OwnsRW (formatterAt f out vt opts) f := by
  unfold formatterAt
  exact ownsRW_sepConj_left (ownsRW_pointsTo64_at f out f (by simp [InRegion]))

private theorem stackFrameSlotsCont_pull (sp : BitVec 64) (k m : Nat) :
    ∀ (X : SepProp) (cont : SepProp → SepProp),
      stackFrameSlotsCont sp k m (fun rest => X ∗ cont rest) =
        X ∗ stackFrameSlotsCont sp k m cont := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro X cont
    cases m with
    | zero => simp only [stackFrameSlotsCont]; exact (sepExists_sepConj_right X _).symm
    | succ m' =>
      simp only [stackFrameSlotsCont]
      have h := fun v : BitVec 64 =>
        ih X (fun rest => cont (((sp - BitVec.ofNat 64 ((k + m' + 2) * 8)) ↦₆₄ v) ∗ rest))
      simp only [h]; exact (sepExists_sepConj_right X _).symm

private theorem stackFrameSlotsFrom_succ_pos (sp : BitVec 64) {m : Nat} (hm : 0 < m) :
    stackFrameSlotsFrom sp 0 (m + 1) =
      (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 ((m + 1) * 8)) ↦₆₄ v) ∗
        stackFrameSlotsFrom sp 0 m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold stackFrameSlotsFrom
  simp only [stackFrameSlotsCont, Nat.zero_add]
  rw [funext fun v => stackFrameSlotsCont_pull sp 0 (d + 1)
    ((sp - BitVec.ofNat 64 ((d + 2) * 8)) ↦₆₄ v) (fun P => P)]
  exact (sepExists_sepConj_left _ _).symm

private theorem satisfies_drop_slotsFrom {m : Memory} {Q R : SepProp} (sp : BitVec 64)
    (extra : Nat) :
    (m ⊨ Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61 + extra) ∗ R)) →
    (m ⊨ Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61) ∗ R)) := by
  induction extra with
  | zero => exact id
  | succ extra ih =>
    intro h
    rw [show 2 ^ 61 + (extra + 1) = (2 ^ 61 + extra) + 1 by omega,
        stackFrameSlotsFrom_succ_pos sp (by omega)] at h
    have h' : m ⊨ (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 (((2 ^ 61 + extra) + 1) * 8)) ↦₆₄ v) ∗
        (Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61 + extra) ∗ R)) :=
      satisfies_of_eq (by ac_rfl) h
    exact ih (Satisfies.drop_left h')

private theorem le_pow64_of_formatterAt_stackFrameAt {m : Memory}
    {f out vt sp : BitVec 64} {opts : FmtOptions} {n : Nat} {R : SepProp}
    (hm : m ⊨ formatterAt f out vt opts ∗ (stackFrameAt sp n ∗ R)) : n ≤ 2 ^ 64 := by
  apply Classical.byContradiction; intro hgt
  have hlt : 2 ^ 64 < n := Nat.lt_of_not_ge hgt
  have hne0 : (n == 0) = false := beq_false_of_ne (by omega)
  by_cases h8 : n % 8 = 0
  · rw [show stackFrameAt sp n = stackFrameSlotsFrom sp 0 (n / 8) by simp [stackFrameAt, hne0, h8],
        show n / 8 = 2 ^ 61 + (n / 8 - 2 ^ 61) by omega] at hm
    have hm64 := satisfies_drop_slotsFrom sp (n / 8 - 2 ^ 61) hm
    have h64 : stackFrameSlotsFrom sp 0 (2 ^ 61) = memRegion (sp - BitVec.ofNat 64 (2 ^ 64)) (2 ^ 64) := by
      have heq := stackFrameAt_eq_memRegion sp (2 ^ 64) (by decide)
      simpa [stackFrameAt] using heq
    rw [h64] at hm64
    exact not_satisfies_ownsRW_ownsRW (ownsRW_formatterAt f out vt opts)
      (ownsRW_sepConj_left (ownsRW_memRegion _ (2 ^ 64) f (BitVec.isLt _))) hm64
  · rw [show stackFrameAt sp n = memRegion (sp - BitVec.ofNat 64 n) n by
        simp [stackFrameAt, hne0, h8]] at hm
    exact not_satisfies_ownsRW_ownsRW (ownsRW_formatterAt f out vt opts)
      (ownsRW_sepConj_left (ownsRW_memRegion _ n f (Nat.lt_trans (BitVec.isLt _) hlt))) hm

private theorem formatterAt_entails_memRegion24_local (f outPtr vtPtr : BitVec 64)
    (opts : FmtOptions) : formatterAt f outPtr vtPtr opts ⊢ memRegion f 24 := by
  unfold formatterAt
  have h16 := (show f + 20#64 + 2#64 = f + 22#64 by bv_omega) ▸
    pointsTo16_pair (f + 20#64) opts.width opts.precision
  have h32 := (show f + 16#64 + 4#64 = f + 20#64 by bv_omega) ▸
    pointsTo32_pair (f + 16#64) opts.flags (opts.precision ++ opts.width)
  rw [h16, h32, memRegion_cells f 3 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, show f + 8#64 + 8#64 = f + 16#64 by bv_omega]
  exact Entails.sepExists_right outPtr (Entails.sepExists_right vtPtr
    (Entails.sepExists_right ((opts.precision ++ opts.width) ++ opts.flags) (Entails.refl _)))

/-- Discharge `lib.withCodeLoadedWhere keep mpl` when `P.CodeLoaded` implies `CodeLoadedWhere`. -/
theorem subroutine_ok_drop_codeLoadedWhere {α : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hload : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoadedWhere keep mpl m)
    (hok : subroutine_ok P entry (lib.withCodeLoadedWhere keep mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hcode
  have hpre' : s0.mem ⊨ (lib.withCodeLoadedWhere keep mpl spec).pre x s0 ∗ R := by
    show s0.mem ⊨ (spec.pre x s0 ∗ ⌜lib.CodeLoadedWhere keep mpl s0.mem⌝) ∗ R
    rwa [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true (hload s0.mem hcode)]
  exact (hok.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

private theorem padCells_sub_one_entails {sp : BitVec 64} (a : Nat) {v : BitVec 64}
    (ha : 8 ≤ a := by decide) :
    ((sp - BitVec.ofNat 64 a) ↦₆₄ v) ⊢ cells (sp - BitVec.ofNat 64 a) 1 := by
  simpa only [sepConj_emp] using cells_sub_succ_entails a 1 (Entails.refl emp) (by decide) ha

private theorem padStack_recombine (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64)
    (stackBytes : Nat) (hmax_le : max 80 stackBytes ≤ 2 ^ 64) :
    ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
      ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
      ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
      ((sp - 8#64) ↦₆₄ v9) ∗ stackFrameAt (sp - 80#64) (max 80 stackBytes - 80) ⊢
    stackFrameAt sp stackBytes ∗
      stackFrameAt (sp - BitVec.ofNat 64 stackBytes) (max 80 stackBytes - stackBytes) := by
  let slots80 := ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
    ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
    ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)
  have hfold : slots80 ⊢ stackFrameAt sp 80 := by
    dsimp only [slots80]
    rw [← stackAt_eq_stackFrameAt sp 80, stackAt_eq_cells sp 10]; simp only [Nat.reduceMul]
    iterate 9 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
    exact padCells_sub_one_entails 8
  refine Entails.trans (entails_of_eq (show _ =
    slots80 ∗ stackFrameAt (sp - 80#64) (max 80 stackBytes - 80) by dsimp only [slots80]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hfold) (entails_of_eq ?_)
  rw [← stackFrameAt_split sp 80 (max 80 stackBytes - 80) (by omega),
      show 80 + (max 80 stackBytes - 80) = stackBytes + (max 80 stackBytes - stackBytes) by omega,
      stackFrameAt_split sp stackBytes (max 80 stackBytes - stackBytes) (by omega)]

private theorem tailcall_ws_with_frame {σ : Type} {P : Program}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes totalStack : Nat}
    {f out vt wsFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {F_stk : SepProp} {st : σ} {R : SepProp} {s0 sm : State}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs))
    (hstk : stackFrameAt s0.sp stackBytes ∗ F_stk = stackFrameAt s0.sp totalStack)
    (hframe : FmtWriteFrame s0 sm) (hpc_sm : sm.pc = wsFn) (hrun_sm : sm.status = .Running)
    (hsp_sm : sm.sp = s0.sp) (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hx0_sm : sm.readReg64 .x0 = out) (hx1_sm : sm.readReg64 .x1 = ptr)
    (hx2_sm : (sm.readReg64 .x2).toNat = bs.length) (hlen_lt : bs.length < 2 ^ 60)
    (hcs_sm : CalleeSavedPreserved s0 sm) :
    SepWPp P (s0.readReg64 Reg.lr) sm
      ((stackFrameAt s0.sp stackBytes ∗ F_stk) ∗
        (W st s0 ∗ fmtSrcBytes ro ptr bs ∗ formatterAt f out vt opts ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn)))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (∃∗ ok : Bool, ∃∗ st' : σ,
            ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
              formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
              stackFrameAt s0.sp totalStack) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜Panic st bs.length sf⌝ ∗ anyHeap) ∗ R)
      (fun sf => ⌜Oom st bs.length sf⌝) := by
  let F_tail : SepProp := formatterAt f out vt opts ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ F_stk
  refine SepWPp.tailcall (x := st) (F := F_tail) hws hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_) (fun _ _ _ _ hex => not_satisfies_false_sepConj hex) (fun sf _ hm_pan => ?_)
    (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => ?_, hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩)
    (fun sf R' _ hoom => ?_)
  · have hent_pre :
        ((stackFrameAt s0.sp stackBytes ∗ F_stk) ∗
          (W st s0 ∗ fmtSrcBytes ro ptr bs ∗ formatterAt f out vt opts ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn))) ⊢
        (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs).pre st sm ∗ F_tail := by
      dsimp only [fmtWriterStrSpec, F_tail]; rw [hsp_sm]; conv => rhs; rw [sepConj_assoc]
      refine Entails.pure_right ⟨hx0_sm, hx1_sm, hx2_sm, hlen_lt⟩ ?_
      exact Entails.trans (sepConj_mono_right (sepConj_mono_left (htransport st s0 sm hframe)))
        (entails_of_eq (by ac_rfl))
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent_pre) hm
  · dsimp only [fmtWriterStrSpec] at hm_pan
    exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan
  · dsimp only [fmtWriterStrSpec, F_tail] at hm_post; rw [hsp_sm] at hm_post
    have hent_post :
        ((∃∗ ok : Bool, ∃∗ st' : σ,
          ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
            fmtSrcBytes ro ptr bs ∗ W st' sf ∗ stackFrameAt s0.sp stackBytes) ∗
          (formatterAt f out vt opts ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ F_stk)) ⊢
        (∃∗ ok : Bool, ∃∗ st' : σ,
          ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
            formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
            stackFrameAt s0.sp totalStack) := by
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ok; apply Entails.sepExists_elim; intro st'
      refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
      refine Entails.trans (entails_of_eq (show _ =
        ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
          formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗
          (((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st' sf) ∗
          (stackFrameAt s0.sp stackBytes ∗ F_stk) by ac_rfl)) ?_
      rw [← hslot st' sf, hstk]; exact Entails.refl _
    exact Satisfies.mono (sepConj_mono_left hent_post) hm_post
  · dsimp only [fmtWriterStrSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom ⊢; exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

/-! ## `<core::fmt::Formatter>::write_str` (`coreFmtMultiLib` block `2`, `12` B) -/

/-- Placement-generic correctness of `<core::fmt::Formatter>::write_str` (`coreFmtMultiLib` block `2`,
    `12` B) under block-local hook freedom `LibBlockNoExtern coreFmtMultiLib mpl P 2` and
    `CodeLoadedWhere writeStrKeep mpl`. -/
theorem formatterWriteStr_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 2)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {f out vt wsFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterWriteStrSym)
      (coreFmtMultiLib.withCodeLoadedWhere writeStrKeep mpl
        (formatterWriteStrSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_writeStr hpl]; apply subroutine_ok_of_sepWPp_init
  intro st R s0 hpc0 hrun0 hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterWriteStrSpec] at hpre ⊢
  have hpre_reord :
      s0.mem ⊨ ⌜coreFmtMultiLib.CodeLoadedWhere writeStrKeep mpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = f ∧ s0.readReg64 .x1 = ptr ∧
            (s0.readReg64 .x2).toNat = bs.length ∧ bs.length < 2 ^ 60⌝ ∗
          (((f ↦₆₄ out) ∗ ((f + 8#64) ↦₆₄ vt) ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗
            (((f + 16#64) ↦₃₂ opts.flags) ∗ ((f + 20#64) ↦₁₆ opts.width) ∗
              ((f + 22#64) ↦₁₆ opts.precision)) ∗
            fmtSrcBytes ro ptr bs ∗ W st s0 ∗ stackFrameAt s0.sp stackBytes) ∗ R)) :=
    satisfies_of_eq (by
      conv => lhs; arg 1; arg 1; arg 2; arg 2; arg 2; arg 1; rw [hslot st s0]
      unfold formatterAt; ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre_reord; rcases hpre_reord with ⟨hcl0, hpre_reord⟩
  rw [satisfies_pure_sepConj] at hpre_reord
  rcases hpre_reord with ⟨⟨hx0_0, hx1_0, hx2_0, hlen_lt⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := writeStrKeep)
    2 ⟨by decide, by decide⟩ hext coreFmtNoSvc0_02 (mid := wsFn) hcl0
  intro s' hcpu_in
  change SepWP (coreFmtPC02.rebase coreFmtPl02.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl02.base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = f := (hcpu_in.readReg64 .x0).trans hx0_0
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc0; wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  have hsp_sm : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
  refine SepWPp.congr_pre (by unfold formatterAt; rw [sepConj_emp]; ac_rfl)
    (tailcall_ws_with_frame (totalStack := stackBytes) (F_stk := emp)
      htransport hslot hws (sepConj_emp _)
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun') hsp_sm
      (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm])
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
      (by
        have hx2_eq : sm.readReg64 .x2 = s0.readReg64 .x2 := by
          rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 .x2
        rw [hx2_eq]; exact hx2_0)
      hlen_lt
      (hcpu_in.calleeSavedPreserved hcpu_out (by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])))

theorem formatterWriteStr_of_writerOk {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 2) {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop} {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {f out vt wsFn wcFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterWriteStrSym)
      (coreFmtMultiLib.withCodeLoadedWhere writeStrKeep mpl
        (formatterWriteStrSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)) :=
  formatterWriteStr_ok hpl hext hw.transport hw.slot_write_str (hw.write_str ro ptr bs)

theorem formatterWriteStr_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 2)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere writeStrKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat} {f out vt wsFn : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterWriteStrSym)
      (formatterWriteStrSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload (formatterWriteStr_ok hpl hext htransport hslot hws)

/-! ## `<core::fmt::Formatter>::pad` (`coreFmtMultiLib` block `1`, `788` B, fast path) -/

/-- Placement-generic correctness of `<core::fmt::Formatter>::pad` (`coreFmtMultiLib` block `1`,
    `788` B) on the unaligned/unpadded fast path (`FmtPadFastOpts opts`) under block-local hook
    freedom `LibBlockNoExtern coreFmtMultiLib mpl P 1` and `CodeLoadedWhere padFastKeep mpl`. -/
theorem formatterPad_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 1)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {f out vt wsFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterPadSym)
      (coreFmtMultiLib.withCodeLoadedWhere padFastKeep mpl
        (formatterPadSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_pad hpl]; apply subroutine_ok_of_sepWPp_init
  intro st R s0 hpc0 hrun0 hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadSpec] at hpre ⊢
  have hmax_le : max 80 stackBytes ≤ 2 ^ 64 :=
    le_pow64_of_formatterAt_stackFrameAt (f := f) (out := out) (vt := vt) (sp := s0.sp) (opts := opts)
      (R := ⌜s0.readReg64 .x0 = f ∧ s0.readReg64 .x1 = ptr ∧
              (s0.readReg64 .x2).toNat = bs.length ∧ bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts⌝ ∗
            fmtSrcBytes ro ptr bs ∗ W st s0 ∗
            ⌜coreFmtMultiLib.CodeLoadedWhere padFastKeep mpl s0.mem⌝ ∗ R)
      (satisfies_of_eq (by ac_rfl) hpre)
  have hsplit80 :
      stackFrameAt s0.sp (max 80 stackBytes) =
        stackFrameAt s0.sp 80 ∗ stackFrameAt (s0.sp - 80#64) (max 80 stackBytes - 80) := by
    conv => lhs; rw [show max 80 stackBytes = 80 + (max 80 stackBytes - 80) by omega]
    exact stackFrameAt_split s0.sp 80 (max 80 stackBytes - 80) (by omega)
  have hpre_reord :
      s0.mem ⊨ ⌜coreFmtMultiLib.CodeLoadedWhere padFastKeep mpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = f ∧ s0.readReg64 .x1 = ptr ∧
            (s0.readReg64 .x2).toNat = bs.length ∧ bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts⌝ ∗
          ((stackFrameAt s0.sp 80 ∗
            (f ↦₆₄ out) ∗ ((f + 8#64) ↦₆₄ vt) ∗ ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗
            ((f + 16#64) ↦₃₂ opts.flags) ∗ ((f + 20#64) ↦₁₆ opts.width) ∗
            ((f + 22#64) ↦₁₆ opts.precision) ∗
            fmtSrcBytes ro ptr bs ∗ W st s0 ∗
            stackFrameAt (s0.sp - 80#64) (max 80 stackBytes - 80)) ∗ R)) :=
    satisfies_of_eq (by
      rw [hsplit80]
      conv => lhs; arg 1; arg 1; arg 2; arg 2; arg 2; arg 1; rw [hslot st s0]
      unfold formatterAt; ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre_reord; rcases hpre_reord with ⟨hcl0, hpre_reord⟩
  rw [satisfies_pure_sepConj] at hpre_reord
  rcases hpre_reord with ⟨⟨hx0_0, hx1_0, hx2_0, hlen_lt, hfast⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := padFastKeep)
    1 ⟨by decide, by decide⟩ hext coreFmtNoSvc0_01 (mid := wsFn) hcl0
  intro s' hcpu_in
  change SepWP (coreFmtPC01.rebase coreFmtPl01.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl01.base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hsp' : s'.spAligned = true := hcpu_in.spAligned.trans hsp0
  have hx0' : s'.readReg64 .x0 = f := (hcpu_in.readReg64 .x0).trans hx0_0
  have hfast' : opts.flags &&& 0x18000000#32 = 0#32 := hfast
  wp_conv_pre =>
    rw [← hcpu_in.sp_eq, ← stackAt_eq_stackFrameAt s'.sp 80, stackAt_eq_cells s'.sp 10]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
      sepConj_assoc]
  iterate 10 (apply SepWP.exists_elim; intro _)
  clear hpc0; wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  have hsp_sm : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
  have hstk :
      stackFrameAt s0.sp stackBytes ∗
        stackFrameAt (s0.sp - BitVec.ofNat 64 stackBytes) (max 80 stackBytes - stackBytes) =
      stackFrameAt s0.sp (max 80 stackBytes) := by
    rw [← stackFrameAt_split s0.sp stackBytes (max 80 stackBytes - stackBytes) (by omega),
        show stackBytes + (max 80 stackBytes - stackBytes) = max 80 stackBytes by omega]
  have hrec := padStack_recombine s0.sp
    (s'.readReg64 (.gpr 29#5)) (s'.readReg64 (.gpr 30#5))
    (s'.readReg64 (.gpr 26#5)) (s'.readReg64 (.gpr 25#5))
    (s'.readReg64 (.gpr 24#5)) (s'.readReg64 (.gpr 23#5))
    (s'.readReg64 (.gpr 22#5)) (s'.readReg64 (.gpr 21#5))
    (s'.readReg64 (.gpr 20#5)) (s'.readReg64 (.gpr 19#5)) stackBytes hmax_le
  refine SepWPp.congr_pre (by rw [hcpu_in.sp_eq]; unfold formatterAt; ac_rfl)
    (SepWPp.weaken_pre (sepConj_mono_left hrec)
      (tailcall_ws_with_frame htransport hslot hws hstk
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun') hsp_sm
        (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
        (by
          have hx2_eq : sm.readReg64 .x2 = s0.readReg64 .x2 := by
            rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 .x2
          rw [hx2_eq]; exact hx2_0)
        hlen_lt
        (hcpu_in.calleeSavedPreserved hcpu_out (by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))))

theorem formatterPad_of_writerOk {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 1) {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop} {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {f out vt wsFn wcFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterPadSym)
      (coreFmtMultiLib.withCodeLoadedWhere padFastKeep mpl
        (formatterPadSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)) :=
  formatterPad_ok hpl hext hw.transport hw.slot_write_str (hw.write_str ro ptr bs)

theorem formatterPad_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibBlockNoExtern coreFmtMultiLib mpl P 1)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere padFastKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat} {f out vt wsFn : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterPadSym)
      (formatterPadSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload (formatterPad_ok hpl hext htransport hslot hws)

/-! ## `<str as Display>::fmt` (block `10`) and `<&str as Display>::fmt` (block `7`) -/

private theorem tailcall_pad_with_frame {σ : Type} {mpl : MultiPlacement} {P : Program}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {f out vt : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {F_ref : SepProp} {st : σ} {R : SepProp} {s0 sm : State}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hpad : subroutine_ok P (coreFmtMultiLib.fnAddr mpl formatterPadSym)
      (coreFmtMultiLib.withCodeLoadedWhere padFastKeep mpl
        (formatterPadSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)))
    (hframe : FmtWriteFrame s0 sm) (hpc_sm : sm.pc = coreFmtMultiLib.fnAddr mpl formatterPadSym)
    (hrun_sm : sm.status = .Running) (hsp_sm : sm.sp = s0.sp) (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hx0_sm : sm.readReg64 .x0 = f) (hx1_sm : sm.readReg64 .x1 = ptr)
    (hx2_sm : (sm.readReg64 .x2).toNat = bs.length) (hlen_lt : bs.length < 2 ^ 60)
    (hfast : FmtPadFastOpts opts) (hcs_sm : CalleeSavedPreserved s0 sm)
    (hcl_pad : coreFmtMultiLib.CodeLoadedWhere padFastKeep mpl sm.mem) :
    SepWPp P (s0.readReg64 Reg.lr) sm
      (F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s0 ∗
        stackFrameAt s0.sp (max 80 stackBytes))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (∃∗ ok : Bool, ∃∗ st' : σ,
            ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
              F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
              stackFrameAt s0.sp (max 80 stackBytes)) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜Panic st bs.length sf⌝ ∗ anyHeap) ∗ R)
      (fun sf => ⌜Oom st bs.length sf⌝) := by
  refine SepWPp.tailcall (x := st) (F := F_ref) hpad hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_) (fun _ _ _ _ hex => not_satisfies_false_sepConj hex) (fun sf _ hm_pan => ?_)
    (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => ?_, hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩)
    (fun sf R' _ hoom => ?_)
  · have hent_pre :
        (F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s0 ∗
          stackFrameAt s0.sp (max 80 stackBytes)) ⊢
        (coreFmtMultiLib.withCodeLoadedWhere padFastKeep mpl
          (formatterPadSpec W StrStep Panic Oom stackBytes f out vt opts ro ptr bs)).pre st sm ∗
          F_ref := by
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadSpec]; rw [hsp_sm]
      refine Entails.trans (entails_of_eq (show _ = W st s0 ∗
        (formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗
          stackFrameAt s0.sp (max 80 stackBytes) ∗ F_ref) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left (htransport st s0 sm hframe)) ?_
      have hpure : sm.readReg64 .x0 = f ∧ sm.readReg64 .x1 = ptr ∧
          (sm.readReg64 .x2).toNat = bs.length ∧ bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts :=
        ⟨hx0_sm, hx1_sm, hx2_sm, hlen_lt, hfast⟩
      refine Entails.trans (Entails.pure_right hcl_pad (Entails.pure_right hpure (Entails.refl _))) ?_
      exact entails_of_eq (by ac_rfl)
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent_pre) hm
  · dsimp only [formatterPadSpec, MultiPlacedLib.withCodeLoadedWhere] at hm_pan
    exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan
  · dsimp only [formatterPadSpec, MultiPlacedLib.withCodeLoadedWhere] at hm_post
    rw [hsp_sm] at hm_post
    have hent_post :
        ((∃∗ ok : Bool, ∃∗ st' : σ,
          ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
            formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
            stackFrameAt s0.sp (max 80 stackBytes)) ∗ F_ref) ⊢
        (∃∗ ok : Bool, ∃∗ st' : σ,
          ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
            F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
            stackFrameAt s0.sp (max 80 stackBytes)) := by
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ok; apply Entails.sepExists_elim; intro st'
      exact Entails.sepExists_right ok (Entails.sepExists_right st' (entails_of_eq (by ac_rfl)))
    exact Satisfies.mono (sepConj_mono_left hent_post) hm_post
  · dsimp only [formatterPadSpec, MultiPlacedLib.withCodeLoadedWhere] at hoom
    rw [satisfies_pure_sepConj] at hoom ⊢; exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

/-- Placement-generic correctness of `<str as core::fmt::Display>::fmt` (`coreFmtMultiLib`
    block `10`, `20` B) on the `FmtPadFastOpts` fast path under cone-local hook freedom
    `LibKeepNoExtern coreFmtMultiLib strDisplayKeep mpl P` and `CodeLoadedWhere strDisplayKeep mpl`. -/
theorem strDisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wsFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere strDisplayKeep mpl
        (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts ro ptr bs)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_strDisplay hpl]; apply subroutine_ok_of_sepWPp_init
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hpre hsp0
  have hpad := formatterPad_ok hpl (hext 1 (by decide) (by decide))
    (f := f) (opts := opts) htransport hslot hws
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, strDisplayFmtSpec] at hpre ⊢
  have hpre_reord :
      s0.mem ⊨ ⌜coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            s0.readReg64 .x2 = f ∧ bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts⌝ ∗
          ((emp ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s0 ∗
            stackFrameAt s0.sp (max 80 stackBytes)) ∗ R)) :=
    satisfies_of_eq (by rw [emp_sepConj]; ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre_reord; rcases hpre_reord with ⟨hcl0, hpre_reord⟩
  rw [satisfies_pure_sepConj] at hpre_reord
  rcases hpre_reord with ⟨⟨hx0_0, hx1_0, hx2_0, hlen_lt, hfast⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := strDisplayKeep)
    10 ⟨by decide, by decide⟩ (hext 10 (by decide) (by decide)) coreFmtNoSvc0_10
    (mid := coreFmtMultiLib.fnAddr mpl formatterPadSym) hcl0
  intro s' hcpu_in
  change SepWP (coreFmtPC10.rebase coreFmtPl10.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl10.base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  clear hpc0; wp_sym_steps
  have hpc_target :
      coreFmtPl10.base + 16#64 +
          (coreFmtMultiLib.resolve coreFmtMpl formatterPadSym - coreFmtPl10.base - 16#64) =
        coreFmtMultiLib.fnAddr mpl formatterPadSym := by
    rw [show coreFmtPl10.base + 16#64 +
          (coreFmtMultiLib.resolve coreFmtMpl formatterPadSym - coreFmtPl10.base - 16#64) =
        coreFmtMultiLib.resolve coreFmtMpl formatterPadSym by bv_omega,
        show coreFmtMpl = mpl from rfl, resolve_pad hpl, fnAddr_pad hpl]
  refine SepWP.done (by dsimp only [State.setPC]; exact hpc_target)
    (by simpa [arm64_norm] using hrun') fun sm hcpu_out hcl_sm hpseg => ?_
  have hsp_sm : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
  simpa only [emp_sepConj] using
    tailcall_pad_with_frame (st := st) (F_ref := emp) (R := R) htransport hpad
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; dsimp only [State.setPC]; exact hpc_target)
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun') hsp_sm
      (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx2_0)
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx0_0)
      (by
        have hx2_eq : sm.readReg64 .x2 = s0.readReg64 .x1 := by
          rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 .x1
        rw [hx2_eq]; exact hx1_0)
      hlen_lt hfast
      (hcpu_in.calleeSavedPreserved hcpu_out (by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
      (fun i hi hk => hcl_sm i hi (by simp [padFastKeep, strDisplayKeep] at hk ⊢; exact Or.inl hk))

theorem strDisplayFmt_of_writerOk {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mpl P) {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop} {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wsFn wcFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64}
    {bs : List (BitVec 8)}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere strDisplayKeep mpl
        (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts ro ptr bs)) :=
  strDisplayFmt_ok hpl hext hw.transport hw.slot_write_str (hw.write_str ro ptr bs)

theorem strDisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat} {out vt wsFn : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strDisplayFmtSym)
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts ro ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload (strDisplayFmt_ok hpl hext htransport hslot hws)

/-- Placement-generic correctness of `<&str as core::fmt::Display>::fmt` (`coreFmtMultiLib`
    block `7`, `16` B) on the `FmtPadFastOpts` fast path under cone-local hook freedom
    `LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mpl P` and
    `CodeLoadedWhere strRefDisplayKeep mpl`. -/
theorem strRefDisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wsFn : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out srcRo ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strRefDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere strRefDisplayKeep mpl
        (strRefDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_strRefDisplay hpl]; apply subroutine_ok_of_sepWPp_init
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hpre hsp0
  have hpad := formatterPad_ok hpl (hext 1 (by decide) (by decide))
    (f := f) (opts := opts) htransport hslot hws
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, strRefDisplayFmtSpec] at hpre ⊢
  have hpre_reord :
      s0.mem ⊨ ⌜coreFmtMultiLib.CodeLoadedWhere strRefDisplayKeep mpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f ∧ bs.length < 2 ^ 60 ∧
            FmtPadFastOpts opts⌝ ∗
          ((fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 bs.length) ∗
            formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s0 ∗
            stackFrameAt s0.sp (max 80 stackBytes)) ∗ R)) :=
    satisfies_of_eq (by ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre_reord; rcases hpre_reord with ⟨hcl0, hpre_reord⟩
  rw [satisfies_pure_sepConj] at hpre_reord
  rcases hpre_reord with ⟨⟨hx0_0, hx1_0, hlen_lt, hfast⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := strRefDisplayKeep)
    7 ⟨by decide, by decide⟩ (hext 7 (by decide) (by decide)) coreFmtNoSvc0_07
    (mid := coreFmtMultiLib.fnAddr mpl formatterPadSym) hcl0
  intro s' hcpu_in
  change SepWP (coreFmtPC07.rebase coreFmtPl07.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl07.base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = valPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  clear hpc0
  have hpc_target :
      coreFmtPl07.base + 12#64 +
          (coreFmtMultiLib.resolve coreFmtMpl formatterPadSym - coreFmtPl07.base - 12#64) =
        coreFmtMultiLib.fnAddr mpl formatterPadSym := by
    rw [show coreFmtPl07.base + 12#64 +
          (coreFmtMultiLib.resolve coreFmtMpl formatterPadSym - coreFmtPl07.base - 12#64) =
        coreFmtMultiLib.resolve coreFmtMpl formatterPadSym by bv_omega,
        show coreFmtMpl = mpl from rfl, resolve_pad hpl, fnAddr_pad hpl]
  cases refRo <;>
    (wp_conv_pre => simp only [fmtRefStr, ↓reduceIte, Bool.false_eq_true, sepConj_assoc]) <;>
    wp_sym_steps <;>
    (refine SepWP.done (by dsimp only [State.setPC]; exact hpc_target)
      (by simpa [arm64_norm] using hrun') fun sm hcpu_out hcl_sm hpseg => ?_;
     have hsp_sm : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
     refine SepWPp.congr_pre ?_
       (tailcall_pad_with_frame (st := st) (R := R) htransport hpad
         (fmtWriteFrame_of_pureSeg hpseg
           (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
           (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
         (by rw [hcpu_out.pc_eq]; dsimp only [State.setPC]; exact hpc_target)
         (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun') hsp_sm
         (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
         (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
         (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
         (by rw [hcpu_out.readReg64]; simp [arm64_norm])
         (by
           have hx2_eq : sm.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
             rw [hcpu_out.readReg64]; simp [arm64_norm]
           rw [hx2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
         hlen_lt hfast
         (hcpu_in.calleeSavedPreserved hcpu_out (by
           rw [CalleeSavedPreserved.iff_regs]
           refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
         (fun i hi hk => hcl_sm i hi
           (by simp [padFastKeep, strRefDisplayKeep] at hk ⊢; exact Or.inl (Or.inl hk))));
     simp only [fmtRefStr, Bool.false_eq_true, ↓reduceIte, sepConj_assoc])

theorem strRefDisplayFmt_of_writerOk {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mpl P) {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop} {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wsFn wcFn : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr ptr : BitVec 64} {bs : List (BitVec 8)}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strRefDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere strRefDisplayKeep mpl
        (strRefDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs)) :=
  strRefDisplayFmt_ok hpl hext hw.transport hw.slot_write_str (hw.write_str srcRo ptr bs)

theorem strRefDisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strRefDisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat} {out vt wsFn : BitVec 64}
    {opts : FmtOptions} {refRo srcRo : Bool} {valPtr ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hslot : ∀ (st : σ) (s : State), W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ W st s)
    (hws : subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out srcRo ptr bs)) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl strRefDisplayFmtSym)
      (strRefDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload (strRefDisplayFmt_ok hpl hext htransport hslot hws)

/-! ## Crate-local 20-byte `<&str as Display>::fmt` and `<String as Display>::fmt` shims -/

/-- Five-instruction template of crate-local `<&str as core::fmt::Display>::fmt` shims
    (`ldp x8, x9, [x0]; mov x2, x1; mov x0, x8; mov x1, x9; b <str as Display>::fmt`). -/
def strRefDisplayShimWords : List (BitVec 32) :=
  [0xa9402408#32, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32, 0x14000000#32]

/-- Five-instruction template of crate-local `<alloc::string::String as core::fmt::Display>::fmt`
    shims (`ldp x8, x9, [x0, #8]; mov x2, x1; mov x0, x8; mov x1, x9; b <str as Display>::fmt`). -/
def stringDisplayShimWords : List (BitVec 32) :=
  [0xa940a408#32, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32, 0x14000000#32]

/-- Extract the `jump26` target symbol of a 5-instruction display shim block `bi` of `lib`. -/
def displayShimTargetSym (lib : MultiPlacedLib) (bi : Nat) : String :=
  match lib.blocks[bi]? with
  | some blk => match blk.relocs with | [r] => r.sym | _ => ""
  | none => ""

/-- Decidable check that block `bi` of `lib` has no raw `svc #0` instructions and matches the
    5-word template `ws` at offset `0` with a single `jump26` relocation (`addend = 0`) at byte
    offset `16`. -/
def checkDisplayShimBlock (ws : List (BitVec 32)) (lib : MultiPlacedLib) (bi : Nat) : Bool :=
  match lib.blocks[bi]? with
  | some blk =>
    match blk.relocs with
    | [r] => checkBlockNoSvc0 blk && (r.off == 16) && (r.kind == .jump26) &&
        (r.addend == 0) && blk.checkSegment 0 ws [r]
    | _ => false
  | none => false

/-- Decidable check that block `bi` of `lib` is a 20-byte `<&str as Display>::fmt` shim. -/
def checkStrRefDisplayShimBlock (lib : MultiPlacedLib) (bi : Nat) : Bool :=
  checkDisplayShimBlock strRefDisplayShimWords lib bi

/-- Decidable check that block `bi` of `lib` is a 20-byte `<String as Display>::fmt` shim. -/
def checkStringDisplayShimBlock (lib : MultiPlacedLib) (bi : Nat) : Bool :=
  checkDisplayShimBlock stringDisplayShimWords lib bi

private theorem displayShim_fetches_of_check {w0 : BitVec 32} {inst0 : Instr}
    (hd0 : decode w0 = some inst0) {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) {bi : Nat}
    (hchk : checkDisplayShimBlock
      [w0, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32, 0x14000000#32] lib bi = true) :
    let prog := (lib.blockProgram mpl bi).rebase (mpl.base bi) (fun _ => none)
    ∃ _hbi : bi < lib.blocks.length, checkBlockNoSvc0 (lib.blockLib bi).text = true ∧
      prog.fetch (mpl.base bi) = some inst0 ∧
      prog.fetch (mpl.base bi + 4#64) = some (.logicalShift .W64 .ORR .x2 .xzr .x1 .LSL 0) ∧
      prog.fetch (mpl.base bi + 8#64) = some (.logicalShift .W64 .ORR .x0 .xzr .x8 .LSL 0) ∧
      prog.fetch (mpl.base bi + 12#64) = some (.logicalShift .W64 .ORR .x1 .xzr .x9 .LSL 0) ∧
      prog.fetch (mpl.base bi + 16#64) =
        some (.b (lib.resolve mpl (displayShimTargetSym lib bi) - (mpl.base bi + 16#64))) := by
  unfold checkDisplayShimBlock at hchk
  cases hblk? : lib.blocks[bi]? with
  | none => simp [hblk?] at hchk
  | some blk =>
    rw [hblk?] at hchk; obtain ⟨hbi, hblk_eq⟩ := List.getElem?_eq_some_iff.mp hblk?
    cases hrel : blk.relocs with
    | nil => simp [hrel] at hchk
    | cons r rs =>
      cases rs with
      | cons _ _ => simp [hrel] at hchk
      | nil =>
        rcases r with ⟨roff, rkind, rsym, radd, rloc⟩
        simp only [hrel, Bool.and_eq_true, beq_iff_eq] at hchk
        rcases hchk with ⟨⟨⟨⟨hnosvc, rfl⟩, rfl⟩, rfl⟩, hseg⟩
        have htsym : displayShimTargetSym lib bi = rsym := by simp [displayShimTargetSym, hblk?, hrel]
        have ⟨hw, hrange⟩ := lib.hasWords_of_checkSegment hbi
          (X := fun _ => none) (svc := (lib.blockProgram mpl bi).svc) hpl (hblk_eq ▸ hseg)
        have hprog : (lib.blockProgram mpl bi).rebase (mpl.base bi) (fun _ => none) =
            lib.blockProgram mpl bi (fun _ => none) (fun _ => none) (lib.blockProgram mpl bi).svc := rfl
        have hpatch :
            patchRelocs [{ off := 16, kind := .jump26, sym := rsym, addend := 0, localSym := rloc }]
              [w0, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32, 0x14000000#32]
              (mpl.base bi) (lib.resolve mpl) =
            [w0, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32,
              branchWord 0x14000000#32 (mpl.base bi + 16#64) (lib.resolve mpl rsym)] := rfl
        rw [← hprog, BitVec.add_zero, hpatch] at hw
        have hbr : BranchInRange (mpl.base bi + 16#64) (lib.resolve mpl rsym) := by
          simpa [CodeRelocInRange, BitVec.add_zero, addSignedAddr] using hrange _ List.mem_cons_self
        refine ⟨hbi, by rw [lib.blockLib_text hbi, hblk_eq]; exact hnosvc, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [BitVec.add_zero] using (Program.fetch_of_hasWords hw 0 (by simp)).trans hd0
        · exact (Program.fetch_of_hasWords hw 1 (by simp)).trans (show decode 0xaa0103e2#32 = _ by decide)
        · exact (Program.fetch_of_hasWords hw 2 (by simp)).trans (show decode 0xaa0803e0#32 = _ by decide)
        · exact (Program.fetch_of_hasWords hw 3 (by simp)).trans (show decode 0xaa0903e1#32 = _ by decide)
        · rw [htsym]; exact fetch_of_hasWords_bAt 4 hw rfl rfl rfl (by decide) hbr

private def displayRefShimSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (opts : FmtOptions) (srcRo : Bool) (valPtr ptr : BitVec 64)
    (bs : List (BitVec 8)) (F_ref : SepProp) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ bs.length < 2 ^ 60 ∧
      FmtPadFastOpts opts⌝ ∗
      F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s ∗
      stackFrameAt s.sp (max 80 stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp (max 80 stackBytes)
  onPanic := fun (st, _) _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf => ⌜Oom st bs.length sf⌝

private theorem displayShim_ok_aux {σ : Type} {w0 : BitVec 32} {off0 : BitVec 64}
    (hd0 : decode w0 = some (.ldp .W64 false .x8 .x9 (.Offset .x0 off0)))
    {lib : MultiPlacedLib} {keep : Nat → Bool} {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    (bi : Nat) (hkeep : keep bi = true)
    (hshim : checkDisplayShimBlock
      [w0, 0xaa0103e2#32, 0xaa0803e0#32, 0xaa0903e1#32, 0x14000000#32] lib bi = true)
    {P : Program} (hext : LibBlockNoExtern lib mpl P bi) {entry strDisplayAddr : BitVec 64}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr ptr : BitVec 64} {bs : List (BitVec 8)} {F_ref F_hdr : SepProp}
    (href : F_ref =
      (if refRo then ((valPtr + off0) ↦₆₄ᵣ ptr) ∗ (((valPtr + off0) + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 bs.length)
       else ((valPtr + off0) ↦₆₄ ptr) ∗ (((valPtr + off0) + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗ F_hdr)
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hstr : subroutine_ok P strDisplayAddr
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts srcRo ptr bs))
    (hentry : entry = mpl.base bi)
    (htarget : lib.resolve mpl (displayShimTargetSym lib bi) = strDisplayAddr) :
    subroutine_ok P entry
      (lib.withCodeLoadedWhere keep mpl
        (displayRefShimSpec W StrStep Panic Oom stackBytes out vt opts srcRo valPtr ptr bs F_ref)) := by
  subst hentry
  obtain ⟨hbi, hnosvc, hf0, hf1, hf2, hf3, hf4⟩ := displayShim_fetches_of_check hd0 hpl hshim
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, displayRefShimSpec] at hpre ⊢
  have hpre_reord :
      s0.mem ⊨ ⌜lib.CodeLoadedWhere keep mpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f ∧ bs.length < 2 ^ 60 ∧
            FmtPadFastOpts opts⌝ ∗
          ((F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s0 ∗
            stackFrameAt s0.sp (max 80 stackBytes)) ∗ R)) :=
    satisfies_of_eq (by ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre_reord; rcases hpre_reord with ⟨hcl0, hpre_reord⟩
  rw [satisfies_pure_sepConj] at hpre_reord
  rcases hpre_reord with ⟨⟨hx0_0, hx1_0, hlen_lt, hfast⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := lib) (keep := keep)
    bi ⟨hbi, hkeep⟩ hext hnosvc (mid := strDisplayAddr) hcl0
  intro s' hcpu_in
  have hpc' : s'.pc = mpl.base bi := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = valPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  clear hpc0; rw [htarget] at hf4
  cases refRo <;>
    (wp_conv_pre => rw [href]; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]) <;>
    (iterate 5 wp_step) <;>
    (refine SepWP.done (by simp only [arm64_norm]; bv_omega)
      (by simpa [arm64_norm] using hrun') fun sm hcpu_out _hcl_sm hpseg => ?_;
     have hsp_sm : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
     have hx1_sm : (sm.readReg64 .x1).toNat = bs.length := by
       have hx1_eq : sm.readReg64 .x1 = BitVec.ofNat 64 bs.length := by
         rw [hcpu_out.readReg64]; simp [arm64_norm]
       rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
     refine SepWPp.congr_pre (show _ =
       F_ref ∗ formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s0 ∗
         stackFrameAt s0.sp (max 80 stackBytes) by
       rw [href]; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]) ?_;
     exact SepWPp.tailcall (x := (st, f)) (F := F_ref) hstr
       (by rw [hcpu_out.pc_eq]; simp only [arm64_norm]; bv_omega)
       (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
       (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
       (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
       (fun R' hm => by
         rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
         dsimp only [strDisplayFmtSpec]; rw [hsp_sm]; conv => rhs; rw [sepConj_assoc]
         refine Entails.pure_right ⟨by rw [hcpu_out.readReg64]; simp [arm64_norm], hx1_sm,
           by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0,
           hlen_lt, hfast⟩ ?_
         refine Entails.trans (entails_of_eq (show _ = W st s0 ∗
           (formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗
             stackFrameAt s0.sp (max 80 stackBytes) ∗ F_ref) by ac_rfl)) ?_
         exact Entails.trans (sepConj_mono_left (htransport st s0 sm
           (fmtWriteFrame_of_pureSeg hpseg
             (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
             (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))))
           (entails_of_eq (by ac_rfl)))
       (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
       (fun sf _ hm_pan => by
         dsimp only [strDisplayFmtSpec] at hm_pan
         exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan)
       (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => by
         dsimp only [strDisplayFmtSpec] at hm_post; rw [hsp_sm] at hm_post
         refine Satisfies.mono (sepConj_mono_left ?_) hm_post
         simp only [sepExists_sepConj_left]
         apply Entails.sepExists_elim; intro ok; apply Entails.sepExists_elim; intro st'
         exact Entails.sepExists_right ok (Entails.sepExists_right st' (entails_of_eq (by ac_rfl))),
         hspf.trans hsp_sm,
         (hcpu_in.calleeSavedPreserved hcpu_out (by
           rw [CalleeSavedPreserved.iff_regs]
           refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])).trans
           hcs_sf⟩)
       (fun sf R' _ hoom => by
         dsimp only [strDisplayFmtSpec] at hoom
         rw [satisfies_pure_sepConj] at hoom ⊢; exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩))

/-- Placement-generic correctness of a crate-local 20-byte `<&str as core::fmt::Display>::fmt`
    shim block `bi` of `lib`, reducing `strRefDisplayFmtSpec` to `strDisplayFmtSpec` at
    `strDisplayAddr` under block-local hook freedom `LibBlockNoExtern lib mpl P bi`. -/
theorem strRefDisplayShim_ok {σ : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    (bi : Nat) (hkeep : keep bi = true := by decide)
    (hshim : checkStrRefDisplayShimBlock lib bi = true := by decide)
    {P : Program} (hext : LibBlockNoExtern lib mpl P bi) {entry strDisplayAddr : BitVec 64}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hstr : subroutine_ok P strDisplayAddr
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts srcRo ptr bs))
    (hentry : entry = mpl.base bi := by rfl)
    (htarget : lib.resolve mpl (displayShimTargetSym lib bi) = strDisplayAddr := by rfl) :
    subroutine_ok P entry
      (lib.withCodeLoadedWhere keep mpl
        (strRefDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs)) :=
  displayShim_ok_aux (w0 := 0xa9402408#32) (off0 := 0#64) (refRo := refRo) (by decide)
    hpl bi hkeep hshim hext (F_hdr := emp)
    (by cases refRo <;> simp [fmtRefStr, BitVec.add_zero, sepConj_emp])
    htransport hstr hentry htarget

theorem strRefDisplayShim_of_codeLoaded {σ : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    (bi : Nat) (hkeep : keep bi = true := by decide)
    (hshim : checkStrRefDisplayShimBlock lib bi = true := by decide)
    {P : Program} (hext : LibBlockNoExtern lib mpl P bi)
    (hload : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoadedWhere keep mpl m)
    {entry strDisplayAddr : BitVec 64}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hstr : subroutine_ok P strDisplayAddr
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts srcRo ptr bs))
    (hentry : entry = mpl.base bi := by rfl)
    (htarget : lib.resolve mpl (displayShimTargetSym lib bi) = strDisplayAddr := by rfl) :
    subroutine_ok P entry
      (strRefDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload
    (strRefDisplayShim_ok hpl bi hkeep hshim hext htransport hstr hentry htarget)

/-- Placement-generic correctness of a crate-local 20-byte
    `<alloc::string::String as core::fmt::Display>::fmt` shim block `bi` of `lib`, reducing
    `stringDisplayFmtSpec` to `strDisplayFmtSpec` at `strDisplayAddr` under block-local hook
    freedom `LibBlockNoExtern lib mpl P bi`. -/
theorem stringDisplayShim_ok {σ : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    (bi : Nat) (hkeep : keep bi = true := by decide)
    (hshim : checkStringDisplayShimBlock lib bi = true := by decide)
    {P : Program} (hext : LibBlockNoExtern lib mpl P bi) {entry strDisplayAddr : BitVec 64}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hstr : subroutine_ok P strDisplayAddr
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts srcRo ptr bs))
    (hentry : entry = mpl.base bi := by rfl)
    (htarget : lib.resolve mpl (displayShimTargetSym lib bi) = strDisplayAddr := by rfl) :
    subroutine_ok P entry
      (lib.withCodeLoadedWhere keep mpl
        (stringDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr cap ptr bs)) :=
  displayShim_ok_aux (w0 := 0xa940a408#32) (off0 := 8#64) (refRo := refRo) (by decide)
    hpl bi hkeep hshim hext (F_hdr := if refRo then valPtr ↦₆₄ᵣ cap else valPtr ↦₆₄ cap)
    (by cases refRo <;>
        simp only [fmtRefString, vecHeader, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc] <;>
        ac_rfl)
    htransport hstr hentry htarget

theorem stringDisplayShim_of_codeLoaded {σ : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    (bi : Nat) (hkeep : keep bi = true := by decide)
    (hshim : checkStringDisplayShimBlock lib bi = true := by decide)
    {P : Program} (hext : LibBlockNoExtern lib mpl P bi)
    (hload : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoadedWhere keep mpl m)
    {entry strDisplayAddr : BitVec 64}
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt : BitVec 64} {opts : FmtOptions} {refRo srcRo : Bool}
    {valPtr cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (htransport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (hstr : subroutine_ok P strDisplayAddr
      (strDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts srcRo ptr bs))
    (hentry : entry = mpl.base bi := by rfl)
    (htarget : lib.resolve mpl (displayShimTargetSym lib bi) = strDisplayAddr := by rfl) :
    subroutine_ok P entry
      (stringDisplayFmtSpec W StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr cap ptr bs) :=
  subroutine_ok_drop_codeLoadedWhere hload
    (stringDisplayShim_ok hpl bi hkeep hshim hext htransport hstr hentry htarget)

/-! ## `fmtArgCallSpec` callback lift lemmas -/

private theorem displayFmt_fmtArg_ok_of_ref {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {out vt valPtr fmtFn ptr : BitVec 64} {opts : FmtOptions}
    {srcRo : Bool} {bs : List (BitVec 8)} {F_ref : SepProp}
    (hfmt : subroutine_ok P fmtFn
      (displayRefShimSpec W_inner StrStep Panic Oom stackBytes out vt opts srcRo valPtr ptr bs F_ref))
    (hlen : bs.length < 2 ^ 60) (hfast : FmtPadFastOpts opts)
    (hstep : ∀ st ok st', StrStep st bs ok st' → Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf, Panic st bs.length sf → PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf, Oom st bs.length sf → OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : max 80 stackBytes ≤ argStackBytes)
    (hW : ∀ (st : σ) (s : State), W st s = F_ref ∗ fmtSrcBytes srcRo ptr bs ∗ W_inner st s) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) := by
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [fmtArgCallSpec] at hpre ⊢
  have harg_le : argStackBytes ≤ 2 ^ 64 :=
    le_pow64_of_formatterAt_stackFrameAt (f := f) (out := out) (vt := vt) (sp := s0.sp) (opts := opts)
      (R := ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f⌝ ∗ W st s0 ∗ R)
      (satisfies_of_eq (by ac_rfl) hpre)
  have hstk :
      stackFrameAt s0.sp argStackBytes =
        stackFrameAt s0.sp (max 80 stackBytes) ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 (max 80 stackBytes))
            (argStackBytes - max 80 stackBytes) := by
    conv => lhs; rw [show argStackBytes = max 80 stackBytes + (argStackBytes - max 80 stackBytes) by omega]
    exact stackFrameAt_split s0.sp (max 80 stackBytes) (argStackBytes - max 80 stackBytes) (by omega)
  have hpre' :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((formatterAt f out vt opts ∗ W st s0 ∗ stackFrameAt s0.sp argStackBytes) ∗ R) :=
    satisfies_of_eq (by ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre'; rcases hpre' with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  let F_stk : SepProp :=
    stackFrameAt (s0.sp - BitVec.ofNat 64 (max 80 stackBytes)) (argStackBytes - max 80 stackBytes)
  refine SepWPp.tailcall (x := (st, f)) (F := F_stk) hfmt hpc0 hrun0 hsp0 rfl
    (fun R' hm => ?_) (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ hm_pan => ?_) (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => ?_, hspf, hcs_sf⟩)
    (fun sf R' _ h_oom => ?_)
  · rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [displayRefShimSpec, F_stk]; rw [hW st s0, hstk]; conv => rhs; rw [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_0, hx1_0, hlen, hfast⟩ (entails_of_eq (by ac_rfl))
  · dsimp only [displayRefShimSpec] at hm_pan
    refine Satisfies.mono (sepConj_mono_left ?_) hm_pan
    rw [sepConj_assoc]
    exact Entails.pure_left fun hp => Entails.pure_right (hpanic st sf hp) (entails_anyHeap _)
  · dsimp only [displayRefShimSpec, F_stk] at hm_post
    refine Satisfies.mono (sepConj_mono_left ?_) hm_post
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ok; apply Entails.sepExists_elim; intro st'
    refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
    rw [sepConj_assoc]; apply Entails.pure_left; rintro ⟨hw0, hst⟩
    refine Entails.pure_right ⟨by rw [hw0]; cases ok <;> decide, hstep st ok st' hst⟩ ?_
    rw [hW st' sf, hstk]
    refine Entails.trans (entails_of_eq (show _ = formatterAt f out vt opts ∗
      ((F_ref ∗ fmtSrcBytes srcRo ptr bs ∗ W_inner st' sf) ∗
        (stackFrameAt s0.sp (max 80 stackBytes) ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 (max 80 stackBytes))
            (argStackBytes - max 80 stackBytes))) by ac_rfl)) ?_
    exact sepConj_mono_left (formatterAt_entails_memRegion24_local f out vt opts)
  · dsimp only [displayRefShimSpec] at h_oom
    rw [satisfies_pure_sepConj] at h_oom ⊢
    exact ⟨hoom st sf h_oom.1, Satisfies.drop_left h_oom.2⟩

/-- Lift a `<&str as Display>::fmt` contract (`strRefDisplayFmtSpec`) to a `core::fmt::write`
    argument callback contract (`fmtArgCallSpec`) when `W` frames `fmtRefStr` and `fmtSrcBytes`
    around `W_inner` and `FmtPadFastOpts opts` holds. -/
theorem strRefDisplayFmt_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {out vt valPtr fmtFn ptr : BitVec 64} {opts : FmtOptions}
    {refRo srcRo : Bool} {bs : List (BitVec 8)}
    (hfmt : subroutine_ok P fmtFn
      (strRefDisplayFmtSpec W_inner StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr ptr bs))
    (hlen : bs.length < 2 ^ 60) (hfast : FmtPadFastOpts opts)
    (hstep : ∀ st ok st', StrStep st bs ok st' → Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf, Panic st bs.length sf → PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf, Oom st bs.length sf → OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : max 80 stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 bs.length) ∗
        fmtSrcBytes srcRo ptr bs ∗ W_inner st s := by intros; ac_rfl) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) :=
  displayFmt_fmtArg_ok_of_ref hfmt hlen hfast hstep hpanic hoom hstack hW

/-- Lift a `<String as Display>::fmt` contract (`stringDisplayFmtSpec`) to a `core::fmt::write`
    argument callback contract (`fmtArgCallSpec`) when `W` frames `fmtRefString` and `fmtSrcBytes`
    around `W_inner` and `FmtPadFastOpts opts` holds. -/
theorem stringDisplayFmt_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {out vt valPtr cap fmtFn ptr : BitVec 64} {opts : FmtOptions}
    {refRo srcRo : Bool} {bs : List (BitVec 8)}
    (hfmt : subroutine_ok P fmtFn
      (stringDisplayFmtSpec W_inner StrStep Panic Oom stackBytes out vt opts refRo srcRo valPtr cap ptr bs))
    (hlen : bs.length < 2 ^ 60) (hfast : FmtPadFastOpts opts)
    (hstep : ∀ st ok st', StrStep st bs ok st' → Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf, Panic st bs.length sf → PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf, Oom st bs.length sf → OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : max 80 stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRefString refRo valPtr cap ptr (BitVec.ofNat 64 bs.length) ∗
        fmtSrcBytes srcRo ptr bs ∗ W_inner st s := by intros; ac_rfl) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) :=
  displayFmt_fmtArg_ok_of_ref hfmt hlen hfast hstep hpanic hoom hstack hW

end VerifiedLibraries.RustStd
