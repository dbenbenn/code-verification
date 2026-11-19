/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayU64Inner

/-!
# `Display` Formatting Proofs for `u64` and `usize`

Proves `subroutine_ok` specifications for `<u64 as core::fmt::Display>::fmt` and
`<usize as core::fmt::Display>::fmt` (`coreFmtMultiLib` block `9`, calling `_fmt_inner` in
block `3`) given a `pad_integral` contract, and lifts them to `core::fmt::write` argument
callbacks (`u64DisplayFmt_fmtArg_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd
open IntDisplayAux

private def CalleeSaved22_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem CalleeSaved22_28.trans {s0 s1 s2 : State}
    (h01 : CalleeSaved22_28 s0 s1) (h12 : CalleeSaved22_28 s1 s2) : CalleeSaved22_28 s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem CalleeSaved22_28.trans_cs {s0 s1 s2 : State}
    (h01 : CalleeSaved22_28 s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSaved22_28 s0 s2 :=
  ⟨h12.2.2.2.1.trans h01.1,
   h12.2.2.2.2.1.trans h01.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.1,
   h12.2.2.2.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem CalleeSaved22_28.of_sameCpu_out {a b b' : State}
    (h_out : SameCpuState b b') (h : CalleeSaved22_28 a b') : CalleeSaved22_28 a b :=
  ⟨(h_out.readReg64 _).trans h.1, (h_out.readReg64 _).trans h.2.1,
   (h_out.readReg64 _).trans h.2.2.1, (h_out.readReg64 _).trans h.2.2.2.1,
   (h_out.readReg64 _).trans h.2.2.2.2.1, (h_out.readReg64 _).trans h.2.2.2.2.2.1,
   (h_out.readReg64 _).trans h.2.2.2.2.2.2.1, h_out.calleeSavedVRegs.trans h.2.2.2.2.2.2.2⟩

private theorem CalleeSaved22_28.of_sameCpu_in {a a' b : State}
    (h_in : SameCpuState a' a) (h : CalleeSaved22_28 a' b) : CalleeSaved22_28 a b :=
  ⟨h.1.trans (h_in.readReg64 _), h.2.1.trans (h_in.readReg64 _),
   h.2.2.1.trans (h_in.readReg64 _), h.2.2.2.1.trans (h_in.readReg64 _),
   h.2.2.2.2.1.trans (h_in.readReg64 _), h.2.2.2.2.2.1.trans (h_in.readReg64 _),
   h.2.2.2.2.2.2.1.trans (h_in.readReg64 _), h.2.2.2.2.2.2.2.trans h_in.calleeSavedVRegs⟩

theorem fmtRef64_false (p : BitVec 64) (v : BitVec 64) : fmtRef64 false p v = (p ↦₆₄ v) := by
  simp only [fmtRef64, Bool.false_eq_true, ↓reduceIte]

theorem fmtRef64_true (p : BitVec 64) (v : BitVec 64) : fmtRef64 true p v = (p ↦₆₄ᵣ v) := by
  simp only [fmtRef64, ↓reduceIte]

private theorem u64Display_stack_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 0x50 =
      stackFrameAt sp0 48 ∗ memRegion (sp0 - 0x50#64) 12 ∗
        memRegion ((sp0 - 0x50#64) + 0x0c#64) 20 := by
  rw [show (0x50 : Nat) = 48 + 32 from rfl, stackFrameAt_split sp0 48 32 (by decide),
      stackFrameAt_eq_memRegion (sp0 - BitVec.ofNat 64 48) 32 (by decide),
      show sp0 - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 = sp0 - 0x50#64 by simp [bv_lin_norm],
      memRegion_split_le (sp0 - 0x50#64) 12 32 (by decide) (by decide)]

private theorem u64Display_buf_repack (sp0 : BitVec 64) (bs : List (BitVec 8))
    (hhi : bs.length ≤ 20) :
    memRegion (sp0 - 0x50#64) 12 ∗
      memRegion ((sp0 - 0x50#64) + 0x0c#64) (20 - bs.length) ∗
      (((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) ↦ₛ bs) ⊢
      stackFrameAt (sp0 - BitVec.ofNat 64 48) 32 := by
  have hbs : (((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) ↦ₛ bs) ⊢
      memRegion ((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) bs.length := by
    have h := pointsToBytes_memRegion_entails
      ((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) bs bs.length
      (Nat.le_refl _) (by omega)
    simpa [Nat.sub_self, memRegion_zero, sepConj_emp] using h
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hbs)) ?_
  have hm := memRegion_split_le ((sp0 - 0x50#64) + 0x0c#64) (20 - bs.length) 20 (by omega) (by decide)
  rw [show 20 - (20 - bs.length) = bs.length by omega] at hm
  rw [← hm, ← memRegion_split_le (sp0 - 0x50#64) 12 32 (by decide) (by decide),
      stackFrameAt_eq_memRegion (sp0 - BitVec.ofNat 64 48) 32 (by decide),
      show sp0 - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 = sp0 - 0x50#64 by simp [bv_lin_norm]]
  exact Entails.refl _

private theorem u64Display_frame_unpack (sp0 : BitVec 64) (stackBytes : Nat)
    (hlt : 240 + stackBytes < 2 ^ 64) :
    stackFrameAt sp0 (240 + stackBytes) ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
        (((sp0 - 48#64) ↦₆₄ c0) ∗ ((sp0 - 40#64) ↦₆₄ c1) ∗ ((sp0 - 32#64) ↦₆₄ c2) ∗
          ((sp0 - 24#64) ↦₆₄ c3) ∗ ((sp0 - 16#64) ↦₆₄ c4) ∗ ((sp0 - 8#64) ↦₆₄ c5)) ∗
        memRegion (sp0 - 0x50#64) 12 ∗ memRegion ((sp0 - 0x50#64) + 0x0c#64) 20 ∗
        stackFrameAt (sp0 - 0x50#64) 0x10 ∗
        stackFrameAt ((sp0 - 0x50#64) - 0x10#64) (144 + stackBytes) := by
  rw [show 240 + stackBytes = 0x50 + (0x10 + (144 + stackBytes)) by omega,
      stackFrameAt_split sp0 0x50 (0x10 + (144 + stackBytes)) (by omega),
      stackFrameAt_split (sp0 - BitVec.ofNat 64 0x50) 0x10 (144 + stackBytes) (by omega),
      u64Display_stack_unpack sp0,
      ← stackAt_eq_stackFrameAt sp0 48, stackAt_eq_cells sp0 6]
  simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun c0 => Entails.sepExists_right c0 ?_
  refine Entails.sepExists_elim fun c1 => Entails.sepExists_right c1 ?_
  refine Entails.sepExists_elim fun c2 => Entails.sepExists_right c2 ?_
  refine Entails.sepExists_elim fun c3 => Entails.sepExists_right c3 ?_
  refine Entails.sepExists_elim fun c4 => Entails.sepExists_right c4 ?_
  refine Entails.sepExists_elim fun c5 => Entails.sepExists_right c5 ?_
  sep_frame

private theorem u64Display_pad_frame_join (sp1 : BitVec 64) (stackBytes : Nat)
    (hlt : 240 + stackBytes < 2 ^ 64) :
    stackFrameAt sp1 0x10 ∗ stackFrameAt (sp1 - 0x10#64) (144 + stackBytes) ⊢
      stackFrameAt sp1 (160 + stackBytes) := by
  rw [show 160 + stackBytes = 0x10 + (144 + stackBytes) by omega,
      stackFrameAt_split sp1 0x10 (144 + stackBytes) (by omega)]
  exact Entails.refl _

private theorem u64Display_frame_repack (sp0 : BitVec 64) (stackBytes : Nat)
    (hlt : 240 + stackBytes < 2 ^ 64) (r29 r30 r21 c3 r20 r19 : BitVec 64)
    (ds : List (BitVec 8)) (hhi : ds.length ≤ 20) :
    (((sp0 - 48#64) ↦₆₄ r29) ∗ ((sp0 - 40#64) ↦₆₄ r30) ∗ ((sp0 - 32#64) ↦₆₄ r21) ∗
      ((sp0 - 24#64) ↦₆₄ c3) ∗ ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19)) ∗
    (memRegion (sp0 - 0x50#64) 12 ∗ memRegion ((sp0 - 0x50#64) + 0x0c#64) (20 - ds.length) ∗
      (((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - ds.length)) ↦ₛ ds)) ∗
    stackFrameAt (sp0 - 0x50#64) (160 + stackBytes) ⊢
    stackFrameAt sp0 (240 + stackBytes) := by
  have hsaved : (((sp0 - 48#64) ↦₆₄ r29) ∗ ((sp0 - 40#64) ↦₆₄ r30) ∗ ((sp0 - 32#64) ↦₆₄ r21) ∗
      ((sp0 - 24#64) ↦₆₄ c3) ∗ ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19)) ⊢
      stackFrameAt sp0 48 := by
    rw [← stackAt_eq_stackFrameAt sp0 48, stackAt_eq_cells sp0 6]
    simp only [Nat.reduceMul]
    iterate 5 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
    exact cells_one_entails _ _
  refine Entails.trans (sepConj_mono hsaved (sepConj_mono_left (u64Display_buf_repack sp0 ds hhi))) ?_
  rw [← sepConj_assoc, ← stackFrameAt_split sp0 48 32 (by decide),
      show (48 : Nat) + 32 = 0x50 from rfl,
      ← stackFrameAt_split sp0 0x50 (160 + stackBytes) (by omega),
      show 0x50 + (160 + stackBytes) = 240 + stackBytes by omega]
  exact Entails.refl _

private theorem step_u64Load_val [CoreFmtPlacement] (ro : Bool) (valPtr v : BitVec 64)
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl09.base + 0x14#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = valPtr)
    (hnext : SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 0#5) v).setPC (coreFmtPl09.base + 0x18#64))
      (fmtRef64 ro valPtr v ∗ Fr) post oom) :
    SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt s
      (fmtRef64 ro valPtr v ∗ Fr) post oom := by
  cases ro
  · rw [fmtRef64_false] at hnext ⊢
    wp_step
    simpa [wp_norm, arm64_norm, bv_lin_norm] using hnext
  · rw [fmtRef64_true] at hnext ⊢
    wp_step
    simpa [wp_norm, arm64_norm, bv_lin_norm] using hnext

private theorem step_u64CallInner_bl [CoreFmtPlacement]
    {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl09.base + 0x2c#64) (hrun : s.status = .Running)
    (hnext : SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 30#5) (coreFmtPl09.base + 0x30#64)).setPC
        (coreFmtMultiLib.resolve coreFmtMpl u64FmtInnerIntSym))
      Pre post oom) :
    SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt s Pre post oom := by
  have hf := coreFmtPC09_rebase_fetch_0x2c coreFmtPl09.base (fun _ => none)
  exact SepWP.step_pure hpc hrun hf
    (by
      have hrho : coreFmtPl09.ρ u64FmtInnerIntSym =
          coreFmtMultiLib.resolve coreFmtMpl u64FmtInnerIntSym := rfl
      simp [wp_norm, arm64_norm, Reg.lr, hrho, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem step_u64CallPad_bl [CoreFmtPlacement]
    {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl09.base + 0x48#64) (hrun : s.status = .Running)
    (hnext : SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 30#5) (coreFmtPl09.base + 0x4c#64)).setPC
        (coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym))
      Pre post oom) :
    SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) tgt s Pre post oom := by
  have hf := coreFmtPC09_rebase_fetch_0x48 coreFmtPl09.base (fun _ => none)
  exact SepWP.step_pure hpc hrun hf
    (by
      have hrho : coreFmtPl09.ρ "<core::fmt::Formatter>::pad_integral" =
          coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym := rfl
      simp [wp_norm, arm64_norm, Reg.lr, hrho, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem u64DisplayFmt_gen_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    {keep padKeep : Nat → Bool}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hkeep3 : keep 3 = true) (hkeep9 : keep 9 = true)
    (hpad_sub : ∀ k, k < coreFmtMultiLib.blocks.length → padKeep k = true → keep k = true)
    (hnoext3 : LibBlockNoExtern coreFmtMultiLib mpl P 3)
    (hnoext9 : LibBlockNoExtern coreFmtMultiLib mpl P 9)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop}
    (hW : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (stackBytes : Nat) (lutAddr out vt : BitVec 64) (opts : FmtOptions)
    (hlut : lutAddr = coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym)
    (hPad : ∀ (f dsPtr : BitVec 64) (ds : List (BitVec 8)),
      subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
        (coreFmtMultiLib.withCodeLoadedWhere padKeep mpl
          (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
            f out vt opts true false dsPtr ds)))
    (sym : String) (hsym : coreFmtMultiLib.fnAddr mpl sym = mpl.base 9)
    (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl sym)
      (coreFmtMultiLib.withCodeLoadedWhere keep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [hsym]
  apply subroutine_ok_of_sepWPp_init
  intro ⟨st, f⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, u64DisplayFmtSpec] at hpre
  rw [sepConj_assoc (⌜_⌝ ∗ _), satisfies_sepConj_pure_assoc] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hno_alt⟩, hpre⟩
  have hm0 : s0.mem ⊨ stackFrameAt s0.sp (240 + stackBytes) ∗
      (fmtRef64 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
       formatterAt f out vt opts ∗ W st s0 ∗ R) :=
    Satisfies.mono (by sep_frame) hpre
  obtain ⟨_, hfr⟩ := frozen_of_codeLoaded (hcl 9 (by decide) hkeep9)
    (by simp only [MultiPlacedLib.blockProgram, PlacedLib.program, Obj.CodeBlock.length_patched]; decide)
  have hstk_lt : 240 + stackBytes < 2 ^ 64 := stackFrameAt_lt_pow64_of_frozen hfr hm0
  have hm1 := Satisfies.mono (sepConj_mono_left (u64Display_frame_unpack s0.sp stackBytes hstk_lt)) hm0
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨c0, c1, c2, c3, c4, c5, hm1⟩
  let sp1 := s0.sp - 0x50#64
  let bufBase := sp1 + 0x0c#64
  let ds := formatDecimalNat v.toNat
  have hds_bounds : 1 ≤ ds.length ∧ ds.length ≤ 20 := formatDecimalNat_length_bounds v.isLt
  let idx := 20 - ds.length
  let dsPtr := bufBase + BitVec.ofNat 64 idx
  let Saved : SepProp :=
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 24#64) ↦₆₄ c3) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))
  let P0 : SepProp :=
    fmtRef64 ro valPtr v ∗
    (((s0.sp - 48#64) ↦₆₄ c0) ∗ ((s0.sp - 40#64) ↦₆₄ c1) ∗ ((s0.sp - 32#64) ↦₆₄ c2) ∗
      ((s0.sp - 24#64) ↦₆₄ c3) ∗ ((s0.sp - 16#64) ↦₆₄ c4) ∗ ((s0.sp - 8#64) ↦₆₄ c5)) ∗
    ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 20 ∗ stackFrameAt sp1 0x10) ∗
    (formatterAt f out vt opts ∗ W st s0 ∗ memRegion sp1 12 ∗
      stackFrameAt (sp1 - 0x10#64) (144 + stackBytes))
  refine ⟨P0, Satisfies.mono (by dsimp only [P0, sp1, bufBase]; sep_frame) hm1, ?_⟩
  -- Segment A: block 9 prologue (+0x00..+0x28) and `bl _fmt_inner` (+0x2c).
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
    9 ⟨by decide, hkeep9⟩ hnoext9 coreFmtNoSvc0_09
    (mid := coreFmtMultiLib.resolve mpl u64FmtInnerIntSym) hcl
  intro s' hcpu_in
  change SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl09.base := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  have hx0' : s'.readReg64 (.gpr 0#5) = valPtr := (hcpu_in.readReg64 .x0).trans hx0
  have hx1' : s'.readReg64 (.gpr 1#5) = f := (hcpu_in.readReg64 .x1).trans hx1
  have hfp' : s'.readReg64 (.gpr 29#5) = s0.readReg64 Reg.fp := hcpu_in.readReg64 Reg.fp
  have hlr' : s'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
  have h19' : s'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu_in.readReg64 _
  have h20' : s'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu_in.readReg64 _
  have h21' : s'.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := hcpu_in.readReg64 _
  dsimp only [P0]
  iterate 5 wp_step
  apply step_u64Load_val ro valPtr v
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
  iterate 5 wp_step
  apply step_u64CallInner_bl
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun'])
  apply SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hrun'])
  intro sB hcpuA hclA hpsegA
  -- Segment B: block 3 `_fmt_inner`, returning to block 9 +0x30.
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
    3 ⟨by decide, hkeep3⟩ hnoext3 coreFmtNoSvc0_03
    (mid := coreFmtPl09.base + 0x30#64) hclA
  intro sB' hcpuB
  change SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) _ _ _ _
  have hpcB : sB'.pc = coreFmtPl03.base :=
    hcpuB.pc_eq.trans (hcpuA.pc_eq.trans (by
      simp [wp_norm, arm64_norm]; exact resolve_u64FmtInner hpl))
  have hrunB : sB'.status = .Running :=
    hcpuB.status_eq.trans (hcpuA.status_eq.trans (by simp [wp_norm, arm64_norm, hrun']))
  have hspB : sB'.sp = sp1 :=
    hcpuB.sp_eq.trans (hcpuA.sp_eq.trans (by simp [wp_norm, arm64_norm, sp1]))
  have hsp_alignB : sB'.spAligned = true := by
    rw [State.spAligned.eq_1, hspB]; exact s0.spAligned_sub 0x50#64 hsp_align
  have hlrB : sB'.readReg64 (.gpr 30#5) = coreFmtPl09.base + 0x30#64 :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  have hx0B : sB'.readReg64 (.gpr 0#5) = v :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  have hx1B : sB'.readReg64 (.gpr 1#5) = bufBase :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, bufBase, sp1, bv_lin_norm]))
  have hx2B : sB'.readReg64 (.gpr 2#5) = 20#64 :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  have hx19B : sB'.readReg64 (.gpr 19#5) = f :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  have hx20B : sB'.readReg64 (.gpr 20#5) = 20#64 :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  have hx21B : sB'.readReg64 (.gpr 21#5) = bufBase :=
    (hcpuB.readReg64 _).trans ((hcpuA.readReg64 _).trans
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, bufBase, sp1, bv_lin_norm]))
  have hcs22B : CalleeSaved22_28 s0 sB' :=
    CalleeSaved22_28.of_sameCpu_out hcpuB (CalleeSaved22_28.of_sameCpu_out hcpuA
      (CalleeSaved22_28.of_sameCpu_in hcpu_in
        (by simp (config := { decide := true }) [CalleeSaved22_28, wp_norm, arm64_norm])))
  have hlut_rho : coreFmtPl03.ρ "rust_core_fmt:.rodata..Lanon.203" = lutAddr := by
    rw [hlut, resolve_decDigitsLut]; rfl
  let F_B : SepProp :=
    fmtRef64 ro valPtr v ∗ Saved ∗ formatterAt f out vt opts ∗ W st s0 ∗ memRegion sp1 12 ∗
      stackFrameAt (sp1 - 0x10#64) (144 + stackBytes)
  refine SepWP.weaken_pre (by rw [hspB]; dsimp only [F_B, Saved]; sep_frame :
    _ ⊢ ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 20 ∗ stackFrameAt sB'.sp 0x10) ∗ F_B) ?_
  refine u64FmtInner_wp hlut_rho hpcB hrunB hsp_alignB hlrB hx0B hx1B hx2B ?_
  intro sC hpcC hrunC hsysC hspC hcsC hx0C
  rw [hspB]
  apply SepWP.done hpcC hrunC
  intro sC' hcpuC hclC hpsegB
  -- Segment C: block 9 +0x30..+0x44 and `bl pad_integral` (+0x48).
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
    9 ⟨by decide, hkeep9⟩ hnoext9 coreFmtNoSvc0_09
    (mid := coreFmtMultiLib.resolve mpl formatterPadIntegralSym) hclC
  intro sD hcpuD
  change SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) _ _ _ _
  have hpcD : sD.pc = coreFmtPl09.base + 0x30#64 := hcpuD.pc_eq.trans (hcpuC.pc_eq.trans hpcC)
  have hrunD : sD.status = .Running := hcpuD.status_eq.trans (hcpuC.status_eq.trans hrunC)
  have hspD : sD.sp = sp1 := hcpuD.sp_eq.trans (hcpuC.sp_eq.trans (hspC.trans hspB))
  have hx0D : sD.readReg64 (.gpr 0#5) = BitVec.ofNat 64 idx :=
    (hcpuD.readReg64 _).trans ((hcpuC.readReg64 _).trans hx0C)
  have hx19D : sD.readReg64 (.gpr 19#5) = f :=
    (hcpuD.readReg64 _).trans ((hcpuC.readReg64 _).trans (hcsC.1.trans hx19B))
  have hx20D : sD.readReg64 (.gpr 20#5) = 20#64 :=
    (hcpuD.readReg64 _).trans ((hcpuC.readReg64 _).trans (hcsC.2.1.trans hx20B))
  have hx21D : sD.readReg64 (.gpr 21#5) = bufBase :=
    (hcpuD.readReg64 _).trans ((hcpuC.readReg64 _).trans (hcsC.2.2.1.trans hx21B))
  have hcs22D : CalleeSaved22_28 s0 sD :=
    CalleeSaved22_28.of_sameCpu_out hcpuD
      (CalleeSaved22_28.of_sameCpu_out hcpuC (hcs22B.trans_cs hcsC))
  have hsub_len : 20#64 - BitVec.ofNat 64 idx = BitVec.ofNat 64 ds.length :=
    (bv_ofNat_sub_small (by dsimp only [idx]; omega)).trans
      (by dsimp only [idx]; congr 1; omega)
  iterate 6 wp_step
  apply step_u64CallPad_bl
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrunD])
  apply SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hrunD])
  intro s1 hcpu1 hcl1 hpsegC
  have hpseg01 : PureSegPreserved s0 s1 := (hpsegA.trans hpsegB).trans hpsegC
  have hsig01 : s1.sigActions = s0.sigActions :=
    hcpu1.sigActions_eq.trans ((by simp [wp_norm, arm64_norm] : _ = sD.sigActions).trans
      (hcpuD.sigActions_eq.trans (hcpuC.sigActions_eq.trans (hsysC.1.trans
        (hcpuB.sigActions_eq.trans (hcpuA.sigActions_eq.trans
          ((by simp [wp_norm, arm64_norm] : _ = s'.sigActions).trans hcpu_in.sigActions_eq)))))))
  have htp01 : s1.tpidrEl0 = s0.tpidrEl0 :=
    hcpu1.tpidrEl0_eq.trans ((by simp [wp_norm, arm64_norm] : _ = sD.tpidrEl0).trans
      (hcpuD.tpidrEl0_eq.trans (hcpuC.tpidrEl0_eq.trans (hsysC.2.trans
        (hcpuB.tpidrEl0_eq.trans (hcpuA.tpidrEl0_eq.trans
          ((by simp [wp_norm, arm64_norm] : _ = s'.tpidrEl0).trans hcpu_in.tpidrEl0_eq)))))))
  have hfw01 : FmtWriteFrame s0 s1 := fmtWriteFrame_of_pureSeg hpseg01 hsig01 htp01
  have hcs22_1 : CalleeSaved22_28 s0 s1 :=
    CalleeSaved22_28.of_sameCpu_out hcpu1
      (hcs22D.trans (by simp (config := { decide := true }) [CalleeSaved22_28, wp_norm, arm64_norm]))
  have hcl1_pad : coreFmtMultiLib.CodeLoadedWhere padKeep mpl s1.mem :=
    fun k hk hpk => hcl1 k hk (hpad_sub k hk hpk)
  have hsp1 : s1.sp = sp1 := hcpu1.sp_eq.trans (by simp [wp_norm, arm64_norm, hspD])
  have hsp1_align : s1.spAligned = true := by
    rw [State.spAligned.eq_1, hsp1]; exact s0.spAligned_sub 0x50#64 hsp_align
  let F_call : SepProp :=
    (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗ fmtRef64 ro valPtr v ∗ Saved ∗
      memRegion sp1 12
  refine sepWPp_call_keepsFrozen (hPad f dsPtr ds) (x := st) (F := F_call)
    (ret_pc := coreFmtPl09.base + 0x4c#64)
    (hpc := hcpu1.pc_eq)
    (hrun := hcpu1.status_eq.trans (by simp [wp_norm, arm64_norm, hrunD]))
    (hsp_align := hsp1_align)
    (hlr := (hcpu1.readReg64 Reg.lr).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
    (hpre := ?_) (hexit_eq := fun _ _ => rfl) (hpanic := ?_) (hnext := ?_) (hoom := ?_)
  · intro R' hm'
    have hx0_1 : s1.readReg64 .x0 = f :=
      (hcpu1.readReg64 .x0).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    have hx1_1 : s1.readReg32 .x1 = 1#32 :=
      (hcpu1.readReg32 .x1).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    have hx4_1 : s1.readReg64 .x4 = dsPtr :=
      (hcpu1.readReg64 .x4).trans
        (by simp (config := { decide := true }) [wp_norm, arm64_norm]; rfl)
    have hx5_1 : (s1.readReg64 .x5).toNat = ds.length := by
      have hx5_eq : s1.readReg64 .x5 = BitVec.ofNat 64 ds.length :=
        (hcpu1.readReg64 .x5).trans
          (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      rw [hx5_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ds.length < 2 ^ 64)]
    have hpure1 : s1.readReg64 .x0 = f ∧ s1.readReg32 .x1 = 1#32 ∧
        s1.readReg64 .x4 = dsPtr ∧ (s1.readReg64 .x5).toNat = ds.length ∧
        ds.length < 2 ^ 60 ∧ opts.flags.getLsbD 23 = false :=
      ⟨hx0_1, hx1_1, hx4_1, hx5_1, by omega, hno_alt⟩
    simp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec, fmtSrcBytes,
      Bool.false_eq_true, ↓reduceIte]
    dsimp only [F_call]
    rw [hsp1, pure_sepConj_of_true hpure1, sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl1_pad]
    refine Satisfies.mono ?_ hm'
    refine Entails.trans (by dsimp only [F_B, Saved]; sep_frame :
      _ ⊢ W st s0 ∗ ((stackFrameAt sp1 0x10 ∗ stackFrameAt (sp1 - 0x10#64) (144 + stackBytes)) ∗
        ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗ (dsPtr ↦ₛ ds) ∗
         fmtRef64 ro valPtr v ∗ Saved ∗ formatterAt f out vt opts ∗ memRegion sp1 12) ∗ R')) ?_
    refine Entails.trans (sepConj_mono (hW st s0 s1 hfw01)
      (sepConj_mono_left (u64Display_pad_frame_join sp1 stackBytes hstk_lt))) ?_
    sep_frame
  · intro sf _ ⟨R'', hpan⟩ hmf
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact allowPanic_panicked hpan.1 hmf
  · intro s2 hpc2 hrun2 hsp2 hcs12 hkf12
    have hcl2 := codeLoadedWhere_of_keepsFrozen hcl1 hkf12
    simp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec, fmtSrcBytes,
      Bool.false_eq_true, ↓reduceIte]
    apply sepWPp_exists_left; intro ok
    apply sepWPp_exists_left; intro st'
    rw [sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hw0_2, hops⟩
    -- Segment D: block 9 epilogue (+0x4c..+0x5c).
    apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
      9 ⟨by decide, hkeep9⟩ hnoext9 coreFmtNoSvc0_09 (mid := s0.readReg64 Reg.lr) hcl2
    intro s2' hcpu2
    change SepWP (coreFmtPC09.rebase coreFmtPl09.base (fun _ => none)) _ _ _ _
    have hpc2' : s2'.pc = coreFmtPl09.base + 0x4c#64 := hcpu2.pc_eq.trans hpc2
    have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun2
    have hsp2' : s2'.sp = s0.sp - 0x50#64 := hcpu2.sp_eq.trans (hsp2.trans hsp1)
    have hw0_2' : s2'.readReg32 .x0 = (if ok then 0#32 else 1#32) :=
      (hcpu2.readReg32 .x0).trans hw0_2
    refine SepWP.weaken_pre (by dsimp only [F_call]; rw [hsp1]; sep_frame :
      _ ⊢ Saved ∗ ((if ok then formatterAt f out vt opts else memRegion f 24) ∗
         (dsPtr ↦ₛ ds) ∗ W st' s2 ∗ stackFrameAt sp1 (160 + stackBytes) ∗
         (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗
         fmtRef64 ro valPtr v ∗ memRegion sp1 12)) ?_
    have he1 : (s0.sp - 0x50#64) + 64#64 = s0.sp - 16#64 := by simp [bv_lin_norm]
    have he2 : (s0.sp - 0x50#64) + 72#64 = s0.sp - 8#64 := by simp [bv_lin_norm]
    have he3 : (s0.sp - 0x50#64) + 48#64 = s0.sp - 32#64 := by simp [bv_lin_norm]
    have he4 : (s0.sp - 0x50#64) + 32#64 = s0.sp - 48#64 := by simp [bv_lin_norm]
    have he5 : (s0.sp - 0x50#64) + 40#64 = s0.sp - 40#64 := by simp [bv_lin_norm]
    have he6 : (s0.sp - 0x50#64) + 80#64 = s0.sp := by simp [bv_lin_norm]
    dsimp only [Saved]
    iterate 5 wp_step
    apply SepWP.done (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun2'])
    intro s3 hcpu3 _ hpseg3
    have hfw23 : FmtWriteFrame s2 s3 :=
      intFmtWriteFrame_of_seg hcpu2 hcpu3 hpseg3 ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    have hw0_3 : s3.readReg32 .x0 = (if ok then 0#32 else 1#32) :=
      (hcpu3.readReg32 .x0).trans
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hw0_2')
    have hsp3 : s3.sp = s0.sp := hcpu3.sp_eq.trans (by simp [wp_norm, arm64_norm])
    have hcs22_3 : CalleeSaved22_28 s0 s3 :=
      CalleeSaved22_28.of_sameCpu_out hcpu3
        ((CalleeSaved22_28.of_sameCpu_out hcpu2 (hcs22_1.trans_cs hcs12)).trans
          (by simp (config := { decide := true }) [CalleeSaved22_28, wp_norm, arm64_norm]))
    have hcs03 : CalleeSavedPreserved s0 s3 := by
      obtain ⟨h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs22_3
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, h22, h23, h24, h25, h26, h27, h28, ?_, hv⟩ <;>
        exact (hcpu3.readReg64 _).trans
          (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    apply SepWPp.done
      (hcpu3.pc_eq.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
      (hcpu3.status_eq.trans (by simp [wp_norm, arm64_norm, hrun2']))
    refine ⟨?_, hsp3, hcs03⟩
    intro hmf3
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, u64DisplayFmtSpec]
    refine Satisfies.mono ?_ hmf3
    refine Entails.sepExists_intro_frame ok ?_
    refine Entails.sepExists_intro_frame st' ?_
    rw [pure_sepConj_of_true ⟨hw0_3, hops⟩]
    apply sepConj_mono_left
    refine Entails.trans (by sep_frame :
      _ ⊢ ((((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 24#64) ↦₆₄ c3) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
           (memRegion sp1 12 ∗ memRegion bufBase idx ∗ (dsPtr ↦ₛ ds)) ∗
           stackFrameAt sp1 (160 + stackBytes)) ∗
          W st' s2 ∗ (fmtRef64 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
            (if ok then formatterAt f out vt opts else memRegion f 24))) ?_
    refine Entails.trans (sepConj_mono
      (u64Display_frame_repack s0.sp stackBytes hstk_lt _ _ _ _ _ _ ds hds_bounds.2)
      (sepConj_mono_left (hW st' s2 s3 hfw23))) ?_
    sep_frame
  · intro sf R' _ hoom
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec, u64DisplayFmtSpec] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

theorem u64DisplayFmt_of_padIntegral_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext3 : LibBlockNoExtern coreFmtMultiLib mpl P 3)
    (hnoext9 : LibBlockNoExtern coreFmtMultiLib mpl P 9)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop}
    (hW : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (stackBytes : Nat) (lutAddr out vt : BitVec 64) (opts : FmtOptions)
    (hlut : lutAddr = coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym)
    (hPad : ∀ (f dsPtr : BitVec 64) (ds : List (BitVec 8)),
      subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
        (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
          f out vt opts true false dsPtr ds))
    (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplaySelfKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  refine u64DisplayFmt_gen_ok (keep := u64DisplaySelfKeep) (padKeep := fun _ => false)
    hpl (by decide) (by decide) (fun _ _ h => Bool.noConfusion h) hnoext3 hnoext9 hW stackBytes
    lutAddr out vt opts hlut ?_ _ (fnAddr_u64Display hpl) ro valPtr v
  intro f dsPtr ds
  exact subroutine_ok_mono_entails (hPad f dsPtr ds)
    (fun _ _ => by dsimp only [MultiPlacedLib.withCodeLoadedWhere]; rw [sepConj_comm]; exact Entails.pure_left fun _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

theorem u64DisplayFmt_of_padIntegralWhere_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext3 : LibBlockNoExtern coreFmtMultiLib mpl P 3)
    (hnoext9 : LibBlockNoExtern coreFmtMultiLib mpl P 9)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop}
    (hW : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (stackBytes : Nat) (lutAddr out vt : BitVec 64) (opts : FmtOptions)
    (hlut : lutAddr = coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym)
    (hPad : ∀ (f dsPtr : BitVec 64) (ds : List (BitVec 8)),
      subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
        (coreFmtMultiLib.withCodeLoadedWhere padIntegralKeep mpl
          (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
            f out vt opts true false dsPtr ds)))
    (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplayKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) :=
  u64DisplayFmt_gen_ok hpl (by decide) (by decide)
    (fun k _ h => by simp [u64DisplayKeep, h]) hnoext3 hnoext9 hW stackBytes lutAddr out vt opts hlut
    hPad _ (fnAddr_u64Display hpl) ro valPtr v

theorem usizeDisplayFmt_of_padIntegral_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext3 : LibBlockNoExtern coreFmtMultiLib mpl P 3)
    (hnoext9 : LibBlockNoExtern coreFmtMultiLib mpl P 9)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop}
    (hW : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (stackBytes : Nat) (lutAddr out vt : BitVec 64) (opts : FmtOptions)
    (hlut : lutAddr = coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym)
    (hPad : ∀ (f dsPtr : BitVec 64) (ds : List (BitVec 8)),
      subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
        (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
          f out vt opts true false dsPtr ds))
    (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplaySelfKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  refine u64DisplayFmt_gen_ok (keep := u64DisplaySelfKeep) (padKeep := fun _ => false)
    hpl (by decide) (by decide) (fun _ _ h => Bool.noConfusion h) hnoext3 hnoext9 hW stackBytes
    lutAddr out vt opts hlut ?_ _ (fnAddr_usizeDisplay hpl) ro valPtr v
  intro f dsPtr ds
  exact subroutine_ok_mono_entails (hPad f dsPtr ds)
    (fun _ _ => by dsimp only [MultiPlacedLib.withCodeLoadedWhere]; rw [sepConj_comm]; exact Entails.pure_left fun _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

theorem usizeDisplayFmt_of_padIntegralWhere_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext3 : LibBlockNoExtern coreFmtMultiLib mpl P 3)
    (hnoext9 : LibBlockNoExtern coreFmtMultiLib mpl P 9)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop}
    (hW : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    (stackBytes : Nat) (lutAddr out vt : BitVec 64) (opts : FmtOptions)
    (hlut : lutAddr = coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym)
    (hPad : ∀ (f dsPtr : BitVec 64) (ds : List (BitVec 8)),
      subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
        (coreFmtMultiLib.withCodeLoadedWhere padIntegralKeep mpl
          (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
            f out vt opts true false dsPtr ds)))
    (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplayKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) :=
  u64DisplayFmt_gen_ok hpl (by decide) (by decide)
    (fun k _ h => by simp [u64DisplayKeep, h]) hnoext3 hnoext9 hW stackBytes lutAddr out vt opts hlut
    hPad _ (fnAddr_usizeDisplay hpl) ro valPtr v

/-- Lifts `u64DisplayFmtSpec` to a `core::fmt::write` argument callback specification
(`fmtArgCallSpec`) when `W` frames `fmtRef64` and `DEC_DIGITS_LUT` around `W_inner` and
`opts.flags.getLsbD 23 = false`. -/
theorem u64DisplayFmt_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {lutAddr out vt valPtr fmtFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {v : BitVec 64}
    (hfmt : subroutine_ok P fmtFn
      (u64DisplayFmtSpec W_inner StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v))
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : 240 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef64 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗ W_inner st s := by intros; ac_rfl) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) :=
  IntDisplayAux.intDisplay_fmtArg_ok (frameBytes := 240 + stackBytes)
    (F_ref := fmtRef64 ro valPtr v) (ds := formatDecimalNat v.toNat) hfmt hno_alt hstep hpanic hoom hstack hW

end VerifiedLibraries.RustStd.CoreFmt
