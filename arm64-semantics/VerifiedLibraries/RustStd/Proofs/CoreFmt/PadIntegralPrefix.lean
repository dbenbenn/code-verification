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
public import ProofLib.SepLogic.Fresh

/-!
# `pad_integral` Algebra and `write_prefix` Proof

Proves sign-word encoding and padding-sequence decomposition lemmas for `pad_integral`, together
with `writePrefix_ok` for `<core::fmt::Formatter>::pad_integral::write_prefix` (`coreFmtMultiLib`
block `5`) when `x3 = 0`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd.CoreFmt

/-! ## Pure Sign Encoding, Option Algebra, and Stack-Frame Size Extraction -/

/-- `Option<char>` niche word passed in `w2` to `pad_integral::write_prefix`: `0xffffffff` for
    `None`, otherwise `Some(c)`. -/
def writePrefixSignOp (signWord : BitVec 32) : List FmtOp :=
  if signWord = 0xffffffff#32 then [] else [.char signWord]

/-- Sign word computed at `pad_integral+0x038..+0x054` into `w24`. -/
def fmtSignWord (opts : FmtOptions) (isNonneg : Bool) : BitVec 32 :=
  if isNonneg then
    if opts.flags.getLsbD 21 then 0x2b#32 else 0xffffffff#32
  else
    0x2d#32

theorem writePrefixSignOp_fmtSignWord (opts : FmtOptions) (isNonneg : Bool) :
    writePrefixSignOp (fmtSignWord opts isNonneg) = fmtSignOp opts isNonneg := by
  unfold writePrefixSignOp fmtSignWord fmtSignOp
  generalize opts.flags.getLsbD 21 = b
  cases isNonneg <;> cases b <;> decide

theorem fmtSignOp_length_le_one (opts : FmtOptions) (isNonneg : Bool) :
    (fmtSignOp opts isNonneg).length ≤ 1 := by
  unfold fmtSignOp
  cases isNonneg <;> cases opts.flags.getLsbD 21 <;> decide

theorem fmtPadSplit_zero (opts : FmtOptions) :
    fmtPadSplit opts 0 = (0, 0) := by
  unfold fmtPadSplit
  split <;> rfl

theorem fmtPadSplit_bounds (opts : FmtOptions) (pad : Nat) :
    (fmtPadSplit opts pad).1 ≤ pad ∧
      (fmtPadSplit opts pad).2 = pad - (fmtPadSplit opts pad).1 := by
  unfold fmtPadSplit
  split <;> omega

theorem padIntegralNoAltOps_of_pad_zero (opts : FmtOptions) (isNonneg : Bool)
    (ds : List (BitVec 8))
    (hle : opts.width.toNat ≤ (fmtSignOp opts isNonneg).length + ds.length) :
    padIntegralNoAltOps opts isNonneg ds = fmtSignOp opts isNonneg ++ [.str ds] := by
  unfold padIntegralNoAltOps
  have hpad : opts.width.toNat - ((fmtSignOp opts isNonneg).length + ds.length) = 0 := by omega
  simp only [hpad]
  cases opts.flags.getLsbD 24
  · simp [fmtPadSplit_zero]
  · simp

theorem padIntegralNoAltOps_of_bit24 (opts : FmtOptions) (isNonneg : Bool)
    (ds : List (BitVec 8)) (h24 : opts.flags.getLsbD 24 = true) :
    padIntegralNoAltOps opts isNonneg ds =
      fmtSignOp opts isNonneg ++
        (List.replicate (opts.width.toNat - ((fmtSignOp opts isNonneg).length + ds.length))
          (.char 0x30#32) ++ [.str ds]) := by
  unfold padIntegralNoAltOps
  rw [h24]
  simp [List.append_assoc]

theorem padIntegralNoAltOps_of_not_bit24 (opts : FmtOptions) (isNonneg : Bool)
    (ds : List (BitVec 8)) (h24 : opts.flags.getLsbD 24 = false) :
    let pad := opts.width.toNat - ((fmtSignOp opts isNonneg).length + ds.length)
    let split := fmtPadSplit opts pad
    padIntegralNoAltOps opts isNonneg ds =
      List.replicate split.1 (.char (fmtFillChar opts)) ++
        (fmtSignOp opts isNonneg ++
          ([.str ds] ++ List.replicate split.2 (.char (fmtFillChar opts)))) := by
  unfold padIntegralNoAltOps
  rw [h24]
  simp [List.append_assoc]

private theorem stackFrameSlotsCont_left (sp : BitVec 64) (k : Nat) :
    ∀ (n : Nat) (X : SepProp),
      stackFrameSlotsCont sp k n (fun rest => X ∗ rest) = X ∗ stackFrameSlotsFrom sp k n := by
  intro n
  induction n with
  | zero =>
    intro X; rfl
  | succ m ih =>
    cases m with
    | zero =>
      intro X
      simp only [stackFrameSlotsCont, stackFrameSlotsFrom, sepExists_sepConj_right]
    | succ n =>
      intro X
      have hstep : ∀ v : BitVec 64,
          stackFrameSlotsCont sp k (n + 1)
            (fun rest => X ∗ (((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗ rest)) =
          (X ∗ ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v)) ∗
            stackFrameSlotsFrom sp k (n + 1) := by
        intro v
        have hfun :
            (fun rest => X ∗ (((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗ rest)) =
            (fun rest => (X ∗ ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v)) ∗ rest) :=
          funext fun rest => (sepConj_assoc _ _ _).symm
        rw [hfun]
        exact ih _
      have hstep2 : ∀ v : BitVec 64,
          stackFrameSlotsCont sp k (n + 1)
            (fun rest => ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗ rest) =
          ((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗
            stackFrameSlotsFrom sp k (n + 1) :=
        fun v => ih _
      have heq : k + (n + 1) + 1 = k + n + 2 := by omega
      conv => lhs; unfold stackFrameSlotsCont; simp only [heq, hstep]
      conv => rhs; arg 2; unfold stackFrameSlotsFrom stackFrameSlotsCont; simp only [heq, hstep2]
      simp only [sepConj_assoc, sepExists_sepConj_right]

private theorem stackFrameSlotsFrom_succ (sp : BitVec 64) (k n : Nat) :
    stackFrameSlotsFrom sp k (n + 1) =
      ∃∗ v : BitVec 64,
        ((sp - BitVec.ofNat 64 ((k + n + 1) * 8)) ↦₆₄ v) ∗ stackFrameSlotsFrom sp k n := by
  cases n with
  | zero =>
    simp [stackFrameSlotsFrom, stackFrameSlotsCont]
  | succ m =>
    conv => lhs; unfold stackFrameSlotsFrom stackFrameSlotsCont
    have h := fun v => stackFrameSlotsCont_left sp k (m + 1)
      ((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v)
    have heq : k + (m + 1) + 1 = k + m + 2 := by omega
    simp only [heq, h]

private theorem stackFrameSlotsFrom_entails_prefix (sp : BitVec 64) (k m : Nat) :
    ∀ d : Nat, stackFrameSlotsFrom sp k (m + d) ⊢ stackFrameSlotsFrom sp k m ∗ anyHeap := by
  intro d
  induction d with
  | zero =>
    rw [Nat.add_zero]
    conv => lhs; rw [← sepConj_emp (stackFrameSlotsFrom sp k m)]
    exact sepConj_mono_right (entails_anyHeap emp)
  | succ d ih =>
    rw [show m + (d + 1) = (m + d) + 1 by omega, stackFrameSlotsFrom_succ]
    apply Entails.sepExists_elim; intro v
    refine Entails.trans (sepConj_mono_right ih) ?_
    rw [sepConj_comm _ (stackFrameSlotsFrom sp k m ∗ anyHeap), sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

private theorem not_inRegion_of_satisfies_pointsTo64 {m : Memory} {a v p : BitVec 64} {n : Nat}
    {R : SepProp} (hm : m ⊨ (a ↦₆₄ v) ∗ (memRegion p n ∗ R)) :
    ¬ InRegion p n a := by
  have hina : InRegion a 8 a := by unfold InRegion; rw [BitVec.sub_self]; decide
  have hent : ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) ⊢
      ⌜¬ InRegion p n a⌝ ∗ ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) :=
    Entails.extract_heap_fact fun _ hhp => pointsTo64_byte_not_inRegion hhp hina
  have hm' := Satisfies.mono hent hm
  rw [satisfies_pure_sepConj] at hm'
  exact hm'.1

private theorem stackFrameSlotsFrom_le_two_pow_61 {m : Memory} {sp : BitVec 64} {s : Nat}
    {R : SepProp} (hm : m ⊨ stackFrameSlotsFrom sp 0 s ∗ R) :
    s ≤ 2 ^ 61 := by
  refine Classical.byContradiction fun hgt => ?_
  have hs_eq : s = (2 ^ 61 + 1) + (s - (2 ^ 61 + 1)) := by omega
  rw [hs_eq] at hm
  have hm1 := Satisfies.mono
    (sepConj_mono_left (stackFrameSlotsFrom_entails_prefix sp 0 (2 ^ 61 + 1) _)) hm
  rw [stackFrameSlotsFrom_succ sp 0 (2 ^ 61), sepExists_sepConj_left, sepExists_sepConj_left,
    satisfies_sepExists] at hm1
  rcases hm1 with ⟨vTop, hm1⟩
  have h261 : (2 ^ 61 : Nat) = 1 + (2 ^ 61 - 1) := by decide
  rw [h261] at hm1
  have hm2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
      (stackFrameSlotsFrom_entails_prefix sp 0 1 (2 ^ 61 - 1))))) hm1
  rw [stackFrameSlotsFrom_succ sp 0 0] at hm2
  simp only [stackFrameSlotsFrom, stackFrameSlotsCont, sepConj_emp, Nat.zero_add, Nat.one_mul,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm2
  rcases hm2 with ⟨vBot, hm2⟩
  have hoff : BitVec.ofNat 64 ((0 + 2 ^ 61 + 1) * 8) = 8#64 := by decide
  have hoff0 : BitVec.ofNat 64 8 = 8#64 := rfl
  rw [hoff, hoff0] at hm2
  have hm3 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
      (sepConj_mono_left (pointsTo64_entails_memRegion (sp - 8#64) vBot))))) hm2
  have hac :
      ((((sp - 8#64) ↦₆₄ vTop) ∗ (memRegion (sp - 8#64) 8 ∗ anyHeap)) ∗ anyHeap) ∗ R =
      ((sp - 8#64) ↦₆₄ vTop) ∗ (memRegion (sp - 8#64) 8 ∗ (anyHeap ∗ anyHeap ∗ R)) := by
    ac_rfl
  rw [hac] at hm3
  have hnot := not_inRegion_of_satisfies_pointsTo64 hm3
  apply hnot
  unfold InRegion; rw [BitVec.sub_self]; decide

theorem stackFrameAt_le_of_pointsTo64 {m : Memory} {a v sp : BitVec 64} {n : Nat} {R : SepProp}
    (hm : m ⊨ (a ↦₆₄ v) ∗ (stackFrameAt sp n ∗ R)) :
    n ≤ 2 ^ 64 := by
  unfold stackFrameAt at hm
  by_cases h0 : n = 0
  · omega
  by_cases h8 : n % 8 = 0
  · simp only [h0, h8, beq_iff_eq, ite_false, ite_true] at hm
    have hm' : m ⊨ stackFrameSlotsFrom sp 0 (n / 8) ∗ ((a ↦₆₄ v) ∗ R) := by
      have hac : (a ↦₆₄ v) ∗ (stackFrameSlotsFrom sp 0 (n / 8) ∗ R) =
          stackFrameSlotsFrom sp 0 (n / 8) ∗ ((a ↦₆₄ v) ∗ R) := by ac_rfl
      rwa [hac] at hm
    have hs := stackFrameSlotsFrom_le_two_pow_61 hm'
    omega
  · simp only [h0, h8, beq_iff_eq, ite_false] at hm
    have hnot := not_inRegion_of_satisfies_pointsTo64 hm
    unfold InRegion at hnot
    have hlt := (a - (sp - BitVec.ofNat 64 n)).isLt
    omega

/-! ## `SepWPp` Call Helper and `pad_integral::write_prefix` (`coreFmtMultiLib` Block `5`) -/

namespace PadIntegralProof

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

end PadIntegralProof

open PadIntegralProof

theorem sepWPp_seq_where {lib : MultiPlacedLib} {keep : Nat → Bool} {mpl : MultiPlacement}
    {P : Program} {mid_pc ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoadedWhere keep mpl s.mem)
    (h1 : SepWPp P mid_pc s Pre
      (fun sm Pm => lib.CodeLoadedWhere keep mpl sm.mem → SepWPp P ret sm Pm Q Qp oom)
      Qp oom) :
    SepWPp P ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨_hpcm, _hrunm, Pm, hmm, hcont⟩ | hpan | hoom
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont (hsteps1.codeLoadedWhere hcl) R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inr hoom)⟩

theorem call_wpp_where {α : Type} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {P : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α}
    {x : α} {s : State} {Pre F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok P entry spec)
    (hcl : lib.CodeLoadedWhere keep mpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      lib.CodeLoadedWhere keep mpl sf.mem →
      SepWPp P ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R')) :
    SepWPp P ret s Pre Q Qp oom := by
  refine sepWPp_seq_where (mid_pc := ret_pc) hcl ?_
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic ?_ hoom
  intro sf hpcf hrunf hspf hcsf
  exact SepWPp.done hpcf hrunf (fun hcl_sf => hnext sf hpcf hrunf hspf hcsf hcl_sf)

private theorem spAligned_to_sub_48_and {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 48#64) &&& 15#64 = 0#64 := by
  have h0 : (sp0 &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  have hm2 : ((sp0 - 48#64) &&& 15#64).toNat = (sp0 - 48#64).toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod (sp0 - 48#64).toNat 4
  rw [hm1] at h0
  apply BitVec.eq_of_toNat_eq
  rw [hm2, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := sp0.isLt
  omega

private theorem stackFrameAt_48_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 48 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
        ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
        ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5) := by
  simp only [arm64_norm]

private def wpSavedSlots (sp0 : BitVec 64) (s0 : State) (ret_pc : BitVec 64) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((sp0 - 40#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem wpSavedSlots_fold (sp0 : BitVec 64) (s0 : State) (ret_pc : BitVec 64) :
    wpSavedSlots sp0 s0 ret_pc ⊢ stackFrameAt sp0 48 := by
  rw [stackFrameAt_48_unpack sp0]
  dsimp only [wpSavedSlots]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _))))))

/-- Contract for `<core::fmt::Formatter>::pad_integral::write_prefix` (`coreFmtMultiLib` block `5`)
    when `x3 = 0` (`pfx_ptr = 0`, skipping any alternate prefix slice). -/
def writePrefixSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (signWord : BitVec 32) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = vt ∧
      s.readReg32 .x2 = signWord ∧ s.readReg64 .x3 = 0#64 ∧
      48 + stackBytes ≤ 2 ^ 64⌝ ∗
      W st s ∗ stackFrameAt s.sp (48 + stackBytes)
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep (writePrefixSignOp signWord) st ok st'⌝ ∗
        W st' sf ∗ stackFrameAt s0.sp (48 + stackBytes)
  onPanic := fun st _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic (writePrefixSignOp signWord) st sf⌝ ∗ anyHeap
  onOom := fun st _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom (writePrefixSignOp signWord) st sf⌝

private theorem signWord_add_one_ne_zero {signWord : BitVec 32} (hne : signWord ≠ 0xffffffff#32) :
    signWord + 1#32 ≠ 0#32 := by
  bv_omega

private theorem signWord_add_one_toNat_ne_zero {signWord : BitVec 32}
    (hne : signWord ≠ 0xffffffff#32) :
    (signWord + 1#32).toNat ≠ 0 := by
  intro h0
  exact signWord_add_one_ne_zero hne (BitVec.eq_of_toNat_eq h0)

section WritePrefixProof
arm64_proof_prelude
set_option linter.literalFetch false

private theorem sepWPp_seg_block5 [CoreFmtPlacement] {keep : Nat → Bool}
    (hkeep5 : keep 5 = true)
    {P : Program} (hext5 : LibBlockNoExtern coreFmtMultiLib coreFmtMpl P 5)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (coreFmtPC05.rebase coreFmtPl05.base (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' →
            coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl sm.mem →
            PureSegPreserved s sm →
            SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom :=
  sepWPp_seg_lib_block_pureWhere 5 ⟨by decide, hkeep5⟩ hext5 coreFmtNoSvc0_05 hcl hseg

namespace PadIntegralProof

theorem sepWPp_seg_block0 [CoreFmtPlacement] {keep : Nat → Bool}
    (hkeep0 : keep 0 = true)
    {P : Program} (hext0 : LibBlockNoExtern coreFmtMultiLib coreFmtMpl P 0)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (coreFmtPC00.rebase coreFmtPl00.base (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' →
            coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl sm.mem →
            PureSegPreserved s sm →
            SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom :=
  sepWPp_seg_lib_block_pureWhere 0 ⟨by decide, hkeep0⟩ hext0 coreFmtNoSvc0_00 hcl hseg

end PadIntegralProof

open PadIntegralProof

private theorem writePrefix_epilogue_wpp [CoreFmtPlacement] {σ : Type} {keep : Nat → Bool}
    (hkeep5 : keep 5 = true)
    {P : Program} (hext5 : LibBlockNoExtern coreFmtMultiLib coreFmtMpl P 5)
    {W : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {stackBytes : Nat}
    {out vt wcFn : BitVec 64} {signWord : BitVec 32}
    (hw : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s')
    {st st' : σ} {ok : Bool} {s0 sf1 : State} {R : SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl sf1.mem)
    (hpc : sf1.pc = coreFmtPl05.base + 56#64)
    (hrun : sf1.status = .Running)
    (hsp : sf1.sp = s0.sp - 48#64)
    (hsp_al : sf1.spAligned = true)
    (hstack : 48 + stackBytes ≤ 2 ^ 64)
    (hw0 : sf1.readReg32 .x0 = if ok then 0#32 else 1#32)
    (hx20 : sf1.readReg64 (.gpr 20#5) = 0#64)
    (hx23 : sf1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5))
    (hx24 : sf1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5))
    (hx25 : sf1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5))
    (hx26 : sf1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27 : sf1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hx28 : sf1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs sf1 = calleeSavedVRegs s0)
    (hrun_op : FmtOpsRun StrStep CharStep (writePrefixSignOp signWord) st ok st') :
    SepWPp P (s0.readReg64 Reg.lr) sf1
      (W st' sf1 ∗ stackFrameAt (s0.sp - 48#64) stackBytes ∗
        ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord).post
            st s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord).onPanic
            st s0 sf ∗ R))
      (fun sf =>
        (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord).onOom st s0 sf) := by
  apply sepWPp_seg_block5 hkeep5 hext5 hcl (mid := s0.readReg64 Reg.lr)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl05.base + 56#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = s0.sp - 48#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  have hw0' : s'.readReg32 .x0 = if ok then 0#32 else 1#32 := (hcpu_in.readReg32 .x0).trans hw0
  have hx20' : s'.readReg64 (.gpr 20#5) = 0#64 := (hcpu_in.readReg64 _).trans hx20
  dsimp only [wpSavedSlots]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  have hw_drop : ∀ (sm : State), FmtWriteFrame sf1 sm →
      ∀ hm : sm.mem ⊨ (W st' sf1 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
        (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
           (((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
             (((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
              (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
               ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))))))))) ∗ R,
      (sm.readReg32 .x0 = if ok then 0#32 else 1#32) →
      sm.mem ⊨ (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord).post
        st s0 sm ∗ R := by
    intro sm hframe hm hw0f
    dsimp only [writePrefixSpec]
    have hfold := wpSavedSlots_fold s0.sp s0 (s0.readReg64 Reg.lr)
    have hent :
        W st' sf1 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
          (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr))) ⊢
        ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ (W st' sm ∗ stackFrameAt s0.sp (48 + stackBytes)) := by
      rw [stackFrameAt_split s0.sp 48 stackBytes hstack]
      have hac :
          W st' sf1 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
            (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr))) =
          ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗
            (W st' sf1 ∗ (wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr) ∗
              stackFrameAt (s0.sp - 48#64) stackBytes)) := by ac_rfl
      rw [hac]
      exact sepConj_mono_right (sepConj_mono (hw st' sf1 sm hframe) (sepConj_mono_left hfold))
    dsimp only [wpSavedSlots] at hent
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hm
    rw [sepConj_assoc] at hm1
    refine Satisfies.mono (sepConj_mono_left ?_) (Satisfies.drop_left hm1)
    refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
    rw [pure_sepConj_of_true ⟨hw0f, hrun_op⟩]
    exact Entails.refl _
  cases ok <;> {
    simp [arm64_norm] at hw0'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out _hcl_sm hpseg => ?_
    have hpcf : sm.pc = s0.readReg64 Reg.lr := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
    have hrunf : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
    have hspf : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have hcsf : CalleeSavedPreserved s0 sm := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_out.readReg64]; simp [arm64_norm]
      · rw [hcpu_out.readReg64]; simp [arm64_norm]
      · rw [hcpu_out.readReg64]; simp [arm64_norm]
      · rw [hcpu_out.readReg64]; simp [arm64_norm]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx23]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx24]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx25]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx26]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27]
      · rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28]
      · rw [hcpu_out.readReg64]; simp [arm64_norm]
      · rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
    have hframe : FmtWriteFrame sf1 sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    exact SepWPp.done hpcf hrunf
      ⟨fun hm => hw_drop sm hframe hm (by rw [hcpu_out.readReg32 .x0]; simp [arm64_norm]),
       hspf, hcsf⟩
  }

/-- `<core::fmt::Formatter>::pad_integral::write_prefix` (`coreFmtMultiLib` block `5`) satisfies
    `writePrefixSpec` when `x3 = 0` (`pfx_ptr = 0`), under block-local hook freedom on block `5`. -/
theorem writePrefix_ok {σ : Type} (P : Program) (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (mpl : Obj.MultiPlacement) (hpl : coreFmtMultiLib.Placeable mpl)
    {keep : Nat → Bool} (hkeep5 : keep 5 = true)
    (hext5 : LibBlockNoExtern coreFmtMultiLib mpl P 5)
    (out vt wsFn wcFn : BitVec 64) (signWord : BitVec 32)
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl writePrefixIntSym)
      (coreFmtMultiLib.withCodeLoadedWhere keep mpl
        (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_writePrefix hpl, show mpl = coreFmtMpl from rfl]
  apply subroutine_ok_of_sepWPp_init
  intro st R s0 hpc hrun hpre hsp_al
  have hpc0 : s0.pc = coreFmtPl05.base := hpc
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec] at hpre
  rw [sepConj_comm _ ⌜coreFmtMultiLib.CodeLoadedWhere keep coreFmtMpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hw2, hx3, hstack⟩, hpre⟩
  rw [stackFrameAt_split s0.sp 48 stackBytes hstack, stackFrameAt_48_unpack s0.sp] at hpre
  have hpre_ex :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
          ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
          ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
          ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
          (W st s0 ∗ stackFrameAt (s0.sp - 48#64) stackBytes ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v0, v1, v2, v3, v4, v5, hpre_slots⟩
  by_cases hnone : signWord = 0xffffffff#32
  · refine ⟨W st s0 ∗ stackFrameAt (s0.sp - 48#64) stackBytes ∗
        (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
         ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
         ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)),
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_slots, ?_⟩
    apply sepWPp_seg_block5 hkeep5 hext5 hcl (mid := s0.readReg64 Reg.lr)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl05.base + 0#64 :=
      (hcpu_in.pc_eq.trans hpc0).trans (BitVec.add_zero _).symm
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx0' : s'.readReg64 .x0 = out := (hcpu_in.readReg64 .x0).trans hx0
    have hx1' : s'.readReg64 .x1 = vt := (hcpu_in.readReg64 .x1).trans hx1
    have hw2' : s'.readReg32 .x2 = 0xffffffff#32 :=
      (hcpu_in.readReg32 .x2).trans (hw2.trans hnone)
    have hx3' : s'.readReg64 .x3 = 0#64 := (hcpu_in.readReg64 .x3).trans hx3
    simp [arm64_norm] at hw2' hx3'
    wp_conv_pre => simp only [sepConj_assoc]
    clear hpc hpc0
    wp_sym_steps
    refine SepWP.done (by simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by simpa [arm64_norm] using hrun') fun sm hcpu_out _hcl_sm hpseg => ?_
    have hpcf : sm.pc = s0.readReg64 Reg.lr := by
      rw [hcpu_out.pc_eq]; simpa [arm64_norm] using (hcpu_in.readReg64 Reg.lr)
    have hrunf : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
    have hspf : sm.sp = s0.sp := by rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have hw0f : sm.readReg32 .x0 = 0#32 := by rw [hcpu_out.readReg32 .x0]; simp [arm64_norm]
    have hcsf : CalleeSavedPreserved s0 sm := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs⟩ <;>
        (rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _)
    have hframe : FmtWriteFrame s0 sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine SepWPp.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec]
    have hfold : wpSavedSlots s0.sp s' (s'.readReg64 Reg.lr) ⊢ stackFrameAt s0.sp 48 := by
      dsimp only [wpSavedSlots]; simp only [hcpu_in.readReg64]
      exact wpSavedSlots_fold s0.sp s0 (s0.readReg64 Reg.lr)
    have hrun_op : FmtOpsRun StrStep CharStep (writePrefixSignOp signWord) st true st := by
      rw [hnone]; exact .nil st
    have hent :
        W st s0 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
          wpSavedSlots s0.sp s' (s'.readReg64 Reg.lr)) ⊢
        (writePrefixSpec W StrStep CharStep Panic Oom stackBytes out vt signWord).post st s0 sm := by
      dsimp only [writePrefixSpec]
      refine Entails.trans (Q := W st sm ∗ stackFrameAt s0.sp (48 + stackBytes)) ?_
        (Entails.sepExists_right true (Entails.sepExists_right st
          (by rw [pure_sepConj_of_true ⟨hw0f, hrun_op⟩]; exact Entails.refl _)))
      rw [stackFrameAt_split s0.sp 48 stackBytes hstack]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (hw.transport st s0 sm hframe) (sepConj_mono_left hfold))
    dsimp only [wpSavedSlots] at hent
    exact Satisfies.mono (sepConj_mono_left hent) hm
  ·
    have hpre_wc :
        s0.mem ⊨
          (W st s0 ∗ stackFrameAt (s0.sp - 48#64) stackBytes ∗
            ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗
            (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
             ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
             ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5))) ∗ R := by
      have hw_dup : W st s0 ⊢ ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ W st s0 :=
        Entails.of_eq (hw.slots st s0)
      have hpre_slots' :=
        Satisfies.mono (sepConj_mono_right (sepConj_mono_left hw_dup)) hpre_slots
      have hac :
          (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
           ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
           ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
            ((((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ W st s0) ∗
              stackFrameAt (s0.sp - 48#64) stackBytes ∗ R) =
          ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗
            ((W st s0 ∗ stackFrameAt (s0.sp - 48#64) stackBytes ∗
              ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗
              (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
               ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
               ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5))) ∗ R) := by
        ac_rfl
      rw [hac] at hpre_slots'
      exact Satisfies.drop_left hpre_slots'
    refine ⟨_, hpre_wc, ?_⟩
    have hsign_eq : writePrefixSignOp signWord = [.char signWord] := by
      unfold writePrefixSignOp; simp [hnone]
    have hne1 : signWord + 1#32 ≠ 0#32 := signWord_add_one_ne_zero hnone
    have hne2 : (signWord + 1#32).toNat ≠ 0 := signWord_add_one_toNat_ne_zero hnone
    have hne3 : (signWord.toNat + 1) % 4294967296 ≠ 0 := by
      simpa [BitVec.toNat_add] using hne2
    apply sepWPp_seg_block5 hkeep5 hext5 hcl (mid := wcFn)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl05.base + 0#64 :=
      (hcpu_in.pc_eq.trans hpc0).trans (BitVec.add_zero _).symm
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx0' : s'.readReg64 .x0 = out := (hcpu_in.readReg64 .x0).trans hx0
    have hx1' : s'.readReg64 .x1 = vt := (hcpu_in.readReg64 .x1).trans hx1
    have hw2' : s'.readReg32 .x2 = signWord := (hcpu_in.readReg32 .x2).trans hw2
    have hx3' : s'.readReg64 .x3 = 0#64 := (hcpu_in.readReg64 .x3).trans hx3
    simp [arm64_norm] at hw2' hx3'
    wp_conv_pre => simp only [sepConj_assoc]
    clear hpc hpc0
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hpc_sm : sm.pc = wcFn := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
    have hrun_sm : sm.status = .Running := by
      rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
    have hsp_sm : sm.sp = s0.sp - 48#64 := by
      rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have hsp_al_sm : sm.spAligned = true := by
      have h0 : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_al
      simp only [State.spAligned, hsp_sm, spAligned_to_sub_48_and h0, beq_self_eq_true]
    have hlr_sm : sm.readReg64 Reg.lr = coreFmtPl05.base + 56#64 := by
      rw [hcpu_out.readReg64 Reg.lr]; simp [arm64_norm]
    have hx0_sm : sm.readReg64 .x0 = out := by
      rw [hcpu_out.readReg64 .x0]; simp [arm64_norm]
    have hw1_sm : sm.readReg32 .x1 = signWord := by
      rw [hcpu_out.readReg32 .x1]; simp [arm64_norm]
    have hx20_sm : sm.readReg64 (.gpr 20#5) = 0#64 := by
      rw [hcpu_out.readReg64]; simp [arm64_norm]
    have hx23_sm : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hx24_sm : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hx25_sm : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hx26_sm : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hx27_sm : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hx28_sm : sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 _
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs
    have hframe_sm : FmtWriteFrame s0 sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    have hslots_eq :
        (((s0.sp - 48#64) ↦₆₄ s'.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 40#64) ↦₆₄ s'.readReg64 Reg.lr) ∗
          (((s0.sp - 32#64) ↦₆₄ s'.readReg64 (.gpr 22#5)) ∗
           (((s0.sp - 24#64) ↦₆₄ s'.readReg64 (.gpr 21#5)) ∗
            (((s0.sp - 16#64) ↦₆₄ s'.readReg64 (.gpr 20#5)) ∗
             ((s0.sp - 8#64) ↦₆₄ s'.readReg64 (.gpr 19#5))))))) =
        wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr) := by
      dsimp only [wpSavedSlots]
      simp only [hcpu_in.readReg64]
    refine call_wpp_where
      (F := ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr))
      (x := st) (hw.write_char signWord) hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
      ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [fmtWriterCharSpec]
      rw [hsp_sm, pure_sepConj_of_true ⟨hx0_sm, hw1_sm⟩]
      have hent :
          (W st s0 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
            (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗
              (((s0.sp - 48#64) ↦₆₄ s'.readReg64 (.gpr 29#5)) ∗
               (((s0.sp - 40#64) ↦₆₄ s'.readReg64 Reg.lr) ∗
                (((s0.sp - 32#64) ↦₆₄ s'.readReg64 (.gpr 22#5)) ∗
                 (((s0.sp - 24#64) ↦₆₄ s'.readReg64 (.gpr 21#5)) ∗
                  (((s0.sp - 16#64) ↦₆₄ s'.readReg64 (.gpr 20#5)) ∗
                   ((s0.sp - 8#64) ↦₆₄ s'.readReg64 (.gpr 19#5)))))))))) ∗ R' ⊢
          (W st sm ∗ stackFrameAt (s0.sp - 48#64) stackBytes) ∗
            ((((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr)) ∗ R') := by
        rw [hslots_eq]
        have hac :
            (W st s0 ∗ (stackFrameAt (s0.sp - 48#64) stackBytes ∗
              (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr)))) ∗ R' =
            (W st s0 ∗ stackFrameAt (s0.sp - 48#64) stackBytes) ∗
              ((((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr)) ∗ R') := by
          ac_rfl
        rw [hac]
        exact sepConj_mono_left (sepConj_mono_left (hw.transport st s0 sm hframe_sm))
      exact Satisfies.mono hent hm
    · intro sf _ R' _ hmf
      exact not_satisfies_false_sepConj hmf
    · intro sf _ _ hm
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec, fmtWriterCharSpec] at hm ⊢
      have hm1 : sf.mem ⊨ (⌜Panic st (charUtf8Len signWord) sf⌝ ∗
          (anyHeap ∗ (((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ wpSavedSlots s0.sp s0 (s0.readReg64 Reg.lr)))) ∗ R := by
        simpa [sepConj_assoc] using hm
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
      refine ⟨?_, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm1.2⟩
      rw [hsign_eq]
      exact FmtOpsAbort.single_char hm1.1
    · intro sf1 hpc1 hrun1 hsp1 hcs1 hcl1
      dsimp only [fmtWriterCharSpec]
      apply sepWPp_sepExists_left; intro ok
      apply sepWPp_sepExists_left; intro st'
      rw [sepConj_assoc, sepConj_assoc]
      apply sepWPp_pure_left; rintro ⟨hw0_1, hcstep⟩
      rw [CalleeSavedPreserved.iff_regs] at hcs1
      rcases hcs1 with ⟨_, h20_1, _, _, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, _, hv_1⟩
      have hsp1_eq : sf1.sp = s0.sp - 48#64 := hsp1.trans hsp_sm
      have hsp1_al : sf1.spAligned = true := by
        have h0 : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_al
        simp only [State.spAligned, hsp1_eq, spAligned_to_sub_48_and h0, beq_self_eq_true]
      have hrun_op : FmtOpsRun StrStep CharStep (writePrefixSignOp signWord) st ok st' := by
        rw [hsign_eq]; exact FmtOpsRun.single_char hcstep
      dsimp only [MultiPlacedLib.withCodeLoadedWhere]
      rw [hsp_sm]
      refine SepWPp.congr_pre ?_
        (writePrefix_epilogue_wpp (wcFn := wcFn) hkeep5 hext5 hw.transport hcl1 hpc1 hrun1
          hsp1_eq hsp1_al hstack hw0_1 (h20_1.trans hx20_sm) (h23_1.trans hx23_sm)
          (h24_1.trans hx24_sm) (h25_1.trans hx25_sm) (h26_1.trans hx26_sm)
          (h27_1.trans hx27_sm) (h28_1.trans hx28_sm) (hv_1.trans hvregs_sm) hrun_op)
      ac_rfl
    · intro sf R' _ hmo
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec, fmtWriterCharSpec] at hmo ⊢
      rw [satisfies_pure_sepConj] at hmo ⊢
      refine ⟨?_, Satisfies.drop_left hmo.2⟩
      rw [hsign_eq]
      exact FmtOpsAbort.single_char hmo.1

end WritePrefixProof

end VerifiedLibraries.RustStd
