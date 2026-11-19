/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.PadIntegralPrefix

/-!
# `pad_integral` Proof Context and Call/Loop Segments

Defines `PiCtx` and its postconditions (`PiPost`, `PiQ`, `PiWpp`), the shared epilogue and error
exit, the `write_prefix` / `write_char` / `write_str` call segments, and the
`SIGN_AWARE_ZERO_PAD` fill loop for `coreFmtMultiLib` block `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd.CoreFmt

namespace PadIntegralProof

arm64_proof_prelude
set_option linter.literalFetch false

theorem pi_formatterAt_triple (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) :
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

theorem pi_formatterAt_memRegion24 (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) :
    formatterAt f outPtr vtPtr opts ⊢ memRegion f 24 := by
  rw [pi_formatterAt_triple, memRegion_split' (n := 8) (k := 16) rfl rfl (by decide),
      memRegion_split' (b := f + 8#64) (b' := f + 16#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem spAligned_to_sub_112_and {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 112#64) &&& 15#64 = 0#64 := by
  have h0 : (sp0 &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 := Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  have hm2 : ((sp0 - 112#64) &&& 15#64).toNat = (sp0 - 112#64).toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod (sp0 - 112#64).toNat 4
  rw [hm1] at h0
  apply BitVec.eq_of_toNat_eq
  rw [hm2, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := sp0.isLt; omega

theorem stackFrameAt_112_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 112 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
      ∃∗ v7, ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12, ∃∗ v13,
        ((sp0 - 112#64) ↦₆₄ v0) ∗ ((sp0 - 104#64) ↦₆₄ v1) ∗
        ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗
        ((sp0 - 80#64) ↦₆₄ v4) ∗ ((sp0 - 72#64) ↦₆₄ v5) ∗
        ((sp0 - 64#64) ↦₆₄ v6) ∗ ((sp0 - 56#64) ↦₆₄ v7) ∗
        ((sp0 - 48#64) ↦₆₄ v8) ∗ ((sp0 - 40#64) ↦₆₄ v9) ∗
        ((sp0 - 32#64) ↦₆₄ v10) ∗ ((sp0 - 24#64) ↦₆₄ v11) ∗
        ((sp0 - 16#64) ↦₆₄ v12) ∗ ((sp0 - 8#64) ↦₆₄ v13) := by
  simp only [arm64_norm]

def piSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

def piSavedSlots (s0 : State) (v0 v1 : BitVec 64) : SepProp :=
  ((s0.sp - 112#64) ↦₆₄ v0) ∗ ((s0.sp - 104#64) ↦₆₄ v1) ∗ piSavedRegs s0

theorem piSavedSlots_fold (s0 : State) (v0 v1 : BitVec 64) :
    piSavedSlots s0 v0 v1 ⊢ stackFrameAt s0.sp 112 := by
  rw [stackFrameAt_112_unpack s0.sp]
  dsimp only [piSavedSlots, piSavedRegs]
  iterate 14 apply Entails.sepExists_right
  exact Entails.refl _

theorem bl_target_writePrefix [CoreFmtPlacement] (off : BitVec 64) :
    coreFmtPl00.base + off + ((coreFmtPl00.ρ writePrefixIntSym - coreFmtPl00.base) - off) =
      coreFmtPl05.base := by
  have hres : coreFmtPl00.ρ writePrefixIntSym = coreFmtPl05.base :=
    resolve_writePrefix CoreFmtPlacement.placeable
  rw [hres]; bv_omega

theorem calleeSavedVRegs_of_cs {s sf : State} (hcs : CalleeSavedPreserved s sf) :
    calleeSavedVRegs sf = calleeSavedVRegs s := by
  rw [CalleeSavedPreserved.iff_regs] at hcs
  exact hcs.2.2.2.2.2.2.2.2.2.2.2

structure PiCtx (σ : Type) (P : Program) [CoreFmtPlacement] where
  W : σ → State → SepProp
  StrStep : σ → List (BitVec 8) → Bool → σ → Prop
  CharStep : σ → BitVec 32 → Bool → σ → Prop
  Panic : σ → Nat → State → Prop
  Oom : σ → Nat → State → Prop
  stackBytes : Nat
  hext : LibKeepNoExtern coreFmtMultiLib padIntegralKeep coreFmtMpl P
  f : BitVec 64
  out : BitVec 64
  vt : BitVec 64
  wsFn : BitVec 64
  wcFn : BitVec 64
  opts : FmtOptions
  isNonneg : Bool
  ro : Bool
  dsPtr : BitVec 64
  ds : List (BitVec 8)
  hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn
  s0 : State
  R : SepProp
  hsp_al0 : s0.spAligned = true
  hstack : 160 + stackBytes ≤ 2 ^ 64
  hds_lt : ds.length < 2 ^ 60
  hnoalt : opts.flags.getLsbD 23 = false

theorem PiCtx.hext0 {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P) :
    LibBlockNoExtern coreFmtMultiLib coreFmtMpl P 0 :=
  C.hext 0 (by decide) (by decide)

theorem PiCtx.hext5 {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P) :
    LibBlockNoExtern coreFmtMultiLib coreFmtMpl P 5 :=
  C.hext 5 (by decide) (by decide)

theorem PiCtx.hstack48 {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P) :
    48 + C.stackBytes ≤ 2 ^ 64 := by
  have := C.hstack; omega

theorem PiCtx.sp1_aligned {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {s : State} (hsp : s.sp = C.s0.sp - 112#64) : s.spAligned = true := by
  have h0 : C.s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using C.hsp_al0
  simp only [State.spAligned, hsp, spAligned_to_sub_112_and h0, beq_self_eq_true]

def PiCtx.vtSlots {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P) : SepProp :=
  ((C.vt + 0x18#64) ↦₆₄ᵣ C.wsFn) ∗ ((C.vt + 0x20#64) ↦₆₄ᵣ C.wcFn)

def PiPost {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (ops : List FmtOp) (st : σ) (sf : State) : SepProp :=
  ∃∗ ok : Bool, ∃∗ st' : σ,
    ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
      FmtOpsRun C.StrStep C.CharStep ops st ok st'⌝ ∗
      (if ok then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
      fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sf ∗ stackFrameAt C.s0.sp (160 + C.stackBytes)

def PiQ {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (ops : List FmtOp) (st : σ) (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ C.R) → (sf.mem ⊨ PiPost C ops st sf ∗ C.R)) ∧
    sf.sp = C.s0.sp ∧ CalleeSavedPreserved C.s0 sf

def PiQp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (ops : List FmtOp) (st : σ) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ C.R) →
    (sf.mem ⊨ (⌜FmtOpsAbort C.StrStep C.CharStep C.Panic ops st sf⌝ ∗ anyHeap) ∗ C.R)

def PiOom {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (ops : List FmtOp) (st : σ) (sf : State) : SepProp :=
  ⌜FmtOpsAbort C.StrStep C.CharStep C.Oom ops st sf⌝

def PiWpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (s : State) (Pre : SepProp) (ops : List FmtOp) (st : σ) : Prop :=
  SepWPp P (C.s0.readReg64 Reg.lr) s Pre (PiQ C ops st) (PiQp C ops st) (PiOom C ops st)

theorem sepWPp_mono_pre {P : Program} {ret : BitVec 64} {s : State} {P1 P2 : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P1 ⊢ P2) (h : SepWPp P ret s P2 Q Qp oom) :
    SepWPp P ret s P1 Q Qp oom :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem pi_wpp_mono {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops : List FmtOp} {st : σ} {s : State} {P1 P2 : SepProp}
    (h : PiWpp C s P2 ops st) (hent : P1 ⊢ P2) :
    PiWpp C s P1 ops st :=
  sepWPp_mono_pre hent h

theorem pi_ops_eq {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops ops' : List FmtOp} {st : σ} {s : State} {Pre : SepProp}
    (heq : ops = ops') (h : PiWpp C s Pre ops' st) :
    PiWpp C s Pre ops st :=
  heq ▸ h

theorem pi_ops_ok_conseq {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops₁ ops₂ : List FmtOp} {st st' : σ} {s : State} {Pre : SepProp}
    (h₁ : FmtOpsRun C.StrStep C.CharStep ops₁ st true st')
    (h₂ : PiWpp C s Pre ops₂ st') :
    PiWpp C s Pre (ops₁ ++ ops₂) st := by
  refine sepWPp_conseq (fun sf P_f hq => ⟨fun hmf => ?_, hq.2⟩)
    (fun sf P_f hqp hmf => ?_) (fun sf R' hmo => ?_) h₂
  · have hm2 := hq.1 hmf
    dsimp only [PiPost] at hm2 ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2 ⊢
    rcases hm2 with ⟨ok, hm2⟩
    refine ⟨ok, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2 ⊢
    rcases hm2 with ⟨st'', hm2⟩
    refine ⟨st'', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2 ⊢
    exact ⟨⟨hm2.1.1, FmtOpsRun.append_ok h₁ hm2.1.2⟩, hm2.2⟩
  · have hm2 := hqp hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2 ⊢
    exact ⟨FmtOpsAbort.of_right h₁ hm2.1, hm2.2⟩
  · dsimp only [PiOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    exact ⟨FmtOpsAbort.of_right h₁ hmo.1, hmo.2⟩

theorem piEpilogue364_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (ok : Bool) (v0 v1 : BitVec 64) {ops : List FmtOp} {st st' : σ} {sf1 : State}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sf1.mem)
    (hpc : sf1.pc = coreFmtPl00.base + 868#64) (hrun : sf1.status = .Running)
    (hsp : sf1.sp = C.s0.sp - 112#64)
    (hw19 : sf1.readReg32 (.gpr 19#5) = if ok then 0#32 else 1#32)
    (hvregs : calleeSavedVRegs sf1 = calleeSavedVRegs C.s0)
    (hrun_ops : FmtOpsRun C.StrStep C.CharStep ops st ok st') :
    PiWpp C sf1
      ((if ok then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
        fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sf1 ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 v1)
      ops st := by
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := C.s0.readReg64 Reg.lr)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 868#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans (C.sp1_aligned hsp)
  have hw19' : s'.readReg32 (.gpr 19#5) = if ok then 0#32 else 1#32 :=
    (hcpu_in.readReg32 _).trans hw19
  have hw_post : ∀ (sm : State), FmtWriteFrame sf1 sm →
      (sm.readReg32 .x0 = if ok then 0#32 else 1#32) →
      ∀ hm : sm.mem ⊨
        ((if ok then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
          (fmtSrcBytes C.ro C.dsPtr C.ds ∗ (C.W st' sf1 ∗
            (stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
              (C.vtSlots ∗ piSavedSlots C.s0 v0 v1))))) ∗ C.R,
      sm.mem ⊨ PiPost C ops st sm ∗ C.R := by
    intro sm hframe hw0f hm
    have h160 : 112 + (48 + C.stackBytes) = 160 + C.stackBytes := by omega
    have hent :
        (if ok then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
          (fmtSrcBytes C.ro C.dsPtr C.ds ∗ (C.W st' sf1 ∗
            (stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
              (C.vtSlots ∗ piSavedSlots C.s0 v0 v1)))) ⊢
        C.vtSlots ∗ ((if ok then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
          fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sm ∗
          stackFrameAt C.s0.sp (160 + C.stackBytes)) := by
      rw [← h160, stackFrameAt_split C.s0.sp 112 (48 + C.stackBytes) (h160.symm ▸ C.hstack)]
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (C.hw.transport st' sf1 sm hframe)
            (sepConj_mono_left (piSavedSlots_fold C.s0 v0 v1))))))
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hm
    rw [sepConj_assoc] at hm1
    dsimp only [PiPost]
    refine Satisfies.mono (sepConj_mono_left ?_) (Satisfies.drop_left hm1)
    refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
    rw [pure_sepConj_of_true ⟨hw0f, hrun_ops⟩]
    exact Entails.refl _
  dsimp only [piSavedSlots, piSavedRegs]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  cases ok <;> {
    simp [arm64_norm] at hw19'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out _hcl_sm hpseg => ?_
    have hpcf : sm.pc = C.s0.readReg64 Reg.lr := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
    have hrunf : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
    have hspf : sm.sp = C.s0.sp := by rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have hcsf : CalleeSavedPreserved C.s0 sm := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs⟩ <;>
        (rw [hcpu_out.readReg64]; simp [arm64_norm])
    have hframe : FmtWriteFrame sf1 sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    exact SepWPp.done hpcf hrunf
      ⟨fun hm => hw_post sm hframe (by rw [hcpu_out.readReg32 .x0]; simp [arm64_norm])
        (by simpa [piSavedSlots, piSavedRegs, sepConj_assoc] using hm), hspf, hcsf⟩
  }

theorem piExitErr360_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (optsCur : FmtOptions) (v0 v1 : BitVec 64) {ops : List FmtOp} {st st' : σ} {sf1 : State}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sf1.mem)
    (hpc : sf1.pc = coreFmtPl00.base + 864#64) (hrun : sf1.status = .Running)
    (hsp : sf1.sp = C.s0.sp - 112#64)
    (hvregs : calleeSavedVRegs sf1 = calleeSavedVRegs C.s0)
    (hrun_err : FmtOpsRun C.StrStep C.CharStep ops st false st') :
    PiWpp C sf1
      (formatterAt C.f C.out C.vt optsCur ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sf1 ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 v1)
      ops st := by
  refine sepWPp_mono_pre (sepConj_mono_left (pi_formatterAt_memRegion24 C.f C.out C.vt optsCur)) ?_
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 868#64)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 864#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  have hpc_sm : sm.pc = coreFmtPl00.base + 868#64 := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrun_sm : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm : sm.sp = C.s0.sp - 112#64 := by
    rw [hcpu_out.sp_eq]; simpa [arm64_norm] using (hcpu_in.sp_eq.trans hsp)
  have hw19_sm : sm.readReg32 (.gpr 19#5) = 1#32 := by
    rw [hcpu_out.readReg32]; simp [arm64_norm]
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
    rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hframe : FmtWriteFrame sf1 sm :=
    fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  refine sepWPp_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st' sf1 sm hframe)))) ?_
  exact piEpilogue364_wpp C false v0 v1 hcl_sm hpc_sm hrun_sm hsp_sm hw19_sm hvregs_sm hrun_err

theorem piCallWritePrefix_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops_rest : List FmtOp} {st : σ} {sm : State} {ret_pc : BitVec 64}
    {signWord : BitVec 32} {F : SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sm.mem)
    (hpc : sm.pc = coreFmtPl05.base) (hrun : sm.status = .Running)
    (hsp : sm.sp = C.s0.sp - 112#64) (hlr : sm.readReg64 Reg.lr = ret_pc)
    (hx0 : sm.readReg64 .x0 = C.out) (hx1 : sm.readReg64 .x1 = C.vt)
    (hw2 : sm.readReg32 .x2 = signWord) (hx3 : sm.readReg64 .x3 = 0#64)
    (hnext : ∀ (sf : State) (ok : Bool) (st' : σ),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = C.s0.sp - 112#64 →
      CalleeSavedPreserved sm sf →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sf.mem →
      sf.readReg32 .x0 = (if ok then 0#32 else 1#32) →
      FmtOpsRun C.StrStep C.CharStep (writePrefixSignOp signWord) st ok st' →
      PiWpp C sf (C.W st' sf ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
        (writePrefixSignOp signWord ++ ops_rest) st) :
    PiWpp C sm (C.W st sm ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
      (writePrefixSignOp signWord ++ ops_rest) st := by
  have hwp := writePrefix_ok P C.W C.StrStep C.CharStep C.Panic C.Oom C.stackBytes
    coreFmtMpl CoreFmtPlacement.placeable (keep := padIntegralKeep) (by decide)
    C.hext5 C.out C.vt C.wsFn C.wcFn signWord C.hw
  rw [fnAddr_writePrefix CoreFmtPlacement.placeable] at hwp
  refine call_wpp_where (F := F) (x := st) hwp hcl hpc hrun (C.sp1_aligned hsp) hlr
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec]
    rw [pure_sepConj_of_true ⟨hx0, hx1, hw2, hx3, C.hstack48⟩, hsp]
    have hent :
        (C.W st sm ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F) ∗ R' ⊢
        ((C.W st sm ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes)) ∗
          ⌜coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sm.mem⌝) ∗ (F ∗ R') := by
      rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl]
      exact Entails.of_eq (by ac_rfl)
    exact Satisfies.mono hent hm
  · intro sf _ R' _ hmf; exact not_satisfies_false_sepConj hmf
  · intro sf _ _ hm
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec, PiQp] at hm ⊢
    have hm1 : sf.mem ⊨
        (⌜FmtOpsAbort C.StrStep C.CharStep C.Panic (writePrefixSignOp signWord) st sf⌝ ∗
          (anyHeap ∗ F)) ∗ C.R := by simpa [sepConj_assoc] using hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
    exact ⟨FmtOpsAbort.of_left ops_rest hm1.1,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm1.2⟩
  · intro sf hpcf hrunf hspf hcsf hcl_sf
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0_sf, hrun_sf⟩
    rw [hsp]
    exact SepWPp.congr_pre (by ac_rfl)
      (hnext sf ok st' hpcf hrunf (hspf.trans hsp) hcsf hcl_sf hw0_sf hrun_sf)
  · intro sf R' _ hmo
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writePrefixSpec, PiOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    exact ⟨FmtOpsAbort.of_left ops_rest hmo.1, Satisfies.drop_left hmo.2⟩

theorem piCallWriteChar_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops_rest : List FmtOp} {st : σ} {sm : State} {ret_pc : BitVec 64}
    {c : BitVec 32} {F : SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sm.mem)
    (hpc : sm.pc = C.wcFn) (hrun : sm.status = .Running)
    (hsp : sm.sp = C.s0.sp - 112#64) (hlr : sm.readReg64 Reg.lr = ret_pc)
    (hx0 : sm.readReg64 .x0 = C.out) (hw1 : sm.readReg32 .x1 = c)
    (hnext : ∀ (sf : State) (ok : Bool) (st' : σ),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = C.s0.sp - 112#64 →
      CalleeSavedPreserved sm sf →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sf.mem →
      sf.readReg32 .x0 = (if ok then 0#32 else 1#32) →
      C.CharStep st c ok st' →
      PiWpp C sf (C.W st' sf ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
        (.char c :: ops_rest) st) :
    PiWpp C sm (C.W st sm ∗ stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
      (.char c :: ops_rest) st := by
  have h48 : 48 + C.stackBytes = C.stackBytes + 48 := by omega
  have hsplit := stackFrameAt_split (C.s0.sp - 112#64) C.stackBytes 48 (h48 ▸ C.hstack48)
  refine call_wpp_where
    (F := stackFrameAt (C.s0.sp - 112#64 - BitVec.ofNat 64 C.stackBytes) 48 ∗ F)
    (x := st) (C.hw.write_char c) hcl hpc hrun (C.sp1_aligned hsp) hlr
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [fmtWriterCharSpec]
    rw [hsp, pure_sepConj_of_true ⟨hx0, hw1⟩]
    rw [h48, hsplit] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf _ R' _ hmf; exact not_satisfies_false_sepConj hmf
  · intro sf _ _ hm
    dsimp only [fmtWriterCharSpec, PiQp] at hm ⊢
    have hm1 : sf.mem ⊨ (⌜C.Panic st (charUtf8Len c) sf⌝ ∗
        (anyHeap ∗ (stackFrameAt (C.s0.sp - 112#64 - BitVec.ofNat 64 C.stackBytes) 48 ∗ F))) ∗ C.R := by
      simpa [sepConj_assoc] using hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
    exact ⟨FmtOpsAbort.of_head (op := .char c) hm1.1,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm1.2⟩
  · intro sf hpcf hrunf hspf hcsf hcl_sf
    dsimp only [fmtWriterCharSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0_sf, hcstep⟩
    refine SepWPp.congr_pre ?_
      (hnext sf ok st' hpcf hrunf (hspf.trans hsp) hcsf hcl_sf hw0_sf hcstep)
    rw [hsp, h48, hsplit]; ac_rfl
  · intro sf R' _ hmo
    dsimp only [fmtWriterCharSpec, PiOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    exact ⟨FmtOpsAbort.of_head (op := .char c) hmo.1, Satisfies.drop_left hmo.2⟩

theorem piCallWriteStr_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {ops_rest : List FmtOp} {st : σ} {sm : State} {ret_pc : BitVec 64} {F : SepProp}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sm.mem)
    (hpc : sm.pc = C.wsFn) (hrun : sm.status = .Running)
    (hsp : sm.sp = C.s0.sp - 112#64) (hlr : sm.readReg64 Reg.lr = ret_pc)
    (hx0 : sm.readReg64 .x0 = C.out) (hx1 : sm.readReg64 .x1 = C.dsPtr)
    (hx2 : (sm.readReg64 .x2).toNat = C.ds.length)
    (hnext : ∀ (sf : State) (ok : Bool) (st' : σ),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = C.s0.sp - 112#64 →
      CalleeSavedPreserved sm sf →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sf.mem →
      sf.readReg32 .x0 = (if ok then 0#32 else 1#32) →
      C.StrStep st C.ds ok st' →
      PiWpp C sf
        (fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sf ∗
          stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
        (.str C.ds :: ops_rest) st) :
    PiWpp C sm
      (fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st sm ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ F)
      (.str C.ds :: ops_rest) st := by
  have h48 : 48 + C.stackBytes = C.stackBytes + 48 := by omega
  have hsplit := stackFrameAt_split (C.s0.sp - 112#64) C.stackBytes 48 (h48 ▸ C.hstack48)
  refine call_wpp_where
    (F := stackFrameAt (C.s0.sp - 112#64 - BitVec.ofNat 64 C.stackBytes) 48 ∗ F)
    (x := st) (C.hw.write_str C.ro C.dsPtr C.ds) hcl hpc hrun (C.sp1_aligned hsp) hlr
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [fmtWriterStrSpec]
    rw [hsp, pure_sepConj_of_true ⟨hx0, hx1, hx2, C.hds_lt⟩]
    rw [h48, hsplit] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf _ R' _ hmf; exact not_satisfies_false_sepConj hmf
  · intro sf _ _ hm
    dsimp only [fmtWriterStrSpec, PiQp] at hm ⊢
    have hm1 : sf.mem ⊨ (⌜C.Panic st C.ds.length sf⌝ ∗
        (anyHeap ∗ (stackFrameAt (C.s0.sp - 112#64 - BitVec.ofNat 64 C.stackBytes) 48 ∗ F))) ∗ C.R := by
      simpa [sepConj_assoc] using hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
    exact ⟨FmtOpsAbort.of_head (op := .str C.ds) hm1.1,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm1.2⟩
  · intro sf hpcf hrunf hspf hcsf hcl_sf
    dsimp only [fmtWriterStrSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0_sf, hsstep⟩
    refine SepWPp.congr_pre ?_
      (hnext sf ok st' hpcf hrunf (hspf.trans hsp) hcsf hcl_sf hw0_sf hsstep)
    rw [hsp, h48, hsplit]; ac_rfl
  · intro sf R' _ hmo
    dsimp only [fmtWriterStrSpec, PiOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    exact ⟨FmtOpsAbort.of_head (op := .str C.ds) hmo.1, Satisfies.drop_left hmo.2⟩

theorem piZeroPadTail2d4_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (optsMut : FmtOptions) (v0 : BitVec 64) {st : σ} {s : State}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 724#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx21 : s.readReg64 (.gpr 21#5) = C.f)
    (hx25 : s.readReg64 (.gpr 25#5) = C.out)
    (hx26 : s.readReg64 (.gpr 26#5) = C.vt)
    (hx28 : s.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt optsMut ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      [.str C.ds] st := by
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := C.wsFn)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 724#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans (C.sp1_aligned hsp)
  have hx25' : s'.readReg64 (.gpr 25#5) = C.out := (hcpu_in.readReg64 _).trans hx25
  have hx26' : s'.readReg64 (.gpr 26#5) = C.vt := (hcpu_in.readReg64 _).trans hx26
  dsimp only [PiCtx.vtSlots, piSavedSlots]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  have hpc_sm : sm.pc = C.wsFn := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrun_sm : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm : sm.sp = C.s0.sp - 112#64 := by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hsp'
  have hlr_sm : sm.readReg64 Reg.lr = coreFmtPl00.base + 744#64 := by
    rw [hcpu_out.readReg64 Reg.lr]; simp [arm64_norm]
  have hx0_sm : sm.readReg64 .x0 = C.out := by rw [hcpu_out.readReg64 .x0]; simp [arm64_norm]
  have hx1_sm : sm.readReg64 .x1 = C.dsPtr := by rw [hcpu_out.readReg64 .x1]; simp [arm64_norm]
  have hx2_sm : (sm.readReg64 .x2).toNat = C.ds.length := by
    rw [hcpu_out.readReg64 .x2]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
  have hx21_sm : sm.readReg64 (.gpr 21#5) = C.f := by
    rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21
  have hx28_sm : sm.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags := by
    rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
    rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hframe_sm : FmtWriteFrame s sm :=
    fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  refine sepWPp_mono_pre
    (P2 := fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st sm ∗
      stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
      (formatterAt C.f C.out C.vt optsMut ∗ C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr))
    (by dsimp only [PiCtx.vtSlots, piSavedSlots]
        exact Entails.trans (Entails.of_eq (by ac_rfl))
          (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe_sm)))) ?_
  refine piCallWriteStr_wpp C hcl_sm hpc_sm hrun_sm hsp_sm hlr_sm hx0_sm hx1_sm hx2_sm ?_
  intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hsstep
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs C.s0 :=
    (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm
  rw [CalleeSavedPreserved.iff_regs] at hcsf
  have hx21_sf : sf.readReg64 (.gpr 21#5) = C.f := hcsf.2.2.1.trans hx21_sm
  have hx28_sf : sf.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags :=
    hcsf.2.2.2.2.2.2.2.2.2.1.trans hx28_sm
  cases ok with
  | false =>
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 864#64)
    intro s2 hcpu2_in
    have hpc2 : s2.pc = coreFmtPl00.base + 744#64 := hcpu2_in.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf
    have hw0_2 : s2.readReg32 .x0 = 1#32 := (hcpu2_in.readReg32 .x0).trans hw0f
    simp [arm64_norm] at hw0_2
    clear hpcf
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 :=
      fmtWriteFrame_of_pureSeg hpseg2
        (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
        (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piExitErr360_wpp C optsMut v0 C.dsPtr hcl_sm2 (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
        (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
        (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)
        (FmtOpsRun.single_str hsstep)) ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2)))
      (Entails.of_eq (by dsimp only [PiCtx.vtSlots, piSavedSlots]; ac_rfl))
  | true =>
    rw [pi_formatterAt_triple C.f C.out C.vt optsMut]
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 868#64)
    intro s2 hcpu2_in
    have hpc2 : s2.pc = coreFmtPl00.base + 744#64 := hcpu2_in.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf
    have hw0_2 : s2.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0f
    have hx21_2 : s2.readReg64 (.gpr 21#5) = C.f := (hcpu2_in.readReg64 _).trans hx21_sf
    have hx28_2 : s2.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags :=
      (hcpu2_in.readReg64 _).trans hx28_sf
    simp [arm64_norm] at hw0_2
    wp_conv_pre => simp only [sepConj_assoc]
    clear hpcf
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 :=
      fmtWriteFrame_of_pureSeg hpseg2
        (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
        (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piEpilogue364_wpp C true v0 C.dsPtr hcl_sm2
        (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
        (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
        (by rw [hcpu2_out.readReg32]; simp [arm64_norm])
        (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)
        (FmtOpsRun.single_str hsstep)) ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2)))
      (Entails.of_eq (by
        simp only [↓reduceIte, pi_formatterAt_triple C.f C.out C.vt C.opts]
        dsimp only [PiCtx.vtSlots, piSavedSlots]; ac_rfl))

theorem loop_mask32_toNat (n : Nat) :
    (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) &&& 281470681808895#64)).toNat =
      n % 65536 := by
  let x := BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
  have h1 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) &&&
      281470681808895#64) = x &&& 65535#32 := BitVec.setWidth_and
  have hm : (x &&& 65535#32).toNat = x.toNat % 65536 := Nat.and_two_pow_sub_one_eq_mod x.toNat 16
  rw [h1, hm]
  dsimp only [x]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem loop_cmp_eq (cnt : Nat) :
    (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 cnt))).ule
      (BitVec.setWidth 32
        (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) &&& 281470681808895#64)) =
      true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, loop_mask32_toNat]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem loop_cmp_lt {cnt tot : Nat} (h1 : cnt < tot) (h2 : tot < 65536) :
    (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 tot))).ule
      (BitVec.setWidth 32
        (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) &&& 281470681808895#64)) =
      false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, loop_mask32_toNat]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem loop_inc64 {cnt : Nat} (h : cnt + 1 < 65536) :
    BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt) + 1#32) =
      BitVec.ofNat 64 (cnt + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem piZeroPadLoop_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (optsMut : FmtOptions) (v0 : BitVec 64) {pad : Nat} (hpad : pad < 65536) :
    ∀ (rem cnt : Nat) (st : σ) (s : State),
      cnt + rem = pad →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem →
      s.pc = coreFmtPl00.base + 664#64 →
      s.status = .Running →
      s.sp = C.s0.sp - 112#64 →
      (s.readReg64 (.gpr 19#5)).toNat = C.ds.length →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 pad →
      s.readReg64 (.gpr 21#5) = C.f →
      s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cnt →
      s.readReg64 (.gpr 25#5) = C.out →
      s.readReg64 (.gpr 26#5) = C.vt →
      s.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags →
      calleeSavedVRegs s = calleeSavedVRegs C.s0 →
      PiWpp C s
        (formatterAt C.f C.out C.vt optsMut ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
          stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        (List.replicate rem (.char 0x30#32) ++ [.str C.ds]) st := by
  intro rem
  induction rem with
  | zero =>
    intro cnt st s hsum hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx25 hx26 hx28 hvregs
    have hcnt : cnt = pad := by omega
    subst hcnt
    have hcmp := loop_cmp_eq cnt
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 724#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 664#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx20
    have hx22' : s'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx22
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hframe : FmtWriteFrame s sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piZeroPadTail2d4_wpp C optsMut v0 hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx25)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx26)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28)
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe)))
  | succ k ih =>
    intro cnt st s hsum hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx25 hx26 hx28 hvregs
    have hlt : cnt < pad := by omega
    have hcmp := loop_cmp_lt hlt hpad
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := C.wcFn)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 664#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 pad := (hcpu_in.readReg64 _).trans hx20
    have hx22' : s'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx22
    have hx25' : s'.readReg64 (.gpr 25#5) = C.out := (hcpu_in.readReg64 _).trans hx25
    have hx26' : s'.readReg64 (.gpr 26#5) = C.vt := (hcpu_in.readReg64 _).trans hx26
    dsimp only [PiCtx.vtSlots]
    wp_conv_pre => simp only [sepConj_assoc]
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hpc_sm : sm.pc = C.wcFn := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
    have hrun_sm : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
    have hsp_sm : sm.sp = C.s0.sp - 112#64 := by
      rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp
    have hlr_sm : sm.readReg64 Reg.lr = coreFmtPl00.base + 696#64 := by
      rw [hcpu_out.readReg64 Reg.lr]; simp [arm64_norm]
    have hx0_sm : sm.readReg64 .x0 = C.out := by rw [hcpu_out.readReg64 .x0]; simp [arm64_norm]
    have hw1_sm : sm.readReg32 .x1 = 0x30#32 := by rw [hcpu_out.readReg32 .x1]; simp [arm64_norm]
    have hx19_sm : (sm.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
    have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 pad := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx20'
    have hx21_sm : sm.readReg64 (.gpr 21#5) = C.f := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21
    have hx22_sm : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cnt + 1) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using loop_inc64 (by omega)
    have hx25_sm : sm.readReg64 (.gpr 25#5) = C.out := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx25'
    have hx26_sm : sm.readReg64 (.gpr 26#5) = C.vt := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx26'
    have hx28_sm : sm.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
      rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
    have hframe_sm : FmtWriteFrame s sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piCallWriteChar_wpp C
        (F := formatterAt C.f C.out C.vt optsMut ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        hcl_sm hpc_sm hrun_sm hsp_sm hlr_sm hx0_sm hw1_sm ?_) ?_
    · intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hcstep
      have hvregs_sf := (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm
      rw [CalleeSavedPreserved.iff_regs] at hcsf
      rcases hcsf with ⟨h19f, h20f, h21f, h22f, _, _, h25f, h26f, _, h28f, _, _⟩
      cases ok with
      | false =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 864#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 696#64 := hcpu2_in.pc_eq.trans hpcf
        have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf
        have hw0_2 : s2.readReg32 .x0 = 1#32 := (hcpu2_in.readReg32 .x0).trans hw0f
        simp [arm64_norm] at hw0_2
        clear hpcf
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
          fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
        have hframe2 : FmtWriteFrame sf sm2 :=
          fmtWriteFrame_of_pureSeg hpseg2
            (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
            (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
        refine pi_wpp_mono C
          (piExitErr360_wpp C optsMut v0 C.dsPtr hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)
            (FmtOpsRun.char_err hcstep)) ?_
        exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2))
          (Entails.of_eq (by ac_rfl))
      | true =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 664#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 696#64 := hcpu2_in.pc_eq.trans hpcf
        have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf
        have hw0_2 : s2.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0f
        simp [arm64_norm] at hw0_2
        clear hpcf
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
          fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
        have hframe2 : FmtWriteFrame sf sm2 :=
          fmtWriteFrame_of_pureSeg hpseg2
            (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
            (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
        refine pi_ops_ok_conseq C (ops₁ := [.char 0x30#32]) (FmtOpsRun.single_char hcstep) ?_
        refine pi_wpp_mono C
          (ih (cnt + 1) st' sm2 (by omega) hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h19f] using hx19_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h20f] using hx20_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h21f] using hx21_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h22f] using hx22_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h25f] using hx25_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h26f] using hx26_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h28f] using hx28_sm)
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)) ?_
        exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2))
          (Entails.of_eq (by ac_rfl))
    · exact Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe_sm))))
        (Entails.of_eq (by dsimp only [PiCtx.vtSlots]; ac_rfl))

end PadIntegralProof

end VerifiedLibraries.RustStd
