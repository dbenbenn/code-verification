/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.PadIntegralPaths

/-!
# `<core::fmt::Formatter>::pad_integral` Proof

Placement-generic proof of `<core::fmt::Formatter>::pad_integral` (`coreFmtMultiLib` block `0` and
`write_prefix` in block `5`) against `formatterPadIntegralSpec` for `opts.flags.getLsbD 23 = false`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd.CoreFmt

namespace PadIntegralProof

arm64_proof_prelude
set_option linter.literalFetch false

theorem alignWord_eq (opts : FmtOptions) :
    BitVec.setWidth 32 (BitVec.setWidth 64 opts.flags >>> 29 &&& 3#64) =
      BitVec.ofNat 32 ((opts.flags >>> 29).toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.setWidth 64 opts.flags >>> 29 &&& 3#64).toNat =
      (BitVec.setWidth 64 opts.flags >>> 29).toNat % 4 :=
    Nat.and_two_pow_sub_one_eq_mod _ 2
  simp only [BitVec.toNat_setWidth, hm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have := opts.flags.isLt
  omega

theorem half32_zeroExtend_of_lt {pad : Nat} (hpad : pad < 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 ((BitVec.ofNat 64 pad >>> 1) &&& 32767#64)) =
      BitVec.ofNat 64 (pad / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hm : ((BitVec.ofNat 64 pad >>> 1) &&& 32767#64).toNat =
      (BitVec.ofNat 64 pad >>> 1).toNat % 32768 :=
    Nat.and_two_pow_sub_one_eq_mod _ 15
  simp only [BitVec.toNat_setWidth, hm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  omega

theorem zext32_ofNat_of_lt {pad : Nat} (hpad : pad < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 pad)) = BitVec.ofNat 64 pad := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem piAlignPad_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 : BitVec 64) {st : σ} {s : State}
    (hgt : (fmtSignOp C.opts C.isNonneg).length + C.ds.length < C.opts.width.toNat)
    (h24 : C.opts.flags.getLsbD 24 = false)
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 572#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat)
    (hx21 : s.readReg64 (.gpr 21#5) = C.f)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (hw24 : s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg)
    (hw26 : s.readReg32 (.gpr 26#5) = C.opts.flags)
    (hx27 : s.readReg64 (.gpr 27#5) =
      BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      (padIntegralNoAltOps C.opts C.isNonneg C.ds) st := by
  let pad := C.opts.width.toNat - ((fmtSignOp C.opts C.isNonneg).length + C.ds.length)
  let lp := (fmtPadSplit C.opts pad).1
  have hpad_lt : pad < 65536 := by have := C.opts.width.isLt; omega
  have hbnd := fmtPadSplit_bounds C.opts pad
  have hlp_le : lp ≤ pad := by dsimp only [lp]; omega
  have hrp_eq : (fmtPadSplit C.opts pad).2 = pad - lp := by dsimp only [lp]; omega
  have hops : padIntegralNoAltOps C.opts C.isNonneg C.ds =
      List.replicate lp (.char (fmtFillChar C.opts)) ++
        (writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++
          ([.str C.ds] ++ List.replicate (pad - lp) (.char (fmtFillChar C.opts)))) := by
    have h0 := padIntegralNoAltOps_of_not_bit24 C.opts C.isNonneg C.ds h24
    dsimp only [pad, lp] at hrp_eq ⊢
    rw [h0, writePrefixSignOp_fmtSignWord, hrp_eq]
  apply pi_ops_eq C hops
  have hsub : BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 C.opts.width.toNat) -
        BitVec.setWidth 32 (BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length))) =
      BitVec.ofNat 64 pad := sub32_zeroExtend_of_le (Nat.le_of_lt hgt) C.opts.width.isLt
  have hmod : (C.opts.flags >>> 29).toNat % 4 = 0 ∨
      (C.opts.flags >>> 29).toNat % 4 = 1 ∨
      (C.opts.flags >>> 29).toNat % 4 = 2 ∨
      (C.opts.flags >>> 29).toNat % 4 = 3 := by omega
  have hgo : ∀ (w : BitVec 32),
      BitVec.setWidth 32 (BitVec.setWidth 64 C.opts.flags >>> 29 &&& 3#64) = w →
      (∀ (sm : State),
        coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl sm.mem →
        FmtWriteFrame s sm →
        sm.pc = coreFmtPl00.base + 772#64 → sm.status = .Running →
        sm.sp = C.s0.sp - 112#64 →
        (sm.readReg64 (.gpr 19#5)).toNat = C.ds.length →
        sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 0 →
        sm.readReg64 (.gpr 21#5) = C.vt →
        sm.readReg64 (.gpr 23#5) = 0#64 →
        sm.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg →
        sm.readReg64 (.gpr 25#5) = C.out →
        sm.readReg32 (.gpr 26#5) = C.opts.flags →
        sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad →
        sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp →
        calleeSavedVRegs sm = calleeSavedVRegs C.s0 →
        PiWpp C sm
          (C.f ↦₆₄ C.out ∗ (C.f + 8#64) ↦₆₄ C.vt ∗ (C.f + 16#64) ↦₃₂ C.opts.flags ∗
            (C.f + 20#64) ↦₁₆ C.opts.width ∗ (C.f + 22#64) ↦₁₆ C.opts.precision ∗
            fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
            stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
            C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
          (List.replicate lp (.char (fmtFillChar C.opts)) ++
            (writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++
              ([.str C.ds] ++ List.replicate (pad - lp) (.char (fmtFillChar C.opts))))) st) := by
    intro _ _ sm hcl_sm hframe hpc_sm hrun_sm hsp_sm hx19_sm hx20_sm hx21_sm hx23_sm hw24_sm
      hx25_sm hw26_sm hx27_sm hx28_sm hvregs_sm
    refine pi_wpp_mono C
      (piLeftPadLoop_wpp C v0 hlp_le hpad_lt lp 0 st sm (by omega) hcl_sm
        hpc_sm hrun_sm hsp_sm hx19_sm hx20_sm hx21_sm hx23_sm hw24_sm hx25_sm hw26_sm
        hx27_sm hx28_sm hvregs_sm) ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (C.hw.transport st s sm hframe))))))))
      (Entails.of_eq (by dsimp only [formatterAt]; ac_rfl))
  rcases hmod with hm | hm | hm | hm
  · have halw : BitVec.setWidth 32 (BitVec.setWidth 64 C.opts.flags >>> 29 &&& 3#64) = 0#32 := by
      rw [alignWord_eq, hm]
    have hlp0 : lp = 0 := by
      dsimp only [lp]; unfold fmtPadSplit; simp only [hm]
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 772#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 572#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat :=
      (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
    have hx27' : s'.readReg64 (.gpr 27#5) =
        BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) :=
      (hcpu_in.readReg64 _).trans hx27
    dsimp only [formatterAt]; wp_conv_pre => simp only [sepConj_assoc]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => hgo 0#32 halw sm hcl_sm
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26')
        (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
        (by rw [hcpu_out.readReg64, hlp0]; simp [arm64_norm])
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
  · have halw : BitVec.setWidth 32 (BitVec.setWidth 64 C.opts.flags >>> 29 &&& 3#64) = 1#32 := by
      rw [alignWord_eq, hm]
    have hlp1 : lp = pad := by
      dsimp only [lp]; unfold fmtPadSplit; simp only [hm]
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 772#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 572#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat :=
      (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
    have hx27' : s'.readReg64 (.gpr 27#5) =
        BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) :=
      (hcpu_in.readReg64 _).trans hx27
    dsimp only [formatterAt]; wp_conv_pre => simp only [sepConj_assoc]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => hgo 1#32 halw sm hcl_sm
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26')
        (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
        (by rw [hcpu_out.readReg64, hlp1]
            simp only [arm64_norm]
            exact zext32_ofNat_of_lt (by omega))
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
  · have halw : BitVec.setWidth 32 (BitVec.setWidth 64 C.opts.flags >>> 29 &&& 3#64) = 2#32 := by
      rw [alignWord_eq, hm]
    have hlp2 : lp = pad / 2 := by
      dsimp only [lp]; unfold fmtPadSplit; simp only [hm]
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 772#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 572#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat :=
      (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
    have hx27' : s'.readReg64 (.gpr 27#5) =
        BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) :=
      (hcpu_in.readReg64 _).trans hx27
    dsimp only [formatterAt]; wp_conv_pre => simp only [sepConj_assoc]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => hgo 2#32 halw sm hcl_sm
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26')
        (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
        (by rw [hcpu_out.readReg64, hlp2]
            simp only [arm64_norm]
            rw [zext32_ofNat_of_lt (by omega)]
            exact half32_zeroExtend_of_lt hpad_lt)
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
  · have halw : BitVec.setWidth 32 (BitVec.setWidth 64 C.opts.flags >>> 29 &&& 3#64) = 3#32 := by
      rw [alignWord_eq, hm]
    have hlp3 : lp = pad := by
      dsimp only [lp]; unfold fmtPadSplit; simp only [hm]
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 772#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 572#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat :=
      (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
    have hx27' : s'.readReg64 (.gpr 27#5) =
        BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) :=
      (hcpu_in.readReg64 _).trans hx27
    dsimp only [formatterAt]; wp_conv_pre => simp only [sepConj_assoc]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => hgo 3#32 halw sm hcl_sm
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26')
        (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
        (by rw [hcpu_out.readReg64, hlp3]
            simp only [arm64_norm]
            exact zext32_ofNat_of_lt (by omega))
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)

theorem flags_bit21_mask (flags : BitVec 32) :
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 flags &&& 2097152#64) != 0#32) =
      flags.getLsbD 21 := by
  bv_slice

theorem flags_bit21_ubfx (flags : BitVec 32) :
    (BitVec.zeroExtend 64 flags >>> 21 &&& 1#64) =
      if flags.getLsbD 21 then 1#64 else 0#64 := by
  cases h : flags.getLsbD 21 <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> bv_slice

theorem w1_ne_zero {x : BitVec 64} {b : Bool}
    (h : BitVec.setWidth 32 x = if b then 1#32 else 0#32) :
    (BitVec.setWidth 32 x != 0#32) = b := by
  rw [h]; cases b <;> decide

theorem piDispatch104_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 v1 : BitVec 64) {st : σ} {s : State}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 104#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat)
    (hx21 : s.readReg64 (.gpr 21#5) = C.f)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (hw24 : s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.setWidth 64 C.opts.flags)
    (hx27 : s.readReg64 (.gpr 27#5) =
      BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length))
    (hx28 : s.readReg64 (.gpr 28#5) = C.dsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 v1)
      (padIntegralNoAltOps C.opts C.isNonneg C.ds) st := by
  have hsl : (fmtSignOp C.opts C.isNonneg).length ≤ 1 := by
    unfold fmtSignOp; split <;> (try split) <;> simp
  have hw_lt := C.opts.width.isLt
  have hds := C.hds_lt
  by_cases hle : C.opts.width.toNat ≤ (fmtSignOp C.opts C.isNonneg).length + C.ds.length
  · apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 112#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 104#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' := (hcpu_in.readReg64 (.gpr 20#5)).trans hx20
    have hx27' := (hcpu_in.readReg64 (.gpr 27#5)).trans hx27
    have hc : (BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length)).ult
        (BitVec.ofNat 64 C.opts.width.toNat) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piNoPad_wpp C v0 v1 hle hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28)
        (by rw [hcpu_out.calleeSavedVRegs]
            simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (C.hw.transport st s sm hframe)))
  · have hgt : (fmtSignOp C.opts C.isNonneg).length + C.ds.length < C.opts.width.toNat := by
      omega
    have hc : (BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length)).ult
        (BitVec.ofNat 64 C.opts.width.toNat) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    by_cases h24 : C.opts.flags.getLsbD 24 = true
    · have h24' : (BitVec.setWidth 64 C.opts.flags).getLsbD 24 = true := by simpa using h24
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 600#64)
      intro s' hcpu_in
      have hpc' : s'.pc = coreFmtPl00.base + 104#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hx20' := (hcpu_in.readReg64 (.gpr 20#5)).trans hx20
      have hx26' := (hcpu_in.readReg64 (.gpr 26#5)).trans hx26
      have hx27' := (hcpu_in.readReg64 (.gpr 27#5)).trans hx27
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hal0 : (C.s0.sp &&& 15#64 == 0#64) = true := by
        simpa [State.spAligned] using C.hsp_al0
      dsimp only [piSavedSlots]; wp_conv_pre => simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      rw [(hcpu_in.readReg64 (.gpr 28#5)).trans hx28]
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hpseg => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piZeroPad_wpp C v0 hgt h24 hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hsp')
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx20')
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21)
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
          (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx27')
          (by rw [hcpu_out.calleeSavedVRegs]
              simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (C.hw.transport st s sm hframe)))
    · have h24' : (BitVec.setWidth 64 C.opts.flags).getLsbD 24 = false := by simpa using h24
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 572#64)
      intro s' hcpu_in
      have hpc' : s'.pc = coreFmtPl00.base + 104#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hx20' := (hcpu_in.readReg64 (.gpr 20#5)).trans hx20
      have hx26' := (hcpu_in.readReg64 (.gpr 26#5)).trans hx26
      have hx27' := (hcpu_in.readReg64 (.gpr 27#5)).trans hx27
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hal0 : (C.s0.sp &&& 15#64 == 0#64) = true := by
        simpa [State.spAligned] using C.hsp_al0
      dsimp only [piSavedSlots]; wp_conv_pre => simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      rw [(hcpu_in.readReg64 (.gpr 28#5)).trans hx28]
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hpseg => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piAlignPad_wpp C v0 hgt (by simpa using h24) hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hsp')
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx20')
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21)
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
          (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
          (by rw [hcpu_out.readReg32]; simp [arm64_norm, hx26'])
          (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx27')
          (by rw [hcpu_out.calleeSavedVRegs]
              simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (C.hw.transport st s sm hframe)))

theorem piPrologue_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    {st : σ}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl C.s0.mem)
    (hpc : C.s0.pc = coreFmtPl00.base) (hrun : C.s0.status = .Running)
    (hx0 : C.s0.readReg64 .x0 = C.f)
    (hw1 : C.s0.readReg32 .x1 = if C.isNonneg then 1#32 else 0#32)
    (hx4 : C.s0.readReg64 .x4 = C.dsPtr)
    (hx5 : (C.s0.readReg64 .x5).toNat = C.ds.length) :
    PiWpp C C.s0
      (stackFrameAt C.s0.sp 112 ∗ formatterAt C.f C.out C.vt C.opts ∗
        fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st C.s0 ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ C.vtSlots)
      (padIntegralNoAltOps C.opts C.isNonneg C.ds) st := by
  rw [stackFrameAt_112_unpack C.s0.sp]
  dsimp only [PiWpp]
  apply sepWPp_sepExists_left; intro v0
  apply sepWPp_sepExists_left; intro v1
  iterate 12 (apply sepWPp_sepExists_left; intro _)
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 104#64)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 0#64 := by
    rw [hcpu_in.pc_eq, hpc]; bv_omega
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp := hcpu_in.sp_eq
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans C.hsp_al0
  have hx0' : s'.readReg64 .x0 = C.f := (hcpu_in.readReg64 .x0).trans hx0
  have hw1' : s'.readReg32 .x1 = if C.isNonneg then 1#32 else 0#32 :=
    (hcpu_in.readReg32 .x1).trans hw1
  have hx4' : s'.readReg64 .x4 = C.dsPtr := (hcpu_in.readReg64 .x4).trans hx4
  dsimp only [formatterAt]
  wp_conv_pre => simp only [sepConj_assoc]
  have hal0 : (C.s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using C.hsp_al0
  have h23 : (BitVec.zeroExtend 64 C.opts.flags).getLsbD 23 = false := by
    simpa using C.hnoalt
  have hx5' : (s'.readReg64 .x5).toNat = C.ds.length := by rw [hcpu_in.readReg64]; exact hx5
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  have hw1n : BitVec.setWidth 32 (s'.readReg64 (.gpr 1#5)) =
      if C.isNonneg then 1#32 else 0#32 := by simpa [arm64_norm] using hw1'
  have hb1 := w1_ne_zero hw1n
  have hx5v : s'.readReg64 (.gpr 5#5) = BitVec.ofNat 64 C.ds.length := by
    have h5 : (s'.readReg64 (.gpr 5#5)).toNat = C.ds.length := hx5'
    apply BitVec.eq_of_toNat_eq; have := C.hds_lt; simp only [BitVec.toNat_ofNat]; omega
  have hframe : FmtWriteFrame C.s0 sm := fmtWriteFrame_of_pureSeg hpseg
    (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
    (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  simp only [hcpu_in.readReg64]
  refine pi_wpp_mono C
    (piDispatch104_wpp C v0 v1 hcl_sm
      (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by rw [hcpu_out.sp_eq]; simp [arm64_norm])
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx5')
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm]
          apply BitVec.eq_of_toNat_eq; simp)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm])
      (by rw [hcpu_out.readReg32]; simp only [arm64_norm, hb1, flags_bit21_mask]
          by_cases h21 : C.opts.flags.getLsbD 21 <;> cases C.isNonneg <;>
            simp [h21, fmtSignWord])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm])
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm, hb1, flags_bit21_ubfx, hx5v]
          unfold fmtSignOp
          generalize C.opts.flags.getLsbD 21 = b21
          have := C.hds_lt
          cases b21 <;> cases C.isNonneg <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm])
      (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs))
    ?_
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (C.hw.transport st C.s0 sm hframe))))
  exact Entails.of_eq (by dsimp only [piSavedSlots, piSavedRegs, formatterAt]; ac_rfl)

end PadIntegralProof

open PadIntegralProof

/-- Placement-generic correctness of `<core::fmt::Formatter>::pad_integral` (`coreFmtMultiLib`
    block `0`, calling `write_prefix` in block `5`) against `formatterPadIntegralSpec`
    (`opts.flags.getLsbD 23 = false`). -/
theorem formatterPadIntegral_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib padIntegralKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (f : BitVec 64) (opts : FmtOptions) (isNonneg ro : Bool) (dsPtr : BitVec 64)
    (ds : List (BitVec 8)) :
    subroutine_ok P (coreFmtMultiLib.resolve mpl formatterPadIntegralSym)
      (coreFmtMultiLib.withCodeLoadedWhere padIntegralKeep mpl
        (formatterPadIntegralSpec W StrStep CharStep Panic Oom stackBytes
          f out vt opts isNonneg ro dsPtr ds)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [resolve_padIntegral hpl, show mpl = coreFmtMpl from rfl]
  apply subroutine_ok_of_sepWPp_init
  intro st R s0 hpc hrun hpre hsp_al
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec] at hpre
  rw [sepConj_comm _ ⌜coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hw1, hx4, hx5, hds_lt, hnoalt⟩, hpre⟩
  have hstack : 160 + stackBytes ≤ 2 ^ 64 :=
    stackFrameAt_le_of_pointsTo64 (a := f) (v := out)
      (R := ((f + 8#64) ↦₆₄ vt) ∗ ((f + 16#64) ↦₃₂ opts.flags) ∗
        ((f + 20#64) ↦₁₆ opts.width) ∗ ((f + 22#64) ↦₁₆ opts.precision) ∗
        fmtSrcBytes ro dsPtr ds ∗ W st s0 ∗ R)
      (Satisfies.of_eq hpre (by dsimp only [formatterAt]; ac_rfl))
  let C : PiCtx σ P :=
    { W := W, StrStep := StrStep, CharStep := CharStep, Panic := Panic, Oom := Oom,
      stackBytes := stackBytes, hext := hext, f := f, out := out, vt := vt, wsFn := wsFn,
      wcFn := wcFn, opts := opts, isNonneg := isNonneg, ro := ro, dsPtr := dsPtr, ds := ds,
      hw := hw, s0 := s0, R := R, hsp_al0 := hsp_al, hstack := hstack, hds_lt := hds_lt,
      hnoalt := hnoalt }
  have hsplit : stackFrameAt s0.sp (160 + stackBytes) =
      stackFrameAt s0.sp 112 ∗ stackFrameAt (s0.sp - 112#64) (48 + stackBytes) := by
    rw [show 160 + stackBytes = 112 + (48 + stackBytes) by omega]
    exact stackFrameAt_split s0.sp 112 (48 + stackBytes) (by omega)
  rw [hsplit, hw.slots st s0] at hpre
  refine ⟨stackFrameAt s0.sp 112 ∗ formatterAt f out vt opts ∗ fmtSrcBytes ro dsPtr ds ∗
      W st s0 ∗ stackFrameAt (s0.sp - 112#64) (48 + stackBytes) ∗
      (((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ ((vt + 0x20#64) ↦₆₄ᵣ wcFn)),
    Satisfies.of_eq hpre (by ac_rfl), ?_⟩
  exact piPrologue_wpp C (st := st) hcl hpc hrun hx0 hw1 hx4 hx5

end VerifiedLibraries.RustStd
