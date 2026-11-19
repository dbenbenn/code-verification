/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.PadIntegralCtx

/-!
# `pad_integral` No-Pad, Zero-Pad, and Fill-Loop Paths

Verifies the `width ≤ len` path (`piNoPad_wpp`), the `SIGN_AWARE_ZERO_PAD` path (`piZeroPad_wpp`),
and the alignment fill loops (`piLeftPadLoop_wpp`, `piAlignMid32c_wpp`, `piRightPadLoop_wpp`) of
`core::fmt::Formatter::pad_integral`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd.CoreFmt

namespace PadIntegralProof

arm64_proof_prelude
set_option linter.literalFetch false

theorem sub32_zeroExtend_of_le {a b : Nat} (hle : b ≤ a) (ha : a < 65536) :
    BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 a) -
      BitVec.setWidth 32 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem cs_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rw [CalleeSavedPreserved.iff_regs] at h01 h12 ⊢
  exact ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2.2⟩

theorem piZeroPad_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 : BitVec 64) {st : σ} {s : State}
    (hgt : (fmtSignOp C.opts C.isNonneg).length + C.ds.length < C.opts.width.toNat)
    (h24 : C.opts.flags.getLsbD 24 = true)
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 600#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat)
    (hx21 : s.readReg64 (.gpr 21#5) = C.f)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (hw24 : s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg)
    (hx27 : s.readReg64 (.gpr 27#5) =
      BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      (padIntegralNoAltOps C.opts C.isNonneg C.ds) st := by
  let pad := C.opts.width.toNat - ((fmtSignOp C.opts C.isNonneg).length + C.ds.length)
  have hpad_lt : pad < 65536 := by have := C.opts.width.isLt; omega
  have hops : padIntegralNoAltOps C.opts C.isNonneg C.ds =
      writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++
        (List.replicate pad (.char 0x30#32) ++ [.str C.ds]) := by
    dsimp only [pad]
    rw [padIntegralNoAltOps_of_bit24 C.opts C.isNonneg C.ds h24, writePrefixSignOp_fmtSignWord]
  apply pi_ops_eq C hops
  rw [pi_formatterAt_triple C.f C.out C.vt C.opts]
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 644#64)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 600#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm1 hcpu1_out hcl_sm1 hpseg1 => ?_
  have hframe1 : FmtWriteFrame s sm1 :=
    fmtWriteFrame_of_pureSeg hpseg1
      (by rw [hcpu1_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu1_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  have hpc1 : sm1.pc = coreFmtPl00.base + 644#64 := by rw [hcpu1_out.pc_eq]; simp [arm64_norm]
  have hrun1 : sm1.status = .Running := by rw [hcpu1_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp1 : sm1.sp = C.s0.sp - 112#64 := by
    rw [hcpu1_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp
  have hx0_1 : sm1.readReg64 .x0 = C.out := by rw [hcpu1_out.readReg64 .x0]; simp [arm64_norm]
  have hx1_1 : sm1.readReg64 .x1 = C.vt := by rw [hcpu1_out.readReg64 .x1]; simp [arm64_norm]
  have hw2_1 : sm1.readReg32 .x2 = fmtSignWord C.opts C.isNonneg := by
    rw [hcpu1_out.readReg32 .x2]; simpa [arm64_norm, hcpu_in.readReg64] using hw24
  have hx3_1 : sm1.readReg64 .x3 = 0#64 := by
    rw [hcpu1_out.readReg64 .x3]; simpa [arm64_norm, hcpu_in.readReg64] using hx23
  have hx19_1 : (sm1.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
  have hx20_1 : sm1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx20
  have hx21_1 : sm1.readReg64 (.gpr 21#5) = C.f := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm] using hx21'
  have hx25_1 : sm1.readReg64 (.gpr 25#5) = C.out := by rw [hcpu1_out.readReg64]; simp [arm64_norm]
  have hx26_1 : sm1.readReg64 (.gpr 26#5) = C.vt := by rw [hcpu1_out.readReg64]; simp [arm64_norm]
  have hx27_1 : sm1.readReg64 (.gpr 27#5) =
      BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx27
  have hx28_1 : sm1.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags := by
    rw [hcpu1_out.readReg64]; simp [arm64_norm]
  have hvregs_1 : calleeSavedVRegs sm1 = calleeSavedVRegs C.s0 := by
    rw [hcpu1_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  refine sepWPp_mono_pre
    (P2 := formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st sm1 ∗
      stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
      C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
    (Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm1 hframe1))))))
      (Entails.of_eq (by rw [pi_formatterAt_triple C.f C.out C.vt C.opts]; ac_rfl))) ?_
  let optsMut : FmtOptions :=
    { C.opts with flags := sm1.readReg32 (.gpr 8#5) }
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sm1 (mid := coreFmtPl05.base)
  intro s2 hcpu2_in
  have hpc2 : s2.pc = coreFmtPl00.base + 644#64 := hcpu2_in.pc_eq.trans hpc1
  have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrun1
  have hx21_2 : s2.readReg64 (.gpr 21#5) = C.f := (hcpu2_in.readReg64 _).trans hx21_1
  have hw8_2 : s2.readReg32 (.gpr 8#5) = optsMut.flags := hcpu2_in.readReg32 _
  dsimp only [formatterAt]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc1
  wp_sym_steps
  refine SepWP.done
    (by simpa [arm64_norm] using bl_target_writePrefix 648#64)
    (by simpa [arm64_norm] using hrun2)
    fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
  have hpc_sm2 : sm2.pc = coreFmtPl05.base := by
    rw [hcpu2_out.pc_eq]; simpa [arm64_norm] using bl_target_writePrefix 648#64
  have hrun_sm2 : sm2.status = .Running := by
    rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2
  have hsp_sm2 : sm2.sp = C.s0.sp - 112#64 := by
    rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hsp1
  have hlr_sm2 : sm2.readReg64 Reg.lr = coreFmtPl00.base + 652#64 := by
    rw [hcpu2_out.readReg64 Reg.lr]; simp [arm64_norm]
  have hx0_sm2 : sm2.readReg64 .x0 = C.out := by
    rw [hcpu2_out.readReg64 .x0]; simpa [arm64_norm, hcpu2_in.readReg64] using hx0_1
  have hx1_sm2 : sm2.readReg64 .x1 = C.vt := by
    rw [hcpu2_out.readReg64 .x1]; simpa [arm64_norm, hcpu2_in.readReg64] using hx1_1
  have hw2_sm2 : sm2.readReg32 .x2 = fmtSignWord C.opts C.isNonneg := by
    rw [hcpu2_out.readReg32 .x2]; simpa [arm64_norm, hcpu2_in.readReg64] using hw2_1
  have hx3_sm2 : sm2.readReg64 .x3 = 0#64 := by
    rw [hcpu2_out.readReg64 .x3]; simpa [arm64_norm, hcpu2_in.readReg64] using hx3_1
  have hx19_sm2 : (sm2.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx19_1
  have hx20_sm2 : sm2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx20_1
  have hx21_sm2 : sm2.readReg64 (.gpr 21#5) = C.f := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm] using hx21_2
  have hx25_sm2 : sm2.readReg64 (.gpr 25#5) = C.out := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx25_1
  have hx26_sm2 : sm2.readReg64 (.gpr 26#5) = C.vt := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx26_1
  have hx27_sm2 : sm2.readReg64 (.gpr 27#5) =
      BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx27_1
  have hx28_sm2 : sm2.readReg64 (.gpr 28#5) = (C.opts.precision ++ C.opts.width) ++ C.opts.flags := by
    rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64] using hx28_1
  have hvregs_sm2 : calleeSavedVRegs sm2 = calleeSavedVRegs C.s0 := by
    rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_1
  have hframe2 : FmtWriteFrame sm1 sm2 :=
    fmtWriteFrame_of_pureSeg hpseg2
      (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
      (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
  refine pi_wpp_mono C
    (piCallWritePrefix_wpp C
      (F := formatterAt C.f C.out C.vt optsMut ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      hcl_sm2 hpc_sm2 hrun_sm2 hsp_sm2 hlr_sm2 hx0_sm2 hx1_sm2 hw2_sm2 hx3_sm2 ?_) ?_
  · intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hrun_pfx
    have hvregs_sf := (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm2
    rw [CalleeSavedPreserved.iff_regs] at hcsf
    rcases hcsf with ⟨h19f, h20f, h21f, _, _, _, h25f, h26f, h27f, h28f, _, _⟩
    cases ok with
    | false =>
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 864#64)
      intro s3 hcpu3_in
      have hpc3 : s3.pc = coreFmtPl00.base + 652#64 := hcpu3_in.pc_eq.trans hpcf
      have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf
      have hw0_3 : s3.readReg32 .x0 = 1#32 := (hcpu3_in.readReg32 .x0).trans hw0f
      simp [arm64_norm] at hw0_3
      clear hpcf
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
        fun sm3 hcpu3_out hcl_sm3 hpseg3 => ?_
      have hframe3 : FmtWriteFrame sf sm3 :=
        fmtWriteFrame_of_pureSeg hpseg3
          (by rw [hcpu3_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
          (by rw [hcpu3_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piExitErr360_wpp C optsMut v0 C.dsPtr hcl_sm3
          (by rw [hcpu3_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu3_out.status_eq]; simpa [arm64_norm] using hrun3)
          (by rw [hcpu3_out.sp_eq]; simpa [arm64_norm] using hcpu3_in.sp_eq.trans hspf)
          (by rw [hcpu3_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf)
          (FmtOpsRun.append_err _ hrun_pfx)) ?_
      exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm3 hframe3))
        (Entails.of_eq (by ac_rfl))
    | true =>
      refine pi_ops_ok_conseq C hrun_pfx ?_
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 664#64)
      intro s3 hcpu3_in
      have hpc3 : s3.pc = coreFmtPl00.base + 652#64 := hcpu3_in.pc_eq.trans hpcf
      have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf
      have hw0_3 : s3.readReg32 .x0 = 0#32 := (hcpu3_in.readReg32 .x0).trans hw0f
      have hx20_3 : s3.readReg64 (.gpr 20#5) = BitVec.ofNat 64 C.opts.width.toNat :=
        (hcpu3_in.readReg64 _).trans (h20f.trans hx20_sm2)
      have hx27_3 : s3.readReg64 (.gpr 27#5) =
          BitVec.ofNat 64 ((fmtSignOp C.opts C.isNonneg).length + C.ds.length) :=
        (hcpu3_in.readReg64 _).trans (h27f.trans hx27_sm2)
      simp [arm64_norm] at hw0_3
      clear hpcf
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
        fun sm3 hcpu3_out hcl_sm3 hpseg3 => ?_
      have hframe3 : FmtWriteFrame sf sm3 :=
        fmtWriteFrame_of_pureSeg hpseg3
          (by rw [hcpu3_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
          (by rw [hcpu3_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piZeroPadLoop_wpp C optsMut v0 hpad_lt pad 0 st' sm3 (by omega) hcl_sm3
          (by rw [hcpu3_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu3_out.status_eq]; simpa [arm64_norm] using hrun3)
          (by rw [hcpu3_out.sp_eq]; simpa [arm64_norm] using hcpu3_in.sp_eq.trans hspf)
          (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h19f] using hx19_sm2)
          (by rw [hcpu3_out.readReg64]
              simpa [arm64_norm] using sub32_zeroExtend_of_le (Nat.le_of_lt hgt) C.opts.width.isLt)
          (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h21f] using hx21_sm2)
          (by rw [hcpu3_out.readReg64]; simp [arm64_norm])
          (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h25f] using hx25_sm2)
          (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h26f] using hx26_sm2)
          (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h28f] using hx28_sm2)
          (by rw [hcpu3_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf)) ?_
      exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm3 hframe3))
        (Entails.of_eq (by ac_rfl))
  · rw [hcpu2_in.readReg64 (.gpr 8#5)]
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (C.hw.transport st sm1 sm2 hframe2))))))))
      (Entails.of_eq (by dsimp only [formatterAt]; ac_rfl))

theorem piNoPad_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 v1 : BitVec 64) {st : σ} {s : State}
    (hle : C.opts.width.toNat ≤ (fmtSignOp C.opts C.isNonneg).length + C.ds.length)
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 112#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx21 : s.readReg64 (.gpr 21#5) = C.f)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (hw24 : s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg)
    (hx28 : s.readReg64 (.gpr 28#5) = C.dsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 v1)
      (padIntegralNoAltOps C.opts C.isNonneg C.ds) st := by
  have hops : padIntegralNoAltOps C.opts C.isNonneg C.ds =
      writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++ [.str C.ds] := by
    rw [padIntegralNoAltOps_of_pad_zero C.opts C.isNonneg C.ds hle, writePrefixSignOp_fmtSignWord]
  apply pi_ops_eq C hops
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl05.base)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 112#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hx21' : s'.readReg64 (.gpr 21#5) = C.f := (hcpu_in.readReg64 _).trans hx21
  dsimp only [formatterAt]
  wp_conv_pre => simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done
    (by simpa [arm64_norm] using bl_target_writePrefix 136#64)
    (by simpa [arm64_norm] using hrun')
    fun sm1 hcpu1_out hcl_sm1 hpseg1 => ?_
  have hframe1 : FmtWriteFrame s sm1 :=
    fmtWriteFrame_of_pureSeg hpseg1
      (by rw [hcpu1_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu1_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  have hpc_sm1 : sm1.pc = coreFmtPl05.base := by
    rw [hcpu1_out.pc_eq]; simpa [arm64_norm] using bl_target_writePrefix 136#64
  have hrun_sm1 : sm1.status = .Running := by
    rw [hcpu1_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm1 : sm1.sp = C.s0.sp - 112#64 := by
    rw [hcpu1_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp
  have hlr_sm1 : sm1.readReg64 Reg.lr = coreFmtPl00.base + 140#64 := by
    rw [hcpu1_out.readReg64 Reg.lr]; simp [arm64_norm]
  have hx0_sm1 : sm1.readReg64 .x0 = C.out := by rw [hcpu1_out.readReg64 .x0]; simp [arm64_norm]
  have hx1_sm1 : sm1.readReg64 .x1 = C.vt := by rw [hcpu1_out.readReg64 .x1]; simp [arm64_norm]
  have hw2_sm1 : sm1.readReg32 .x2 = fmtSignWord C.opts C.isNonneg := by
    rw [hcpu1_out.readReg32 .x2]; simpa [arm64_norm, hcpu_in.readReg64] using hw24
  have hx3_sm1 : sm1.readReg64 .x3 = 0#64 := by
    rw [hcpu1_out.readReg64 .x3]; simpa [arm64_norm, hcpu_in.readReg64] using hx23
  have hx19_sm1 : (sm1.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
  have hx21_sm1 : sm1.readReg64 (.gpr 21#5) = C.vt := by rw [hcpu1_out.readReg64]; simp [arm64_norm]
  have hx25_sm1 : sm1.readReg64 (.gpr 25#5) = C.out := by rw [hcpu1_out.readReg64]; simp [arm64_norm]
  have hx28_sm1 : sm1.readReg64 (.gpr 28#5) = C.dsPtr := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28
  have hvregs_sm1 : calleeSavedVRegs sm1 = calleeSavedVRegs C.s0 := by
    rw [hcpu1_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  refine pi_wpp_mono C
    (piCallWritePrefix_wpp C
      (F := formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 v1)
      hcl_sm1 hpc_sm1 hrun_sm1 hsp_sm1 hlr_sm1 hx0_sm1 hx1_sm1 hw2_sm1 hx3_sm1 ?_) ?_
  · intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hrun_pfx
    have hvregs_sf := (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm1
    rw [CalleeSavedPreserved.iff_regs] at hcsf
    rcases hcsf with ⟨h19f, _, h21f, _, _, _, h25f, _, _, h28f, _, _⟩
    cases ok with
    | false =>
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 864#64)
      intro s3 hcpu3_in
      have hpc3 : s3.pc = coreFmtPl00.base + 140#64 := hcpu3_in.pc_eq.trans hpcf
      have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf
      have hw0_3 : s3.readReg32 .x0 = 1#32 := (hcpu3_in.readReg32 .x0).trans hw0f
      simp [arm64_norm] at hw0_3
      clear hpcf
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
        fun sm3 hcpu3_out hcl_sm3 hpseg3 => ?_
      have hframe3 : FmtWriteFrame sf sm3 :=
        fmtWriteFrame_of_pureSeg hpseg3
          (by rw [hcpu3_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
          (by rw [hcpu3_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piExitErr360_wpp C C.opts v0 v1 hcl_sm3
          (by rw [hcpu3_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu3_out.status_eq]; simpa [arm64_norm] using hrun3)
          (by rw [hcpu3_out.sp_eq]; simpa [arm64_norm] using hcpu3_in.sp_eq.trans hspf)
          (by rw [hcpu3_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf)
          (FmtOpsRun.append_err _ hrun_pfx)) ?_
      exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm3 hframe3))
        (Entails.of_eq (by ac_rfl))
    | true =>
      refine pi_ops_ok_conseq C hrun_pfx ?_
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := C.wsFn)
      intro s3 hcpu3_in
      have hpc3 : s3.pc = coreFmtPl00.base + 140#64 := hcpu3_in.pc_eq.trans hpcf
      have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf
      have hsp3 : s3.sp = C.s0.sp - 112#64 := hcpu3_in.sp_eq.trans hspf
      have hsp_al3 : s3.spAligned = true := hcpu3_in.spAligned.trans (C.sp1_aligned hspf)
      have hw0_3 : s3.readReg32 .x0 = 0#32 := (hcpu3_in.readReg32 .x0).trans hw0f
      have hx21_3 : s3.readReg64 (.gpr 21#5) = C.vt :=
        (hcpu3_in.readReg64 _).trans (h21f.trans hx21_sm1)
      simp [arm64_norm] at hw0_3
      dsimp only [PiCtx.vtSlots, piSavedSlots, piSavedRegs]
      wp_conv_pre => simp only [sepConj_assoc]
      clear hpcf
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
        fun sm2 hcpu2_out _hcl_sm2 hpseg2 => ?_
      have hframe2 : FmtWriteFrame sf sm2 :=
        fmtWriteFrame_of_pureSeg hpseg2
          (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
          (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
      have hpc_sm2 : sm2.pc = C.wsFn := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
      have hrun_sm2 : sm2.status = .Running := by
        rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun3
      have hsp_sm2 : sm2.sp = C.s0.sp := by rw [hcpu2_out.sp_eq]; simp [arm64_norm]
      have hsp_al_sm2 : sm2.spAligned = true := by
        simp only [State.spAligned, hsp_sm2]; simpa [State.spAligned] using C.hsp_al0
      have hlr_sm2 : sm2.readReg64 Reg.lr = C.s0.readReg64 Reg.lr := by
        rw [hcpu2_out.readReg64 Reg.lr]; simp [arm64_norm]
      have hx0_sm2 : sm2.readReg64 .x0 = C.out := by
        rw [hcpu2_out.readReg64 .x0]; simpa [arm64_norm, hcpu3_in.readReg64, h25f] using hx25_sm1
      have hx1_sm2 : sm2.readReg64 .x1 = C.dsPtr := by
        rw [hcpu2_out.readReg64 .x1]; simpa [arm64_norm, hcpu3_in.readReg64, h28f] using hx28_sm1
      have hx2_sm2 : (sm2.readReg64 .x2).toNat = C.ds.length := by
        rw [hcpu2_out.readReg64 .x2]; simpa [arm64_norm, hcpu3_in.readReg64, h19f] using hx19_sm1
      have hcs_sm2 : CalleeSavedPreserved C.s0 sm2 := by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf⟩ <;>
          (rw [hcpu2_out.readReg64]; simp [arm64_norm])
      have h160a : 112 + (48 + C.stackBytes) = 160 + C.stackBytes := by omega
      have h160b : C.stackBytes + 160 = 160 + C.stackBytes := by omega
      have hsp_splitA := stackFrameAt_split C.s0.sp 112 (48 + C.stackBytes) (h160a.symm ▸ C.hstack)
      have hsp_splitB := stackFrameAt_split C.s0.sp C.stackBytes 160 (h160b.symm ▸ C.hstack)
      refine pi_wpp_mono C
        (P2 := fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sm2 ∗ stackFrameAt C.s0.sp C.stackBytes ∗
          (formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots ∗
            stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 160))
        ?_ ?_
      · refine SepWPp.call_wpp (C.hw.write_str C.ro C.dsPtr C.ds)
          (x := st')
          (F := formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots ∗
            stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 160)
          hpc_sm2 hrun_sm2 hsp_al_sm2 hlr_sm2 ?_ ?_ ?_ ?_ ?_
        · intro R' hm
          dsimp only [fmtWriterStrSpec]
          rw [hsp_sm2, pure_sepConj_of_true ⟨hx0_sm2, hx1_sm2, hx2_sm2, C.hds_lt⟩]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        · intro sf2 _ R' _ hmf; exact not_satisfies_false_sepConj hmf
        · intro sf2 _ _ hm
          dsimp only [fmtWriterStrSpec, PiQp] at hm ⊢
          have hm1 : sf2.mem ⊨ (⌜C.Panic st' C.ds.length sf2⌝ ∗
              (anyHeap ∗ (formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots ∗
                stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 160))) ∗ C.R := by
            simpa [sepConj_assoc] using hm
          rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
          exact ⟨FmtOpsAbort.of_head (op := .str C.ds) hm1.1,
            Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm1.2⟩
        · intro sf2 hpcf2 hrunf2 hspf2 hcsf2
          dsimp only [fmtWriterStrSpec]
          apply sepWPp_sepExists_left; intro ok2
          apply sepWPp_sepExists_left; intro st''
          rw [sepConj_assoc]
          apply sepWPp_pure_left; rintro ⟨hw0_sf2, hsstep⟩
          refine SepWPp.done hpcf2 hrunf2 ⟨fun hmf => ?_, hspf2.trans hsp_sm2, cs_trans hcs_sm2 hcsf2⟩
          have hfmt : formatterAt C.f C.out C.vt C.opts ⊢
              if ok2 then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24 := by
            cases ok2
            · exact pi_formatterAt_memRegion24 C.f C.out C.vt C.opts
            · exact Entails.refl _
          have hrun_str : FmtOpsRun C.StrStep C.CharStep [.str C.ds] st' ok2 st'' := by
            cases ok2
            · exact .str_err hsstep
            · exact .str_ok hsstep (.nil st'')
          have hent :
              fmtSrcBytes C.ro C.dsPtr C.ds ∗ (C.W st'' sf2 ∗ (stackFrameAt sm2.sp C.stackBytes ∗
                (formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots ∗
                  stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 160))) ⊢
              C.vtSlots ∗ ((if ok2 then formatterAt C.f C.out C.vt C.opts else memRegion C.f 24) ∗
                fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st'' sf2 ∗
                stackFrameAt C.s0.sp (160 + C.stackBytes)) := by
            rw [hsp_sm2, ← h160b, hsp_splitB]
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hfmt))))
              (Entails.of_eq (by ac_rfl))
          have hm1 := Satisfies.mono (sepConj_mono_left hent) (by simpa [sepConj_assoc] using hmf)
          rw [sepConj_assoc] at hm1
          dsimp only [PiPost]
          refine Satisfies.mono (sepConj_mono_left ?_) (Satisfies.drop_left hm1)
          refine Entails.sepExists_right ok2 (Entails.sepExists_right st'' ?_)
          rw [pure_sepConj_of_true ⟨hw0_sf2, hrun_str⟩]
          exact Entails.refl _
        · intro sf2 R' _ hmo
          dsimp only [fmtWriterStrSpec, PiOom] at hmo ⊢
          rw [satisfies_pure_sepConj] at hmo ⊢
          exact ⟨FmtOpsAbort.of_head (op := .str C.ds) hmo.1, Satisfies.drop_left hmo.2⟩
      · have hfold :
            stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ piSavedSlots C.s0 v0 v1 ⊢
            stackFrameAt C.s0.sp C.stackBytes ∗
              stackFrameAt (C.s0.sp - BitVec.ofNat 64 C.stackBytes) 160 := by
          rw [← hsp_splitB, h160b, ← h160a, hsp_splitA, sepConj_comm]
          exact sepConj_mono_left (piSavedSlots_fold C.s0 v0 v1)
        refine Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2)) ?_
        refine Entails.trans (Entails.of_eq (show
            C.W st' sm2 ∗ (stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
              (formatterAt C.f C.out C.vt C.opts ∗ (fmtSrcBytes C.ro C.dsPtr C.ds ∗
                (((C.vt + 0x18#64) ↦₆₄ᵣ C.wsFn) ∗ (((C.vt + 0x20#64) ↦₆₄ᵣ C.wcFn) ∗
                  (((C.s0.sp - 112#64) ↦₆₄ v0) ∗ (((C.s0.sp - 104#64) ↦₆₄ v1) ∗
                    piSavedRegs C.s0))))))) =
            (stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗ piSavedSlots C.s0 v0 v1) ∗
              (fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st' sm2 ∗
                formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots) by
            dsimp only [PiCtx.vtSlots, piSavedSlots, piSavedRegs]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfold) (Entails.of_eq (by ac_rfl))
  · exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (C.hw.transport st s sm1 hframe1))))))))
      (Entails.of_eq (by dsimp only [formatterAt]; ac_rfl))

theorem fillChar_and32 (opts : FmtOptions) {M : BitVec 64}
    (hM : BitVec.setWidth 32 M = 0x1fffff#32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 opts.flags &&& M) = fmtFillChar opts := by
  dsimp only [fmtFillChar]
  rw [BitVec.setWidth_and, hM]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := opts.flags.isLt
  omega

theorem piRightPadLoop_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 : BitVec 64) {rp : Nat} (hrp : rp < 65536) :
    ∀ (rem cnt : Nat) (st : σ) (s : State),
      cnt + rem = rp →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem →
      s.pc = coreFmtPl00.base + 912#64 →
      s.status = .Running →
      s.sp = C.s0.sp - 112#64 →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt →
      s.readReg64 (.gpr 21#5) = C.vt →
      s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 rp →
      s.readReg64 (.gpr 25#5) = C.out →
      s.readReg32 (.gpr 26#5) = C.opts.flags →
      calleeSavedVRegs s = calleeSavedVRegs C.s0 →
      PiWpp C s
        (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
          stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        (List.replicate rem (.char (fmtFillChar C.opts))) st := by
  intro rem
  induction rem with
  | zero =>
    intro cnt st s hsum hcl hpc hrun hsp hx20 hx21 hx22 hx25 _hw26 hvregs
    have hcnt : cnt = rp := by omega
    subst hcnt
    have hcmp := loop_cmp_eq cnt
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 868#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 912#64 := hcpu_in.pc_eq.trans hpc
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
      (piEpilogue364_wpp C true v0 C.dsPtr hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg32]; simp [arm64_norm])
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
        (.nil st)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe)))
  | succ k ih =>
    intro cnt st s hsum hcl hpc hrun hsp hx20 hx21 hx22 hx25 hw26 hvregs
    have hlt : cnt < rp := by omega
    have hcmp := loop_cmp_lt hlt hrp
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := C.wcFn)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 912#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
    have hx22' : s'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 rp := (hcpu_in.readReg64 _).trans hx22
    have hx25' : s'.readReg64 (.gpr 25#5) = C.out := (hcpu_in.readReg64 _).trans hx25
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
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
    have hlr_sm : sm.readReg64 Reg.lr = coreFmtPl00.base + 948#64 := by
      rw [hcpu_out.readReg64 Reg.lr]; simp [arm64_norm]
    have hx0_sm : sm.readReg64 .x0 = C.out := by rw [hcpu_out.readReg64 .x0]; simp [arm64_norm]
    have hw1_sm : sm.readReg32 .x1 = fmtFillChar C.opts := by
      rw [hcpu_out.readReg32 .x1]; simp only [arm64_norm, hw26']; exact fillChar_and32 C.opts (by decide)
    have hx19_sm : sm.readReg64 (.gpr 19#5) = 1#64 := by
      rw [hcpu_out.readReg64]; simp [arm64_norm]
    have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (cnt + 1) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using loop_inc64 (by omega)
    have hx21_sm : sm.readReg64 (.gpr 21#5) = C.vt := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx21'
    have hx22_sm : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 rp := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx22'
    have hx25_sm : sm.readReg64 (.gpr 25#5) = C.out := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx25'
    have hw26_sm : sm.readReg32 (.gpr 26#5) = C.opts.flags := by
      rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26'
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
      rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
    have hframe_sm : FmtWriteFrame s sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piCallWriteChar_wpp C
        (F := formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        hcl_sm hpc_sm hrun_sm hsp_sm hlr_sm hx0_sm hw1_sm ?_) ?_
    · intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hcstep
      have hvregs_sf := (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm
      rw [CalleeSavedPreserved.iff_regs] at hcsf
      rcases hcsf with ⟨h19f, h20f, h21f, h22f, _, _, h25f, h26f, _, _, _, _⟩
      cases ok with
      | false =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 868#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 948#64 := hcpu2_in.pc_eq.trans hpcf
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
          (piEpilogue364_wpp C false v0 C.dsPtr hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.readReg32]; simp [arm64_norm, hcpu2_in.readReg64, h19f, hx19_sm])
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)
            (FmtOpsRun.char_err hcstep)) ?_
        refine Entails.trans
          (sepConj_mono (C.hw.transport st' sf sm2 hframe2)
            (sepConj_mono_right (sepConj_mono_left
              (pi_formatterAt_memRegion24 C.f C.out C.vt C.opts)))) ?_
        exact Entails.of_eq (by simp only [Bool.false_eq_true, ↓reduceIte]; ac_rfl)
      | true =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 912#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 948#64 := hcpu2_in.pc_eq.trans hpcf
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
        refine pi_ops_ok_conseq C (ops₁ := [.char (fmtFillChar C.opts)])
          (FmtOpsRun.single_char hcstep) ?_
        refine pi_wpp_mono C
          (ih (cnt + 1) st' sm2 (by omega) hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h20f] using hx20_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h21f] using hx21_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h22f] using hx22_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h25f] using hx25_sm)
            (by rw [hcpu2_out.readReg32]; simpa [arm64_norm, hcpu2_in.readReg64, h26f] using hw26_sm)
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)) ?_
        exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2))
          (Entails.of_eq (by ac_rfl))
    · exact Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe_sm))))
        (Entails.of_eq (by dsimp only [PiCtx.vtSlots]; ac_rfl))

theorem piAlignMid32c_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 : BitVec 64) {pad lp : Nat} (hlp_le : lp ≤ pad) (hpad : pad < 65536)
    {st : σ} {s : State}
    (hcl : coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem)
    (hpc : s.pc = coreFmtPl00.base + 812#64) (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hx19 : (s.readReg64 (.gpr 19#5)).toNat = C.ds.length)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (hw24 : s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg)
    (hx25 : s.readReg64 (.gpr 25#5) = C.out)
    (hw26 : s.readReg32 (.gpr 26#5) = C.opts.flags)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    PiWpp C s
      (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
        stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      (writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++
        ([.str C.ds] ++ List.replicate (pad - lp) (.char (fmtFillChar C.opts)))) st := by
  apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl05.base)
  intro s' hcpu_in
  have hpc' : s'.pc = coreFmtPl00.base + 812#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  clear hpc
  wp_sym_steps
  refine SepWP.done
    (by simpa [arm64_norm] using bl_target_writePrefix 832#64)
    (by simpa [arm64_norm] using hrun')
    fun sm1 hcpu1_out hcl_sm1 hpseg1 => ?_
  have hframe1 : FmtWriteFrame s sm1 :=
    fmtWriteFrame_of_pureSeg hpseg1
      (by rw [hcpu1_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu1_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  have hpc_sm1 : sm1.pc = coreFmtPl05.base := by
    rw [hcpu1_out.pc_eq]; simpa [arm64_norm] using bl_target_writePrefix 832#64
  have hrun_sm1 : sm1.status = .Running := by
    rw [hcpu1_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm1 : sm1.sp = C.s0.sp - 112#64 := by
    rw [hcpu1_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp
  have hlr_sm1 : sm1.readReg64 Reg.lr = coreFmtPl00.base + 836#64 := by
    rw [hcpu1_out.readReg64 Reg.lr]; simp [arm64_norm]
  have hx0_sm1 : sm1.readReg64 .x0 = C.out := by
    rw [hcpu1_out.readReg64 .x0]; simpa [arm64_norm, hcpu_in.readReg64] using hx25
  have hx1_sm1 : sm1.readReg64 .x1 = C.vt := by
    rw [hcpu1_out.readReg64 .x1]; simpa [arm64_norm, hcpu_in.readReg64] using hx21
  have hw2_sm1 : sm1.readReg32 .x2 = fmtSignWord C.opts C.isNonneg := by
    rw [hcpu1_out.readReg32 .x2]; simpa [arm64_norm, hcpu_in.readReg64] using hw24
  have hx3_sm1 : sm1.readReg64 .x3 = 0#64 := by
    rw [hcpu1_out.readReg64 .x3]; simpa [arm64_norm, hcpu_in.readReg64] using hx23
  have hx19_sm1 : (sm1.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
  have hx21_sm1 : sm1.readReg64 (.gpr 21#5) = C.vt := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21
  have hx25_sm1 : sm1.readReg64 (.gpr 25#5) = C.out := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx25
  have hw26_sm1 : sm1.readReg32 (.gpr 26#5) = C.opts.flags := by
    rw [hcpu1_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw26
  have hx27_sm1 : sm1.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx27
  have hx28_sm1 : sm1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp := by
    rw [hcpu1_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx28
  have hvregs_sm1 : calleeSavedVRegs sm1 = calleeSavedVRegs C.s0 := by
    rw [hcpu1_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  refine pi_wpp_mono C
    (piCallWritePrefix_wpp C
      (F := formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
        C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
      hcl_sm1 hpc_sm1 hrun_sm1 hsp_sm1 hlr_sm1 hx0_sm1 hx1_sm1 hw2_sm1 hx3_sm1 ?_) ?_
  · intro sf1 ok1 st1 hpcf1 hrunf1 hspf1 hcsf1 hcl_sf1 hw0f1 hrun_pfx
    have hvregs_sf1 := (calleeSavedVRegs_of_cs hcsf1).trans hvregs_sm1
    rw [CalleeSavedPreserved.iff_regs] at hcsf1
    rcases hcsf1 with ⟨h19f1, _, h21f1, _, _, _, h25f1, h26f1, h27f1, h28f1, _, _⟩
    cases ok1 with
    | false =>
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf1 (mid := coreFmtPl00.base + 864#64)
      intro s2 hcpu2_in
      have hpc2 : s2.pc = coreFmtPl00.base + 836#64 := hcpu2_in.pc_eq.trans hpcf1
      have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf1
      have hw0_2 : s2.readReg32 .x0 = 1#32 := (hcpu2_in.readReg32 .x0).trans hw0f1
      simp [arm64_norm] at hw0_2
      clear hpcf1
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
        fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
      have hframe2 : FmtWriteFrame sf1 sm2 :=
        fmtWriteFrame_of_pureSeg hpseg2
          (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
          (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
      refine pi_wpp_mono C
        (piExitErr360_wpp C C.opts v0 C.dsPtr hcl_sm2
          (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
          (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf1)
          (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf1)
          (FmtOpsRun.append_err _ hrun_pfx)) ?_
      exact Entails.trans (sepConj_mono_left (C.hw.transport st1 sf1 sm2 hframe2))
        (Entails.of_eq (by ac_rfl))
    | true =>
      refine pi_ops_ok_conseq C hrun_pfx ?_
      apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf1 (mid := C.wsFn)
      intro s2 hcpu2_in
      have hpc2 : s2.pc = coreFmtPl00.base + 836#64 := hcpu2_in.pc_eq.trans hpcf1
      have hrun2 : s2.status = .Running := hcpu2_in.status_eq.trans hrunf1
      have hsp2 : s2.sp = C.s0.sp - 112#64 := hcpu2_in.sp_eq.trans hspf1
      have hsp_al2 : s2.spAligned = true := hcpu2_in.spAligned.trans (C.sp1_aligned hspf1)
      have hw0_2 : s2.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0f1
      have hx21_2 : s2.readReg64 (.gpr 21#5) = C.vt :=
        (hcpu2_in.readReg64 _).trans (h21f1.trans hx21_sm1)
      simp [arm64_norm] at hw0_2
      dsimp only [PiCtx.vtSlots, piSavedSlots]
      wp_conv_pre => simp only [sepConj_assoc]
      clear hpcf1
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
        fun sm2 hcpu2_out hcl_sm2 hpseg2 => ?_
      have hframe2 : FmtWriteFrame sf1 sm2 :=
        fmtWriteFrame_of_pureSeg hpseg2
          (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
          (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
      have hpc_sm2 : sm2.pc = C.wsFn := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
      have hrun_sm2 : sm2.status = .Running := by
        rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2
      have hsp_sm2 : sm2.sp = C.s0.sp - 112#64 := by
        rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hsp2
      have hlr_sm2 : sm2.readReg64 Reg.lr = coreFmtPl00.base + 860#64 := by
        rw [hcpu2_out.readReg64 Reg.lr]; simp [arm64_norm]
      have hx0_sm2 : sm2.readReg64 .x0 = C.out := by
        rw [hcpu2_out.readReg64 .x0]; simpa [arm64_norm, hcpu2_in.readReg64, h25f1] using hx25_sm1
      have hx1_sm2 : sm2.readReg64 .x1 = C.dsPtr := by
        rw [hcpu2_out.readReg64 .x1]; simp [arm64_norm]
      have hx2_sm2 : (sm2.readReg64 .x2).toNat = C.ds.length := by
        rw [hcpu2_out.readReg64 .x2]; simpa [arm64_norm, hcpu2_in.readReg64, h19f1] using hx19_sm1
      have hx21_sm2 : sm2.readReg64 (.gpr 21#5) = C.vt := by
        rw [hcpu2_out.readReg64]; simpa [arm64_norm] using hx21_2
      have hx25_sm2 : sm2.readReg64 (.gpr 25#5) = C.out := by
        rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h25f1] using hx25_sm1
      have hw26_sm2 : sm2.readReg32 (.gpr 26#5) = C.opts.flags := by
        rw [hcpu2_out.readReg32]; simpa [arm64_norm, hcpu2_in.readReg64, h26f1] using hw26_sm1
      have hx27_sm2 : sm2.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad := by
        rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h27f1] using hx27_sm1
      have hx28_sm2 : sm2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp := by
        rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h28f1] using hx28_sm1
      have hvregs_sm2 : calleeSavedVRegs sm2 = calleeSavedVRegs C.s0 := by
        rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf1
      refine pi_wpp_mono C
        (piCallWriteStr_wpp C
          (F := formatterAt C.f C.out C.vt C.opts ∗ C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
          hcl_sm2 hpc_sm2 hrun_sm2 hsp_sm2 hlr_sm2 hx0_sm2 hx1_sm2 hx2_sm2 ?_) ?_
      · intro sf2 ok2 st2 hpcf2 hrunf2 hspf2 hcsf2 hcl_sf2 hw0f2 hsstep
        have hvregs_sf2 := (calleeSavedVRegs_of_cs hcsf2).trans hvregs_sm2
        rw [CalleeSavedPreserved.iff_regs] at hcsf2
        rcases hcsf2 with ⟨_, _, h21f2, _, _, _, h25f2, h26f2, h27f2, h28f2, _, _⟩
        cases ok2 with
        | false =>
          apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf2 (mid := coreFmtPl00.base + 864#64)
          intro s3 hcpu3_in
          have hpc3 : s3.pc = coreFmtPl00.base + 860#64 := hcpu3_in.pc_eq.trans hpcf2
          have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf2
          have hw0_3 : s3.readReg32 .x0 = 1#32 := (hcpu3_in.readReg32 .x0).trans hw0f2
          simp [arm64_norm] at hw0_3
          clear hpcf2
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
            fun sm3 hcpu3_out hcl_sm3 hpseg3 => ?_
          have hframe3 : FmtWriteFrame sf2 sm3 :=
            fmtWriteFrame_of_pureSeg hpseg3
              (by rw [hcpu3_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
              (by rw [hcpu3_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
          refine pi_wpp_mono C
            (piExitErr360_wpp C C.opts v0 C.dsPtr hcl_sm3
              (by rw [hcpu3_out.pc_eq]; simp [arm64_norm])
              (by rw [hcpu3_out.status_eq]; simpa [arm64_norm] using hrun3)
              (by rw [hcpu3_out.sp_eq]; simpa [arm64_norm] using hcpu3_in.sp_eq.trans hspf2)
              (by rw [hcpu3_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf2)
              (FmtOpsRun.str_err hsstep)) ?_
          exact Entails.trans
            (sepConj_mono_right (sepConj_mono_left (C.hw.transport st2 sf2 sm3 hframe3)))
            (Entails.of_eq (by ac_rfl))
        | true =>
          refine pi_ops_ok_conseq C (ops₁ := [.str C.ds]) (FmtOpsRun.single_str hsstep) ?_
          apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf2 (mid := coreFmtPl00.base + 912#64)
          intro s3 hcpu3_in
          have hpc3 : s3.pc = coreFmtPl00.base + 860#64 := hcpu3_in.pc_eq.trans hpcf2
          have hrun3 : s3.status = .Running := hcpu3_in.status_eq.trans hrunf2
          have hw0_3 : s3.readReg32 .x0 = 0#32 := (hcpu3_in.readReg32 .x0).trans hw0f2
          have hx27_3 : s3.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad :=
            (hcpu3_in.readReg64 _).trans (h27f2.trans hx27_sm2)
          have hx28_3 : s3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp :=
            (hcpu3_in.readReg64 _).trans (h28f2.trans hx28_sm2)
          simp [arm64_norm] at hw0_3
          clear hpcf2
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun3)
            fun sm3 hcpu3_out hcl_sm3 hpseg3 => ?_
          have hframe3 : FmtWriteFrame sf2 sm3 :=
            fmtWriteFrame_of_pureSeg hpseg3
              (by rw [hcpu3_out.sigActions_eq]; simpa [arm64_norm] using hcpu3_in.sigActions_eq)
              (by rw [hcpu3_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu3_in.tpidrEl0_eq)
          refine pi_wpp_mono C
            (piRightPadLoop_wpp C v0 (rp := pad - lp) (by omega) (pad - lp) 0 st2 sm3 (by omega) hcl_sm3
              (by rw [hcpu3_out.pc_eq]; simp [arm64_norm])
              (by rw [hcpu3_out.status_eq]; simpa [arm64_norm] using hrun3)
              (by rw [hcpu3_out.sp_eq]; simpa [arm64_norm] using hcpu3_in.sp_eq.trans hspf2)
              (by rw [hcpu3_out.readReg64]; simp [arm64_norm])
              (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h21f2] using hx21_sm2)
              (by rw [hcpu3_out.readReg64]
                  simpa [arm64_norm] using sub32_zeroExtend_of_le hlp_le hpad)
              (by rw [hcpu3_out.readReg64]; simpa [arm64_norm, hcpu3_in.readReg64, h25f2] using hx25_sm2)
              (by rw [hcpu3_out.readReg32]; simpa [arm64_norm, hcpu3_in.readReg64, h26f2] using hw26_sm2)
              (by rw [hcpu3_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu3_in.calleeSavedVRegs] using hvregs_sf2)) ?_
          exact Entails.trans
            (sepConj_mono_right (sepConj_mono_left (C.hw.transport st2 sf2 sm3 hframe3)))
            (Entails.of_eq (by ac_rfl))
      · exact Entails.trans (sepConj_mono_left (C.hw.transport st1 sf1 sm2 hframe2))
          (Entails.of_eq (by dsimp only [PiCtx.vtSlots, piSavedSlots]; ac_rfl))
  · exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm1 hframe1))))
      (Entails.of_eq (by ac_rfl))

theorem piLeftPadLoop_wpp {σ : Type} {P : Program} [CoreFmtPlacement] (C : PiCtx σ P)
    (v0 : BitVec 64) {pad lp : Nat} (hlp_le : lp ≤ pad) (hpad : pad < 65536) :
    ∀ (rem cnt : Nat) (st : σ) (s : State),
      cnt + rem = lp →
      coreFmtMultiLib.CodeLoadedWhere padIntegralKeep coreFmtMpl s.mem →
      s.pc = coreFmtPl00.base + 772#64 →
      s.status = .Running →
      s.sp = C.s0.sp - 112#64 →
      (s.readReg64 (.gpr 19#5)).toNat = C.ds.length →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt →
      s.readReg64 (.gpr 21#5) = C.vt →
      s.readReg64 (.gpr 23#5) = 0#64 →
      s.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg →
      s.readReg64 (.gpr 25#5) = C.out →
      s.readReg32 (.gpr 26#5) = C.opts.flags →
      s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad →
      s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp →
      calleeSavedVRegs s = calleeSavedVRegs C.s0 →
      PiWpp C s
        (formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗ C.W st s ∗
          stackFrameAt (C.s0.sp - 112#64) (48 + C.stackBytes) ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        (List.replicate rem (.char (fmtFillChar C.opts)) ++
          (writePrefixSignOp (fmtSignWord C.opts C.isNonneg) ++
            ([.str C.ds] ++ List.replicate (pad - lp) (.char (fmtFillChar C.opts))))) st := by
  intro rem
  induction rem with
  | zero =>
    intro cnt st s hsum hcl hpc hrun hsp hx19 hx20 hx21 hx23 hw24 hx25 hw26 hx27 hx28 hvregs
    have hcnt : cnt = lp := by omega
    subst hcnt
    have hcmp := loop_cmp_eq cnt
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := coreFmtPl00.base + 812#64)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 772#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx20
    have hx28' : s'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx28
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    have hframe : FmtWriteFrame s sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piAlignMid32c_wpp C v0 hlp_le hpad hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq.trans hsp)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx21)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx25)
        (by rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw26)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx27)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx28')
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe)))
  | succ k ih =>
    intro cnt st s hsum hcl hpc hrun hsp hx19 hx20 hx21 hx23 hw24 hx25 hw26 hx27 hx28 hvregs
    have hlt : cnt < lp := by omega
    have hlp_lt : lp < 65536 := by omega
    have hcmp := loop_cmp_lt hlt hlp_lt
    apply sepWPp_seg_block0 (by decide) C.hext0 hcl (mid := C.wcFn)
    intro s' hcpu_in
    have hpc' : s'.pc = coreFmtPl00.base + 772#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hx20' : s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 cnt := (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
    have hx25' : s'.readReg64 (.gpr 25#5) = C.out := (hcpu_in.readReg64 _).trans hx25
    have hw26' : BitVec.setWidth 32 (s'.readReg64 (.gpr 26#5)) = C.opts.flags := by
      simpa [arm64_norm, hcpu_in.readReg64] using hw26
    have hx28' : s'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp := (hcpu_in.readReg64 _).trans hx28
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
    have hlr_sm : sm.readReg64 Reg.lr = coreFmtPl00.base + 804#64 := by
      rw [hcpu_out.readReg64 Reg.lr]; simp [arm64_norm]
    have hx0_sm : sm.readReg64 .x0 = C.out := by rw [hcpu_out.readReg64 .x0]; simp [arm64_norm]
    have hw1_sm : sm.readReg32 .x1 = fmtFillChar C.opts := by
      rw [hcpu_out.readReg32 .x1]; simp only [arm64_norm, hw26']; exact fillChar_and32 C.opts (by decide)
    have hx19_sm : (sm.readReg64 (.gpr 19#5)).toNat = C.ds.length := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx19
    have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (cnt + 1) := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using loop_inc64 (by omega)
    have hx21_sm : sm.readReg64 (.gpr 21#5) = C.vt := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx21'
    have hx23_sm : sm.readReg64 (.gpr 23#5) = 0#64 := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx23
    have hw24_sm : sm.readReg32 (.gpr 24#5) = fmtSignWord C.opts C.isNonneg := by
      rw [hcpu_out.readReg32]; simpa [arm64_norm, hcpu_in.readReg64] using hw24
    have hx25_sm : sm.readReg64 (.gpr 25#5) = C.out := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx25'
    have hw26_sm : sm.readReg32 (.gpr 26#5) = C.opts.flags := by
      rw [hcpu_out.readReg32]; simpa [arm64_norm] using hw26'
    have hx27_sm : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 pad := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx27
    have hx28_sm : sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 lp := by
      rw [hcpu_out.readReg64]; simpa [arm64_norm] using hx28'
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
      rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
    have hframe_sm : FmtWriteFrame s sm :=
      fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
    refine pi_wpp_mono C
      (piCallWriteChar_wpp C
        (F := formatterAt C.f C.out C.vt C.opts ∗ fmtSrcBytes C.ro C.dsPtr C.ds ∗
          C.vtSlots ∗ piSavedSlots C.s0 v0 C.dsPtr)
        hcl_sm hpc_sm hrun_sm hsp_sm hlr_sm hx0_sm hw1_sm ?_) ?_
    · intro sf ok st' hpcf hrunf hspf hcsf hcl_sf hw0f hcstep
      have hvregs_sf := (calleeSavedVRegs_of_cs hcsf).trans hvregs_sm
      rw [CalleeSavedPreserved.iff_regs] at hcsf
      rcases hcsf with ⟨h19f, h20f, h21f, _, h23f, h24f, h25f, h26f, h27f, h28f, _, _⟩
      cases ok with
      | false =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 864#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 804#64 := hcpu2_in.pc_eq.trans hpcf
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
          (piExitErr360_wpp C C.opts v0 C.dsPtr hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)
            (FmtOpsRun.char_err hcstep)) ?_
        exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2))
          (Entails.of_eq (by ac_rfl))
      | true =>
        apply sepWPp_seg_block0 (by decide) C.hext0 hcl_sf (mid := coreFmtPl00.base + 772#64)
        intro s2 hcpu2_in
        have hpc2 : s2.pc = coreFmtPl00.base + 804#64 := hcpu2_in.pc_eq.trans hpcf
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
        refine pi_ops_ok_conseq C (ops₁ := [.char (fmtFillChar C.opts)])
          (FmtOpsRun.single_char hcstep) ?_
        refine pi_wpp_mono C
          (ih (cnt + 1) st' sm2 (by omega) hcl_sm2
            (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
            (by rw [hcpu2_out.sp_eq]; simpa [arm64_norm] using hcpu2_in.sp_eq.trans hspf)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h19f] using hx19_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h20f] using hx20_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h21f] using hx21_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h23f] using hx23_sm)
            (by rw [hcpu2_out.readReg32]; simpa [arm64_norm, hcpu2_in.readReg64, h24f] using hw24_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h25f] using hx25_sm)
            (by rw [hcpu2_out.readReg32]; simpa [arm64_norm, hcpu2_in.readReg64, h26f] using hw26_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h27f] using hx27_sm)
            (by rw [hcpu2_out.readReg64]; simpa [arm64_norm, hcpu2_in.readReg64, h28f] using hx28_sm)
            (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2_in.calleeSavedVRegs] using hvregs_sf)) ?_
        exact Entails.trans (sepConj_mono_left (C.hw.transport st' sf sm2 hframe2))
          (Entails.of_eq (by ac_rfl))
    · exact Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (C.hw.transport st s sm hframe_sm))))
        (Entails.of_eq (by dsimp only [PiCtx.vtSlots]; ac_rfl))

end PadIntegralProof

end VerifiedLibraries.RustStd
