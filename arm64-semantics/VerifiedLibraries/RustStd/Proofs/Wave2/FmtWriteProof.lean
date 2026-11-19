/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteCustom
public import ProofLib.Disproof

/-!
# `core::fmt::write` Proof and Template Checks

Proves `coreFmtWrite_ok` and `coreFmtWrite_subroutineOk` (`VerifiedLibraries.RustStd.Spec.CoreFmtWrite`)
for `coreMultiLib` block `0` (`core::fmt::write`, `rustc 1.98.1`, `aarch64-unknown-linux-musl`),
together with non-vacuity witnesses and compiled template decoding checks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib

/-! ## Loop body dispatch and induction -/

private theorem cw_tpl_focus_u8 (tplPtr : BitVec 64) (tpl : List (BitVec 8))
    (pos : Nat) (n : BitVec 8) (rest : List (BitVec 8))
    (hdrop : tpl.drop pos = n :: rest) (hpos_lt : pos < tpl.length) :
    (tplPtr ↦ᵣ tpl) =
      ((tplPtr + BitVec.ofNat 64 pos) ↦₈ᵣ n) ∗
      ((tplPtr ↦ᵣ tpl.take pos) ∗
       ((tplPtr + BitVec.ofNat 64 (pos + 1)) ↦ᵣ rest)) := by
  have hsplit : tpl = tpl.take pos ++ n :: rest := by
    rw [← hdrop, List.take_append_drop]
  have hlen : (tpl.take pos).length = pos := List.length_take_of_le (Nat.le_of_lt hpos_lt)
  conv => lhs; rw [hsplit]
  rw [tpl_split_byte tplPtr (tpl.take pos) n rest, hlen]

private theorem cw_u8_ne_zero_w32 {n : BitVec 8} (hn0 : n ≠ 0#8) :
    BitVec.setWidth 32 (n.zeroExtend 64) ≠ 0#32 ∧
    (BitVec.setWidth 32 (n.zeroExtend 64) == 0#32) = false ∧
    n.zeroExtend 32 ≠ 0#32 ∧
    (n.zeroExtend 32 == 0#32) = false := by
  have h1 : BitVec.setWidth 32 (n.zeroExtend 64) ≠ 0#32 := by
    change BitVec.setWidth 32 (BitVec.setWidth 64 n) ≠ 0#32
    bv_omega
  have h2 : n.zeroExtend 32 ≠ 0#32 := by
    change BitVec.setWidth 32 n ≠ 0#32
    bv_omega
  exact ⟨h1, beq_false_of_ne h1, h2, beq_false_of_ne h2⟩

private theorem cw_w32_getLsbD_0 (x : BitVec 64) :
    (BitVec.setWidth 32 x).getLsbD 0 = x.getLsbD 0 := by
  simp

private theorem cw_stackFrameAt_0x70_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 0x70 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
      ∃∗ v7, ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12, ∃∗ v13,
        ((sp0 - 112#64) ↦₆₄ v0) ∗ ((sp0 - 104#64) ↦₆₄ v1) ∗
        ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗
        ((sp0 - 80#64) ↦₆₄ v4) ∗ ((sp0 - 72#64) ↦₆₄ v5) ∗
        ((sp0 - 64#64) ↦₆₄ v6) ∗ ((sp0 - 56#64) ↦₆₄ v7) ∗
        ((sp0 - 48#64) ↦₆₄ v8) ∗ ((sp0 - 40#64) ↦₆₄ v9) ∗
        ((sp0 - 32#64) ↦₆₄ v10) ∗ ((sp0 - 24#64) ↦₆₄ v11) ∗
        ((sp0 - 16#64) ↦₆₄ v12) ∗ ((sp0 - 8#64) ↦₆₄ v13) := by
  simp only [wp_norm]

private theorem cw_prologue_entail (A B W0 W1 S0 V0 : SepProp)
    (sp0 : BitVec 64) (v1 v2 v3 : BitVec 64) (SAV : SepProp)
    (hw : W0 ⊢ W1) :
    A ∗ B ∗ W0 ∗ S0 ∗ V0 ∗
      ((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗ SAV ⊢
    A ∗ B ∗ W1 ∗ S0 ∗ (V0 ∗ memRegion (sp0 - 104#64) 24 ∗ SAV) := by
  have h24 := triple64_entails_memRegion24 (sp0 - 104#64) v1 v2 v3
  have ha1 : sp0 - 104#64 + 8#64 = sp0 - 96#64 := by bv_omega
  have ha2 : sp0 - 104#64 + 16#64 = sp0 - 88#64 := by bv_omega
  rw [ha1, ha2] at h24
  have h_assoc :
      ((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗ SAV =
      (((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3)) ∗ SAV := by
    simp only [sepConj_assoc]
  rw [h_assoc]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono hw (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono h24 (Entails.refl _))))))

private theorem cw_prologue_entail3 (A1 A2 A3 A4 W0 W1 S0 V0 : SepProp)
    (sp0 : BitVec 64) (v1 v2 v3 : BitVec 64) (SAV : SepProp)
    (hw : W0 ⊢ W1) :
    A1 ∗ A2 ∗ A3 ∗ A4 ∗ W0 ∗ S0 ∗ V0 ∗
      ((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗ SAV ⊢
    A1 ∗ ((A2 ∗ A3) ∗ A4) ∗ W1 ∗ S0 ∗ (V0 ∗ memRegion (sp0 - 104#64) 24 ∗ SAV) := by
  have h_lhs :
      A1 ∗ A2 ∗ A3 ∗ A4 ∗ W0 ∗ S0 ∗ V0 ∗
        ((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗ SAV =
      A1 ∗ ((A2 ∗ A3) ∗ A4) ∗ W0 ∗ S0 ∗ V0 ∗
        ((sp0 - 104#64) ↦₆₄ v1) ∗ ((sp0 - 96#64) ↦₆₄ v2) ∗ ((sp0 - 88#64) ↦₆₄ v3) ∗ SAV := by
    simp only [sepConj_assoc]
  rw [h_lhs]
  exact cw_prologue_entail A1 ((A2 ∗ A3) ∗ A4) W0 W1 S0 V0 sp0 v1 v2 v3 SAV hw

section
arm64_proof_prelude

theorem cwStep074_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {fuel pos ai : Nat} {n : BitVec 8} {rest : List (BitVec 8)} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (hdrop : C.tpl.drop pos = n :: rest)
    (hn0 : n ≠ 0#8)
    (hdec : decodeFmtTemplate C.tplPtr C.args (fuel + 1) pos ai (n :: rest) = some cs)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn cs)
    (ih_loop : ∀ pos' ai' cs',
      decodeFmtTemplate C.tplPtr C.args fuel pos' ai' (C.tpl.drop pos') = some cs' →
      CwLoopCont C pos' ai' cs')
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = C.out)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx24 : s.readReg64 (.gpr 24#5) = C.writeStrFn)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai)
    (hx26 : s.readReg64 (.gpr 26#5) = 0x60000020#64)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s)
      (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hpos_lt : pos < C.tpl.length :=
    Classical.byContradiction fun hge => by
      rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)] at hdrop
      cases hdrop
  have hdrop_k : ∀ m : Nat, rest.drop m = C.tpl.drop (pos + 1 + m) := fun m => by
    rw [show pos + 1 + m = pos + (m + 1) by omega, ← List.drop_drop, hdrop]
    rfl
  simp only [decodeFmtTemplate, hn0, ↓reduceIte] at hdec
  by_cases hn_lt : n.toNat < 0x80
  · simp only [hn_lt, ↓reduceIte] at hdec
    by_cases hlen_lt : rest.length < n.toNat
    · simp only [hlen_lt, ↓reduceIte] at hdec; cases hdec
    · simp only [hlen_lt, ↓reduceIte, Option.map_eq_some_iff] at hdec
      rcases hdec with ⟨cs', hdec', rfl⟩
      rw [hdrop_k n.toNat] at hdec'
      exact cwStep_shortLit C hext_blk hcl hdrop hpos_lt hn_lt (Nat.le_of_not_lt hlen_lt)
        hcb (ih_loop (pos + 1 + n.toNat) ai cs' hdec')
        hpc hrun hsp hsp_al hx2 hx8 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hvregs
  · simp only [hn_lt, ↓reduceIte] at hdec
    by_cases hne80 : n = 0x80#8
    · subst hne80
      simp only [eq_self, ↓reduceIte] at hdec
      match rest with
      | [] => simp at hdec
      | [_] => simp at hdec
      | b0 :: b1 :: r =>
        have hlen2 : ¬ (b0 :: b1 :: r).length < 2 := by simp
        simp only [hlen2, ↓reduceIte, List.take_succ_cons, List.take_zero,
          List.drop_succ_cons, List.drop_zero] at hdec
        by_cases hr_lt : r.length < leBytesNat [b0, b1]
        · simp only [hr_lt, ↓reduceIte] at hdec; cases hdec
        · simp only [hr_lt, ↓reduceIte, Option.map_eq_some_iff] at hdec
          rcases hdec with ⟨cs', hdec', rfl⟩
          have hr_drop : r.drop (leBytesNat [b0, b1]) = C.tpl.drop (pos + 3 + leBytesNat [b0, b1]) := by
            have hk := hdrop_k (2 + leBytesNat [b0, b1])
            rw [← List.drop_drop] at hk
            rw [show pos + 3 + leBytesNat [b0, b1] = pos + 1 + (2 + leBytesNat [b0, b1]) by omega]
            exact hk
          rw [hr_drop] at hdec'
          exact cwStep_longLit C hext_blk hcl hdrop hpos_lt (Nat.le_of_not_lt hr_lt)
            hcb (ih_loop (pos + 3 + leBytesNat [b0, b1]) ai cs' hdec')
            hpc hrun hsp hsp_al hx2 hx8 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hvregs
    · simp only [hne80, ↓reduceIte] at hdec
      by_cases hnc0_lt : n.toNat < 0xc0
      · simp only [hnc0_lt, ↓reduceIte] at hdec; cases hdec
      · simp only [hnc0_lt, ↓reduceIte] at hdec
        by_cases hnec0 : n = 0xc0#8
        · subst hnec0
          have hph_c0 : decodeFmtPlaceholder 0xc0#8 rest C.args ai =
              some (defaultFmtOptions, ai, ai + 1, 0) := by
            simp [decodeFmtPlaceholder, defaultFmtOptions]
          rw [hph_c0] at hdec
          dsimp only at hdec
          cases harg : C.args[ai]? with
          | none => simp only [harg] at hdec; cases hdec
          | some vf =>
            rcases vf with ⟨value, fmtFn⟩
            simp only [harg, Option.map_eq_some_iff] at hdec
            rcases hdec with ⟨cs', hdec', rfl⟩
            have hdrop0 : rest.drop 0 = C.tpl.drop (pos + 1) := by
              simpa only [Nat.add_zero] using hdrop_k 0
            rw [Nat.add_zero, hdrop0] at hdec'
            exact cwStep_defaultArg C hext_blk hcl heven harg hcb
              (ih_loop (pos + 1) (ai + 1) cs' hdec')
              hpc hrun hsp hsp_al hx2 hx8 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hvregs
        · cases hph : decodeFmtPlaceholder n rest C.args ai with
          | none => simp only [hph] at hdec; cases hdec
          | some quad =>
            rcases quad with ⟨opts, idx, ai', k⟩
            simp only [hph] at hdec
            cases harg : C.args[idx]? with
            | none => simp only [harg] at hdec; cases hdec
            | some vf =>
              rcases vf with ⟨value, fmtFn⟩
              simp only [harg, Option.map_eq_some_iff] at hdec
              rcases hdec with ⟨cs', hdec', rfl⟩
              rw [hdrop_k k] at hdec'
              exact cwStep_customArg C hext_blk hcl heven hdrop hpos_lt hn_lt hne80 hnec0
                hph harg hcb (ih_loop (pos + 1 + k) ai' cs' hdec')
                hpc hrun hsp hsp_al hx2 hx8 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hvregs

theorem cwLoop068_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    (heven : C.argsPtr.getLsbD 0 = false) :
    ∀ (fuel pos ai : Nat) (cs : List FmtCall),
      decodeFmtTemplate C.tplPtr C.args fuel pos ai (C.tpl.drop pos) = some cs →
      CwLoopCont C pos ai cs := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos ai cs hdec
    simp [decodeFmtTemplate] at hdec
  | succ fuel ih =>
    intro pos ai cs hdec st pad s hcl hcb hpc hrun hsp hsp_al
      hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hvregs
    cases hdrop : C.tpl.drop pos with
    | nil =>
      rw [hdrop] at hdec
      simp [decodeFmtTemplate] at hdec
    | cons n rest =>
      rw [hdrop] at hdec
      have hpos_lt : pos < C.tpl.length :=
        Classical.byContradiction fun hge => by
          rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)] at hdrop
          cases hdrop
      have htpl_b := cw_tpl_focus_u8 C.tplPtr C.tpl pos n rest hdrop hpos_lt
      by_cases hn0 : n = 0#8
      · subst hn0
        simp only [decodeFmtTemplate, ↓reduceIte] at hdec
        by_cases hrest : rest = []
        · subst hrest
          simp only [↓reduceIte, Option.some.injEq] at hdec
          subst hdec
          apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 396#64)
          intro s' hcpu_in
          have hpc' : s'.pc = cwPl0.base + 104#64 := hcpu_in.pc_eq.trans hpc
          have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
          have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
          have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 pos :=
            (hcpu_in.readReg64 _).trans hx22
          wp_conv_pre =>
            dsimp only [CwLoopMem, fmtArgumentsAt]
            rw [htpl_b]
            simp only [sepConj_assoc]
          clear hpc
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
            fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
          have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
          refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
            (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
              (cwLoopMem_transport C hcb.transport hframe)) ?_
          · dsimp only [CwLoopMem, fmtArgumentsAt]
            rw [htpl_b]
            ac_rfl
          · exact cwExitOk_wpp C hext_blk hcl_sm
              (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
              (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
              (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hcpu_in.sp_eq, hsp])
              (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
              (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
              (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
              hcb.transport
        · simp only [hrest, ↓reduceIte] at hdec; cases hdec
      · rcases cw_u8_ne_zero_w32 hn0 with ⟨hw32_ne, hw32_beq, hz32_ne, hz32_beq⟩
        apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 116#64)
        intro s' hcpu_in
        have hpc' : s'.pc = cwPl0.base + 104#64 := hcpu_in.pc_eq.trans hpc
        have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
        have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
        have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 pos :=
          (hcpu_in.readReg64 _).trans hx22
        wp_conv_pre =>
          dsimp only [CwLoopMem, fmtArgumentsAt]
          rw [htpl_b]
          simp only [sepConj_assoc]
        clear hpc
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
          fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
        have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
        refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
          (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
            (cwLoopMem_transport C hcb.transport hframe)) ?_
        · dsimp only [CwLoopMem, fmtArgumentsAt]
          rw [htpl_b]
          ac_rfl
        · exact cwStep074_wpp C hext_blk hcl_sm heven hdrop hn0 hdec hcb (ih)
            (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
            (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hcpu_in.sp_eq, hsp])
            (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
            (by rw [hcpu_out.readReg64]; simp [arm64_norm])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx19])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx20])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx21])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx24])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx25])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx26])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
            (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)

/-! ## Prologue and `coreFmtWrite_ok` -/

theorem cwBlock0_ok [CoreFmtWritePl] {σ : Type} {P : Program}
    (hext_blk : ∀ off : Nat, off < 436 →
      P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    (W : σ → State → SepProp) (Step : FmtCall → σ → Bool → σ → Prop)
    (Panic Oom : FmtCall → σ → State → Prop) (stackBytes : Nat) :
    subroutine_ok P (coreMultiLib.fnAddr coreFmtMpl coreFmtWriteSym)
      (coreMultiLib.withCodeLoaded coreFmtMpl
        (coreFmtWriteSpec P W Step Panic Oom stackBytes)) := by
  rw [fnAddr_coreFmtWrite CoreFmtWritePl.placeable]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨out, vt, writeStrFn, argsRo, tpl, args, st₀⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, coreFmtWriteSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded coreFmtMpl s0.mem⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hstack, cs, hdec, hcb⟩, hpre⟩
  let C : CwCtx σ := {
    P := P
    W := W
    Step := Step
    Panic := Panic
    Oom := Oom
    stackBytes := stackBytes
    hstack := hstack
    out := out
    vt := vt
    writeStrFn := writeStrFn
    argsRo := argsRo
    tplPtr := s0.readReg64 .x2
    argsPtr := s0.readReg64 .x3
    tpl := tpl
    args := args
    s0 := s0
    R := R
    ret_pc := s0.readReg64 Reg.lr
  }
  have hpre_split :
      s0.mem ⊨
        (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
         fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
         C.W st₀ s0 ∗
         stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
         stackFrameAt C.s0.sp 0x70) ∗ R := by
    rw [stackFrameAt_split s0.sp 0x70 stackBytes hstack,
      sepConj_comm (stackFrameAt s0.sp 0x70)] at hpre
    simpa only [sepConj_assoc] using hpre
  rw [cw_stackFrameAt_0x70_unpack C.s0.sp] at hpre_split
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre_split
  rcases hpre_split with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, hpre_split⟩
  refine ⟨_, hpre_split, ?_⟩
  refine sepWPp_conseq
    (Q1 := CwQ C cs st₀) (Qp1 := CwQp C cs st₀) (oom1 := CwOom C cs st₀)
    (fun sf P_f hq => ?_)
    (fun sf P_f hqp hm_f => ?_)
    (fun sf R' hmo => ?_)
    ?_
  ·
    rcases hq with ⟨⟨ok, st', hw0, hrun_cs, hmem_f⟩, hsp_f, hcs_f⟩
    refine ⟨fun hm_f => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left ?_) (hmem_f hm_f)
    refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
    rw [pure_sepConj_of_true ⟨hw0, cs, hdec, hrun_cs⟩]
    exact Entails.refl _
  ·
    have hm' := hqp hm_f
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
    rcases hm' with ⟨⟨c, stm, hreach, hpan⟩, hany⟩
    exact ⟨⟨cs, c, stm, hdec, hreach, hpan⟩, hany⟩
  ·
    dsimp only [CwOom] at hmo ⊢
    rw [satisfies_pure_sepConj] at hmo ⊢
    rcases hmo with ⟨⟨c, stm, hreach, hoom⟩, hR'⟩
    exact ⟨⟨cs, c, stm, hdec, hreach, hoom⟩, hR'⟩
  ·
    have hsp_sub : (s0.sp - 112#64) &&& 15#64 = 0#64 :=
      spAligned_to_sub_112_and (by simpa [State.spAligned] using hsp0)
    cases hbit0 : (s0.readReg64 .x3).getLsbD 0
    · -- Even `x3`: encoded template walk
      have hbit0_C : C.argsPtr.getLsbD 0 = false := hbit0
      have hdec_even : decodeFmtTemplate C.tplPtr C.args tpl.length 0 0 tpl = some cs := by
        simpa only [decodeFmtArguments, hbit0, Bool.false_eq_true, ↓reduceIte] using hdec
      cases tpl with
      | nil =>
        simp [decodeFmtTemplate] at hdec_even
      | cons n rest =>
        have htpl_b0 : (C.tplPtr ↦ᵣ (n :: rest)) =
            (C.tplPtr ↦₈ᵣ n) ∗ ((C.tplPtr + 1#64) ↦ᵣ rest) :=
          pointsToBytesRO_cons C.tplPtr n rest
        have hw3_bit0 : (BitVec.setWidth 32 C.argsPtr).getLsbD 0 = false := by
          rw [cw_w32_getLsbD_0, hbit0_C]
        by_cases hn0 : n = 0#8
        ·
          subst hn0
          simp only [List.length_cons, decodeFmtTemplate, ↓reduceIte] at hdec_even
          by_cases hrest : rest = []
          · subst hrest
            injection hdec_even with hdec_even
            subst hdec_even
            apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 396#64)
            intro s' hcpu_in
            have hpc' : s'.pc = cwPl0.base := hcpu_in.pc_eq.trans hpc0
            have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
            have hsp' : s'.sp = C.s0.sp := hcpu_in.sp_eq
            have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp0
            have hx0' : s'.readReg64 .x0 = C.out := (hcpu_in.readReg64 .x0).trans hx0_0
            have hx1' : s'.readReg64 .x1 = C.vt := (hcpu_in.readReg64 .x1).trans hx1_0
            have hx2' : s'.readReg64 .x2 = C.tplPtr := hcpu_in.readReg64 .x2
            have hx3' : s'.readReg64 .x3 = C.argsPtr := hcpu_in.readReg64 .x3
            have hlr' : s'.readReg64 .lr = C.ret_pc := hcpu_in.readReg64 .lr
            wp_conv_pre =>
              dsimp only [fmtArgumentsAt]
              rw [htpl_b0]
              simp only [sepConj_assoc]
            clear hpc0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
              fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
            have hframe : FmtWriteFrame s0 sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
            refine SepWPp.weaken_pre
              (P' := ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
                fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
                C.W st₀ sm ∗
                stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
                (((C.s0.sp - 112#64) ↦₆₄ v0) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
                 cwSavedSlots C.s0.sp C.s0 C.ret_pc)) ?_ ?_
            · have hw := hcb.transport st₀ s0 sm hframe
              dsimp only [fmtArgumentsAt, cwSavedSlots]
              rw [htpl_b0,
                hcpu_in.readReg64 (.gpr 29#5),
                hcpu_in.readReg64 (.gpr 26#5), hcpu_in.readReg64 (.gpr 25#5),
                hcpu_in.readReg64 (.gpr 24#5), hcpu_in.readReg64 (.gpr 23#5),
                hcpu_in.readReg64 (.gpr 22#5), hcpu_in.readReg64 (.gpr 21#5),
                hcpu_in.readReg64 (.gpr 20#5), hcpu_in.readReg64 (.gpr 19#5)]
              exact cw_prologue_entail3 _ _ _ _ _ _ _ _ C.s0.sp v1 v2 v3 _ hw
            · exact cwExitOk_wpp C hext_blk hcl_sm
                (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
                (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
                (by dsimp only [C]; rw [hcpu_out.sp_eq]; simp [arm64_norm])
                (by rw [hcpu_out.spAligned]; simp [State.spAligned, arm64_norm, hsp_sub])
                (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
                (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
                (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs)
                hcb.transport
          · simp only [hrest, ↓reduceIte] at hdec_even; cases hdec_even
        ·
          rcases cw_u8_ne_zero_w32 hn0 with ⟨hw32_ne, hw32_beq, hz32_ne, hz32_beq⟩
          apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 116#64)
          intro s' hcpu_in
          have hpc' : s'.pc = cwPl0.base := hcpu_in.pc_eq.trans hpc0
          have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
          have hsp' : s'.sp = C.s0.sp := hcpu_in.sp_eq
          have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp0
          have hx0' : s'.readReg64 .x0 = C.out := (hcpu_in.readReg64 .x0).trans hx0_0
          have hx1' : s'.readReg64 .x1 = C.vt := (hcpu_in.readReg64 .x1).trans hx1_0
          have hx2' : s'.readReg64 .x2 = C.tplPtr := hcpu_in.readReg64 .x2
          have hx3' : s'.readReg64 .x3 = C.argsPtr := hcpu_in.readReg64 .x3
          have hlr' : s'.readReg64 .lr = C.ret_pc := hcpu_in.readReg64 .lr
          wp_conv_pre =>
            dsimp only [fmtArgumentsAt]
            rw [htpl_b0]
            simp only [sepConj_assoc]
          clear hpc0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
            fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
          have hframe : FmtWriteFrame s0 sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
          refine SepWPp.weaken_pre (P' := CwLoopMem C st₀ v0 sm) ?_ ?_
          · have hw := hcb.transport st₀ s0 sm hframe
            dsimp only [CwLoopMem, fmtArgumentsAt, cwSavedSlots]
            rw [htpl_b0,
              hcpu_in.readReg64 (.gpr 29#5),
              hcpu_in.readReg64 (.gpr 26#5), hcpu_in.readReg64 (.gpr 25#5),
              hcpu_in.readReg64 (.gpr 24#5), hcpu_in.readReg64 (.gpr 23#5),
              hcpu_in.readReg64 (.gpr 22#5), hcpu_in.readReg64 (.gpr 21#5),
              hcpu_in.readReg64 (.gpr 20#5), hcpu_in.readReg64 (.gpr 19#5)]
            exact cw_prologue_entail3 _ _ _ _ _ _ _ _ C.s0.sp v1 v2 v3 _ hw
          · exact cwStep074_wpp C hext_blk hcl_sm hbit0_C rfl hn0 hdec_even hcb
              (cwLoop068_wpp C hext_blk hbit0_C rest.length)
              (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
              (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
              (by dsimp only [C]; rw [hcpu_out.sp_eq]; simp [arm64_norm])
              (by rw [hcpu_out.spAligned]; simp [State.spAligned, arm64_norm, hsp_sub])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx2'])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by dsimp only [C, Reg.x3]; rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by rw [hcpu_out.readReg64]; simp [arm64_norm])
              (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
              (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
              (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs)
    · -- Odd `x3`: `Arguments::from_str` fast path
      have hbit0_C : C.argsPtr.getLsbD 0 = true := hbit0
      simp only [decodeFmtArguments, hbit0, ↓reduceIte] at hdec
      by_cases hlen_eq : tpl.length = ((s0.readReg64 .x3) >>> 1).toNat
      · simp only [hlen_eq, ↓reduceIte, Option.some.injEq] at hdec
        subst hdec
        have hw3_bit0 : (BitVec.setWidth 32 C.argsPtr).getLsbD 0 = true := by
          rw [cw_w32_getLsbD_0, hbit0_C]
        apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 348#64)
        intro s' hcpu_in
        have hpc' : s'.pc = cwPl0.base := hcpu_in.pc_eq.trans hpc0
        have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
        have hsp' : s'.sp = C.s0.sp := hcpu_in.sp_eq
        have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp0
        have hx0' : s'.readReg64 .x0 = C.out := (hcpu_in.readReg64 .x0).trans hx0_0
        have hx1' : s'.readReg64 .x1 = C.vt := (hcpu_in.readReg64 .x1).trans hx1_0
        have hx2' : s'.readReg64 .x2 = C.tplPtr := hcpu_in.readReg64 .x2
        have hx3' : s'.readReg64 .x3 = C.argsPtr := hcpu_in.readReg64 .x3
        have hlr' : s'.readReg64 .lr = C.ret_pc := hcpu_in.readReg64 .lr
        wp_conv_pre =>
          dsimp only [fmtArgumentsAt]
          rw [hbit0]
          simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
        clear hpc0
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
          fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
        have hframe : FmtWriteFrame s0 sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
        refine SepWPp.weaken_pre
          (P' := ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (C.tplPtr ↦ᵣ C.tpl) ∗
            C.W st₀ sm ∗
            stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
            (((C.s0.sp - 112#64) ↦₆₄ v0) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
             cwSavedSlots C.s0.sp C.s0 C.ret_pc)) ?_ ?_
        · have hw := hcb.transport st₀ s0 sm hframe
          dsimp only [cwSavedSlots]
          rw [hcpu_in.readReg64 (.gpr 29#5),
            hcpu_in.readReg64 (.gpr 26#5), hcpu_in.readReg64 (.gpr 25#5),
            hcpu_in.readReg64 (.gpr 24#5), hcpu_in.readReg64 (.gpr 23#5),
            hcpu_in.readReg64 (.gpr 22#5), hcpu_in.readReg64 (.gpr 21#5),
            hcpu_in.readReg64 (.gpr 20#5), hcpu_in.readReg64 (.gpr 19#5)]
          exact cw_prologue_entail _ _ _ _ _ _ C.s0.sp v1 v2 v3 _ hw
        · exact cwOddFastPath_wpp C hext_blk hcl_sm hbit0 hlen_eq hcb
            (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
            (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
            (by dsimp only [C]; rw [hcpu_out.sp_eq]; simp [arm64_norm])
            (by rw [hcpu_out.spAligned]; simp [State.spAligned, arm64_norm, hsp_sub])
            (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx2'])
            (by dsimp only [C, Reg.x3]; rw [hcpu_out.readReg64]; simp [arm64_norm])
            (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm])
            (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm])
            (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
            (by dsimp only [C]; rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64])
            (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm] using hcpu_in.calleeSavedVRegs)
      · simp only [hlen_eq, ↓reduceIte] at hdec; cases hdec

end

/-- Placement-generic correctness of `core::fmt::write` (`coreMultiLib` block `0`) against
    `coreFmtWriteSpec` for any `P : Program` with no hooks inside `coreMultiLib.blocks[0]`. -/
theorem coreFmtWrite_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext_blk : ∀ off : Nat, off < 436 →
      P.externAt? (mpl.base 0 + BitVec.ofNat 64 off) = none)
    (W : σ → State → SepProp) (Step : FmtCall → σ → Bool → σ → Prop)
    (Panic Oom : FmtCall → σ → State → Prop) (stackBytes : Nat) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFmtWriteSym)
      (coreMultiLib.withCodeLoaded mpl
        (coreFmtWriteSpec P W Step Panic Oom stackBytes)) := by
  letI : CoreFmtWritePl := ⟨mpl, hpl⟩
  exact cwBlock0_ok hext_blk W Step Panic Oom stackBytes

/-- Canonical `MultiPlacedLib.subroutineOk` for `coreFmtWriteSym` under any `externs` map. -/
theorem coreFmtWrite_subroutineOk {σ : Type}
    (W : σ → State → SepProp) (Step : FmtCall → σ → Bool → σ → Prop)
    (Panic Oom : FmtCall → σ → State → Prop) (stackBytes : Nat)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFmtWriteSym
      (fun mpl => coreFmtWriteSpec (coreMultiLib.blockProgram mpl 0 externs)
        W Step Panic Oom stackBytes) externs := by
  refine ⟨by decide, 0, 0, by decide, fun mpl hpl => ?_⟩
  refine coreFmtWrite_ok hpl (fun off hoff => ?_) W Step Panic Oom stackBytes
  have hP0 : (coreMultiLib.blockLib 0).text.Placeable (coreMultiLib.blockPlacement mpl 0) :=
    hpl.blocks_ok 0 (by decide)
  have hlen : 0 + 436 ≤ (coreMultiLib.blockLib 0).text.code.length := by decide
  have hhf := PlacedLib.hookFree_program_noOverrides
    (lib := coreMultiLib.blockLib 0) (pl := coreMultiLib.blockPlacement mpl 0)
    (X := externs) (svc := Syscall.standard) hP0 hlen
  have hoff_eq :
      (mpl.base 0 + BitVec.ofNat 64 off -
        (coreMultiLib.blockProgram mpl 0 externs).base).toNat = off := by
    change (mpl.base 0 + BitVec.ofNat 64 off - mpl.base 0).toNat = off
    rw [Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Program.externAt?
  rw [hoff_eq]
  exact Program.hookAtOff?_eq_none_of_hookFree hhf (Nat.zero_le _) hoff

/-! ## Compiled `rustc 1.98.1` template decoding checks -/

theorem decodeFmtArguments_fromStr_abc (x2 : BitVec 64) :
    decodeFmtArguments x2 7#64 [0x61#8, 0x62#8, 0x63#8] [] =
      some [FmtCall.writeStr x2 [0x61#8, 0x62#8, 0x63#8]] := rfl

theorem decodeFmtArguments_smoke_abc (x2 : BitVec 64) :
    decodeFmtArguments x2 0#64 [0x03#8, 0x61#8, 0x62#8, 0x63#8, 0x00#8] [] =
      some [FmtCall.writeStr (x2 + 1#64) [0x61#8, 0x62#8, 0x63#8]] := rfl

theorem decodeFmtArguments_single_default (x2 v0 fn0 : BitVec 64) :
    decodeFmtArguments x2 0#64 [0xc0#8, 0x00#8] [(v0, fn0)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := rfl

theorem decodeFmtArguments_dotted_pair (x2 v0 fn0 v1 fn1 : BitVec 64) :
    decodeFmtArguments x2 0#64 [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8] [(v0, fn0), (v1, fn1)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions,
            FmtCall.writeStr (x2 + 2#64) [0x2e#8],
            FmtCall.fmtArg 1 v1 fn1 defaultFmtOptions] := rfl

/-- Raw 51-byte template from `alloc::vec::Vec::split_off::assert_failed`
    (``"`at` split index (is {}) should be <= len (is {})"``). -/
def vecSplitOffAssertTpl : List (BitVec 8) :=
  [0x15#8, 0x60#8, 0x61#8, 0x74#8, 0x60#8, 0x20#8, 0x73#8, 0x70#8, 0x6c#8, 0x69#8, 0x74#8,
   0x20#8, 0x69#8, 0x6e#8, 0x64#8, 0x65#8, 0x78#8, 0x20#8, 0x28#8, 0x69#8, 0x73#8, 0x20#8,
   0xc0#8,
   0x17#8, 0x29#8, 0x20#8, 0x73#8, 0x68#8, 0x6f#8, 0x75#8, 0x6c#8, 0x64#8, 0x20#8, 0x62#8,
   0x65#8, 0x20#8, 0x3c#8, 0x3d#8, 0x20#8, 0x6c#8, 0x65#8, 0x6e#8, 0x20#8, 0x28#8, 0x69#8,
   0x73#8, 0x20#8,
   0xc0#8,
   0x01#8, 0x29#8,
   0x00#8]

theorem decodeFmtArguments_vecSplitOffAssert (x2 vAt vLen fnUsize : BitVec 64) :
    decodeFmtArguments x2 0#64 vecSplitOffAssertTpl [(vAt, fnUsize), (vLen, fnUsize)] =
      some [FmtCall.writeStr (x2 + 1#64)
              [0x60#8, 0x61#8, 0x74#8, 0x60#8, 0x20#8, 0x73#8, 0x70#8, 0x6c#8, 0x69#8, 0x74#8,
               0x20#8, 0x69#8, 0x6e#8, 0x64#8, 0x65#8, 0x78#8, 0x20#8, 0x28#8, 0x69#8, 0x73#8,
               0x20#8],
            FmtCall.fmtArg 0 vAt fnUsize defaultFmtOptions,
            FmtCall.writeStr (x2 + 24#64)
              [0x29#8, 0x20#8, 0x73#8, 0x68#8, 0x6f#8, 0x75#8, 0x6c#8, 0x64#8, 0x20#8, 0x62#8,
               0x65#8, 0x20#8, 0x3c#8, 0x3d#8, 0x20#8, 0x6c#8, 0x65#8, 0x6e#8, 0x20#8, 0x28#8,
               0x69#8, 0x73#8, 0x20#8],
            FmtCall.fmtArg 1 vLen fnUsize defaultFmtOptions,
            FmtCall.writeStr (x2 + 49#64) [0x29#8]] := rfl

theorem decodeFmtArguments_indirectCountWidth (x2 v0 fn0 : BitVec 64) :
    decodeFmtArguments x2 0#64
      [0x01#8, 0x2e#8, 0xd3#8, 0x30#8, 0x00#8, 0x00#8, 0x08#8, 0x01#8, 0x00#8, 0x00#8]
      [(v0, fn0), (0#64, 6#64)] =
      some [FmtCall.writeStr (x2 + 1#64) [0x2e#8],
            FmtCall.fmtArg 0 v0 fn0
              { flags := 0x08000030#32, width := 6#16, precision := 0#16 }] := rfl

theorem decodeFmtArguments_longLiteral130 (x2 : BitVec 64) :
    decodeFmtArguments x2 0#64
      ([0x80#8, 0x82#8, 0x00#8] ++ List.replicate 130 0x78#8 ++ [0x00#8]) [] =
      some [FmtCall.writeStr (x2 + 3#64) (List.replicate 130 0x78#8)] := rfl

/-! ## Non-vacuity witnesses -/

section GkWitnesses

open Arm64.Process ProofLib.Disproof

def cwWitnessW : Unit → State → SepProp := fun _ _ => emp
def cwWitnessStep : FmtCall → Unit → Bool → Unit → Prop := fun _ _ ok _ => ok = true
def cwWitnessFalse : FmtCall → Unit → State → Prop := fun _ _ _ => False

def cwStubAddr : BitVec 64 := BitVec.ofNat 64 (1 <<< 20)
def cwVtAddr : BitVec 64 := BitVec.ofNat 64 (2 <<< 20)
def cwTplAddr : BitVec 64 := BitVec.ofNat 64 (3 <<< 20)
def cwArgsAddr : BitVec 64 := BitVec.ofNat 64 (4 <<< 20)
def cwOutAddr : BitVec 64 := BitVec.ofNat 64 (5 <<< 20)
def cwEntryAddr : BitVec 64 := BitVec.ofNat 64 (6 <<< 20)
def cwSp0 : BitVec 64 := BitVec.ofNat 64 (8 <<< 20)
def cwLr0 : BitVec 64 := BitVec.ofNat 64 (9 <<< 20)

/-- 2-instruction stub `mov w0, #0; ret` returning `fmt::Result::Ok(())`. -/
def cwStubWords : List (BitVec 32) := [0x52800000#32, 0xd65f03c0#32]

def cwStubProg : Program := pureWordsProg cwStubAddr cwStubWords

theorem cwStub_writeStr_ok (out ptr : BitVec 64) (bs : List (BitVec 8)) :
    subroutine_ok cwStubProg cwStubAddr
      (fmtWriteStrCallSpec cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0 out ptr bs) := by
  apply subroutine_ok_of_sepWP_init
  intro st R s0 hpc hrun hpre _hsp
  dsimp only [fmtWriteStrCallSpec, cwWitnessW] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hmemR : s0.mem ⊨ R := Satisfies.drop_left hpre.2
  refine ⟨emp, by rwa [emp_sepConj], ?_⟩
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hrun)
  refine ⟨fun _ => ?_, rfl, ?_⟩
  · refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right true (Entails.sepExists_right () (Entails.refl _)))) ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [arm64_norm], rfl⟩, ?_⟩
    simpa [stackFrameAt] using hmemR
  · rw [CalleeSavedPreserved.iff_regs]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cwStub_argCall_ok (out vt : BitVec 64) (idx : Nat) (val : BitVec 64) (opts : FmtOptions) :
    subroutine_ok cwStubProg cwStubAddr
      (fmtArgCallSpec cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0
        out vt idx val cwStubAddr opts) := by
  apply subroutine_ok_of_sepWP_init
  intro ⟨st, f⟩ R s0 hpc hrun hpre _hsp
  dsimp only [fmtArgCallSpec, cwWitnessW] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hfR : s0.mem ⊨ memRegion f 24 ∗ R := by
    have h1 : formatterAt f out vt opts ∗ (emp ∗ stackFrameAt s0.sp 0) ⊢ memRegion f 24 := by
      simpa [stackFrameAt] using formatterAt_entails_memRegion24 f out vt opts
    exact Satisfies.mono (sepConj_mono_left h1) hpre.2
  refine ⟨memRegion f 24, hfR, ?_⟩
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hrun)
  refine ⟨fun hm => ?_, rfl, ?_⟩
  · refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right true (Entails.sepExists_right () (Entails.refl _)))) ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [arm64_norm], rfl⟩, ?_⟩
    simpa [stackFrameAt] using hm
  · rw [CalleeSavedPreserved.iff_regs]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity witness for literal `"abc"` (`[0x03, 'a', 'b', 'c', 0x00]`): exhibits a concrete
    `Program` and `State` satisfying `FmtCallbacks`, `spAligned = true`, `CodeLoaded`, and
    `(coreFmtWriteSpec ...).pre`. -/
theorem coreFmtWrite_gk_witness1_smoke :
    let tpl : List (BitVec 8) := [0x03#8, 0x61#8, 0x62#8, 0x63#8, 0x00#8]
    let cs : List FmtCall := [FmtCall.writeStr (cwTplAddr + 1#64) [0x61#8, 0x62#8, 0x63#8]]
    FmtCallbacks cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0
      cwOutAddr cwVtAddr cwStubAddr cs ∧
    ∃ s0 : State,
      s0.status = .Running ∧
      s0.spAligned = true ∧
      cwStubProg.CodeLoaded s0.mem ∧
      s0.mem ⊨
        (coreFmtWriteSpec cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0).pre
          (cwOutAddr, cwVtAddr, cwStubAddr, true, tpl, [], ()) s0 := by
  intro tpl cs
  have hcb : FmtCallbacks cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0
      cwOutAddr cwVtAddr cwStubAddr cs :=
    { transport := fun _ _ _ _ => Entails.refl _
      write_str := fun ptr bs _ => cwStub_writeStr_ok cwOutAddr ptr bs
      fmt_arg := fun _ _ _ _ hmem => False.elim (by simp [cs] at hmem) }
  refine ⟨hcb, ?_⟩
  let rs : List DisproofRegion :=
    [ .ro64 (cwVtAddr + 0x18#64) cwStubAddr,
      .roBytes cwTplAddr tpl,
      .rwRegion (cwSp0 - 0x70#64) 0x70 ]
  let s0 := mkDisproofState cwStubProg cwEntryAddr cwSp0 cwLr0
    [(.x0, cwOutAddr), (.x1, cwVtAddr), (.x2, cwTplAddr), (.x3, 0#64)] rs
  have hcl : cwStubProg.CodeLoaded s0.mem :=
    mkDisproofState_codeLoaded cwStubProg cwEntryAddr cwSp0 cwLr0 _ rs
  have hsat : s0.mem ⊨ DisproofRegion.listToSepProp rs :=
    mkDisproofState_satisfies cwStubProg cwEntryAddr cwSp0 cwLr0 _ rs
  refine ⟨s0, rfl, by decide, hcl, ?_⟩
  have hx0_eq : s0.readReg64 .x0 = cwOutAddr := by decide
  have hx1_eq : s0.readReg64 .x1 = cwVtAddr := by decide
  have hx2_eq : s0.readReg64 .x2 = cwTplAddr := by decide
  have hx3_eq : s0.readReg64 .x3 = 0#64 := by decide
  dsimp only [coreFmtWriteSpec, fmtArgumentsAt, fmtArgEntriesAt, cwWitnessW]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_eq, hx1_eq, by decide, cs, ?_, hcb⟩, ?_⟩
  · rw [hx2_eq, hx3_eq]
    exact decodeFmtArguments_smoke_abc cwTplAddr
  · have hsp_eq : s0.sp = cwSp0 := rfl
    rw [hx2_eq, hx3_eq, hsp_eq, show (0x70 + 0 : Nat) = 0x70 from rfl,
      stackFrameAt_eq_memRegion cwSp0 0x70 (by decide)]
    have h0_even : (0#64 : BitVec 64).getLsbD 0 = false := by decide
    rw [h0_even]
    dsimp only [rs, DisproofRegion.listToSepProp, DisproofRegion.toSepProp] at hsat
    simpa [fmtArgEntriesAt, sepConj_emp, emp_sepConj, sepConj_assoc] using hsat

/-- Non-vacuity witness for placeholder `"{}"` (`[0xc0, 0x00]`): exhibits a concrete `Program` and
    `State` with `args = [(42, cwStubAddr)]` satisfying `FmtCallbacks`, `spAligned = true`,
    `CodeLoaded`, and `(coreFmtWriteSpec ...).pre`. -/
theorem coreFmtWrite_gk_witness2_placeholder :
    let tpl : List (BitVec 8) := [0xc0#8, 0x00#8]
    let args : List (BitVec 64 × BitVec 64) := [(42#64, cwStubAddr)]
    let cs : List FmtCall := [FmtCall.fmtArg 0 42#64 cwStubAddr defaultFmtOptions]
    FmtCallbacks cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0
      cwOutAddr cwVtAddr cwStubAddr cs ∧
    ∃ s0 : State,
      s0.status = .Running ∧
      s0.spAligned = true ∧
      cwStubProg.CodeLoaded s0.mem ∧
      s0.mem ⊨
        (coreFmtWriteSpec cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0).pre
          (cwOutAddr, cwVtAddr, cwStubAddr, true, tpl, args, ()) s0 := by
  intro tpl args cs
  have hcb : FmtCallbacks cwStubProg cwWitnessW cwWitnessStep cwWitnessFalse cwWitnessFalse 0
      cwOutAddr cwVtAddr cwStubAddr cs :=
    { transport := fun _ _ _ _ => Entails.refl _
      write_str := fun _ _ hmem => False.elim (by simp [cs] at hmem)
      fmt_arg := fun idx val fn opts hmem => by
        have hm : FmtCall.fmtArg idx val fn opts =
            FmtCall.fmtArg 0 42#64 cwStubAddr defaultFmtOptions := by
          simpa [cs] using hmem
        injection hm with _ _ hfn _
        subst hfn
        exact cwStub_argCall_ok cwOutAddr cwVtAddr idx val opts }
  refine ⟨hcb, ?_⟩
  let rs : List DisproofRegion :=
    [ .ro64 (cwVtAddr + 0x18#64) cwStubAddr,
      .roBytes cwTplAddr tpl,
      .ro64 cwArgsAddr 42#64,
      .ro64 (cwArgsAddr + 8#64) cwStubAddr,
      .rwRegion (cwSp0 - 0x70#64) 0x70 ]
  let s0 := mkDisproofState cwStubProg cwEntryAddr cwSp0 cwLr0
    [(.x0, cwOutAddr), (.x1, cwVtAddr), (.x2, cwTplAddr), (.x3, cwArgsAddr)] rs
  have hcl : cwStubProg.CodeLoaded s0.mem :=
    mkDisproofState_codeLoaded cwStubProg cwEntryAddr cwSp0 cwLr0 _ rs
  have hsat : s0.mem ⊨ DisproofRegion.listToSepProp rs :=
    mkDisproofState_satisfies cwStubProg cwEntryAddr cwSp0 cwLr0 _ rs
  refine ⟨s0, rfl, by decide, hcl, ?_⟩
  have hx0_eq : s0.readReg64 .x0 = cwOutAddr := by decide
  have hx1_eq : s0.readReg64 .x1 = cwVtAddr := by decide
  have hx2_eq : s0.readReg64 .x2 = cwTplAddr := by decide
  have hx3_eq : s0.readReg64 .x3 = cwArgsAddr := by decide
  have hx3_even : cwArgsAddr.getLsbD 0 = false := by decide
  dsimp only [coreFmtWriteSpec, fmtArgumentsAt, cwWitnessW]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_eq, hx1_eq, by decide, cs, ?_, hcb⟩, ?_⟩
  · rw [hx2_eq, hx3_eq]
    simp only [decodeFmtArguments, hx3_even]
    rfl
  · have hsp_eq : s0.sp = cwSp0 := rfl
    rw [hx2_eq, hx3_eq, hx3_even, hsp_eq, show (0x70 + 0 : Nat) = 0x70 from rfl,
      stackFrameAt_eq_memRegion cwSp0 0x70 (by decide)]
    dsimp only [args, fmtArgEntriesAt]
    dsimp only [rs, DisproofRegion.listToSepProp, DisproofRegion.toSepProp] at hsat
    simpa [sepConj_emp, emp_sepConj, sepConj_assoc] using hsat

end GkWitnesses


end VerifiedLibraries.RustStd
