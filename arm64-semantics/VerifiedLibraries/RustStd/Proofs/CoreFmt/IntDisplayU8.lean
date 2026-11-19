/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayLemmas

/-!
# `<u8 as core::fmt::Display>::fmt` Proofs

Placement-generic verification of `<u8 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block `6`)
against `u8DisplayFmtSpec`, parameterized by a `formatterPadIntegralSpec` callee contract.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd
open IntDisplayAux

private theorem bv_u8_magic_div100 {n : Nat} (hn : n < 256) :
    BitVec.truncate 32
      ((BitVec.zeroExtend 64 (0#32 + BitVec.truncate 32 (BitVec.ofNat 64 n) * 41#32)) >>> 12) =
      BitVec.ofNat 32 (n / 100) ∧
    (BitVec.zeroExtend 64 (0#32 + BitVec.truncate 32 (BitVec.ofNat 64 n) * 41#32)) >>> 12 &&&
      0xfffff#64 = BitVec.ofNat 64 (n / 100) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (n / 100)) = BitVec.ofNat 64 (n / 100) := by
  have hm := magic_u8_div_100 hn
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp [Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : n * 41 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : n * 41 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n / 100 < 2 ^ 32)]
    omega
  · rw [BitVec.toNat_and]
    have h1 : ((BitVec.zeroExtend 64 (0#32 + BitVec.truncate 32 (BitVec.ofNat 64 n) * 41#32)) >>> 12).toNat =
        n / 100 := by
      simp [Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : n * 41 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : n * 41 < 2 ^ 64)]
      omega
    have hmask : (0xfffff#64).toNat = 2 ^ 20 - 1 := rfl
    rw [h1, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n / 100 < 2 ^ 20),
      Nat.mod_eq_of_lt (by omega : n / 100 < 2 ^ 64)]
  · simp [Nat.mod_eq_of_lt (by omega : n / 100 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : n / 100 < 2 ^ 64)]

private theorem step_u8CallPad_bl [CoreFmtPlacement]
    {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl06.base + 0x94#64) (hrun : s.status = .Running)
    (hnext : SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 30#5) (coreFmtPl06.base + 0x98#64)).setPC
        (coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym))
      Pre post oom) :
    SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s Pre post oom := by
  have hf := coreFmtPC06_rebase_fetch_0x94 coreFmtPl06.base (fun _ => none)
  exact SepWP.step_pure hpc hrun hf
    (by
      have hrho : coreFmtPl06.ρ "<core::fmt::Formatter>::pad_integral" =
          coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym := rfl
      simp [wp_norm, arm64_norm, Reg.lr, hrho, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem step_u8Load_val [CoreFmtPlacement] (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8)
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl06.base + 0x0c#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = valPtr)
    (hnext : SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 10#5) (BitVec.ofNat 64 v.toNat)).setPC (coreFmtPl06.base + 0x10#64))
      (fmtRef8 ro valPtr v ∗ Fr) post oom) :
    SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s
      (fmtRef8 ro valPtr v ∗ Fr) post oom := by
  cases ro
  · rw [fmtRef8_false] at hnext ⊢
    wp_step
    simpa [wp_norm, arm64_norm, bv_lin_norm] using hnext
  · rw [fmtRef8_true] at hnext ⊢
    wp_step
    simpa [wp_norm, arm64_norm, bv_lin_norm] using hnext

private theorem u8Display_last_digit_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (idx1 q1 : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hidx1 : 1 ≤ idx1 ∧ idx1 ≤ 3) (hq1 : q1 < 10)
    (hpc : s.pc = coreFmtPl06.base + 0x5c#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 (.gpr 29#5) = sp0 - 16#64)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 idx1)
    (hx9 : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q1)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl06.base + 0x74#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 (.gpr 29#5) = sp0 - 16#64 →
      s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (idx1 - 1) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 13#64) (idx1 - 1) ∗
          (((sp0 - 32#64) + 13#64 + BitVec.ofNat 64 (idx1 - 1)) ↦ₛ (decDigit8 q1 :: suf))) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion ((sp0 - 32#64) + 13#64) idx1 ∗
        (((sp0 - 32#64) + 13#64 + BitVec.ofNat 64 idx1) ↦ₛ suf)) ∗ Fr)
      post oom := by
  let bufBase := (sp0 - 32#64) + 13#64
  obtain ⟨_, hubf6, _, _, hand127, _, _, hsh254, _, _⟩ := bv_ubfiz_digit hq1
  have hsub8 : BitVec.ofNat 64 idx1 - 1#64 = BitVec.ofNat 64 (idx1 - 1) :=
    bv_ofNat_sub_small hidx1.1
  have hx29_sub3 : (sp0 - 16#64) - 3#64 = bufBase := by
    dsimp only [bufBase]; simp [bv_lin_norm]
  have hlut_off : lutAddr + BitVec.ofNat 64 (2 * q1) + 1#64 =
      lutAddr + BitVec.ofNat 64 (2 * q1 + 1) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  have hmr_split : memRegion bufBase idx1 ⊢
      memRegion bufBase (idx1 - 1) ∗
        (∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ b0) := by
    rw [memRegion_split_le bufBase (idx1 - 1) idx1 (by omega) (by omega),
        show idx1 - (idx1 - 1) = 1 by omega]
    exact sepConj_mono_right (memRegion1_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hmr_split))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro b0
  conv =>
    arg 4; arg 1; arg 1
    rw [decDigitsLut_focus8_odd lutAddr (i := q1) (by omega)]
  iterate 6 wp_step
  have hent_out :
      ((((lutAddr + BitVec.ofNat 64 (2 * q1 + 1)) ↦₈ᵣ decDigit8 q1) ∗
        (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * q1 + 1) ∗
          (lutAddr + BitVec.ofNat 64 (2 * q1 + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * q1 + 2))) ∗
       (memRegion bufBase (idx1 - 1) ∗
         ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigit8 q1)) ∗
       ((bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf)) ∗ Fr ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (idx1 - 1) ∗
        ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦ₛ (decDigit8 q1 :: suf))) ∗ Fr) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus8_odd lutAddr (i := q1) hq1]
    refine sepConj_mono_right ?_
    rw [sepConj_assoc]
    refine sepConj_mono_right ?_
    rw [pointsToBytes_cons,
        show bufBase + BitVec.ofNat 64 (idx1 - 1) + 1#64 = bufBase + BitVec.ofNat 64 idx1 by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add (idx1 - 1) 1, show idx1 - 1 + 1 = idx1 by omega]]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx29])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)

private theorem u8Display_digits_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (v : BitVec 8)
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl06.base + 0x18#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 (.gpr 29#5) = sp0 - 16#64)
    (hx9 : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 v.toNat)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl06.base + 0x74#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 (.gpr 29#5) = sp0 - 16#64 →
      s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (3 - (formatDecimalNat v.toNat).length) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 13#64) (3 - (formatDecimalNat v.toNat).length) ∗
          (((sp0 - 32#64) + 13#64 + BitVec.ofNat 64 (3 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat)) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion ((sp0 - 32#64) + 13#64) 3) ∗ Fr)
      post oom := by
  have hn : v.toNat < 256 := v.isLt
  let bufBase := (sp0 - 32#64) + 13#64
  obtain ⟨_, h1d, h2d, h3d⟩ := formatDecimalNat_u8_cases hn
  have htr10 : BitVec.truncate 32 (BitVec.ofNat 64 v.toNat) = BitVec.ofNat 32 v.toNat := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  by_cases hlt10 : v.toNat < 10
  · have hv_ult : (BitVec.ofNat 32 v.toNat).ult 10#32 = true := by
      simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 32), hlt10]
    have hds_eq : formatDecimalNat v.toNat = [decDigit8 v.toNat] := h1d hlt10
    have hidx_eq : 3 - (formatDecimalNat v.toNat).length = 2 := by rw [hds_eq]; rfl
    have hpre_nil :
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 3) ∗ Fr) ⊢
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 3 ∗
          ((bufBase + BitVec.ofNat 64 3) ↦ₛ [])) ∗ Fr) := by
      rw [pointsToBytes_nil, sepConj_emp]; exact Entails.refl _
    refine SepWP.weaken_pre hpre_nil ?_
    by_cases hn0 : v = 0#8
    · subst v
      iterate 5 wp_step
      refine u8Display_last_digit_wp lutAddr sp0 3 0 [] ⟨by decide, by decide⟩ (by decide)
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx29])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
      intro s' hpc' hrun' hsp' hx29' hx1' hx8' hcs' hsys'
      have h0_eq : formatDecimalNat (0#8).toNat = [decDigit8 0] := rfl
      rw [show (3 - 1 : Nat) = 3 - (formatDecimalNat (0#8).toNat).length from rfl] at hx8' ⊢
      rw [← h0_eq]
      exact hnext s' hpc' hrun'
        (by simpa [wp_norm, arm64_norm] using hsp') hx29'
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx8'
        (CalleeSavedPreserved.trans
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
        (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')
    · have hv_pos : 0 < v.toNat := by
        refine Classical.byContradiction fun h0 => hn0 (BitVec.eq_of_toNat_eq (by simp; omega))
      have hzext10 : BitVec.zeroExtend 64 (BitVec.ofNat 32 v.toNat) = BitVec.ofNat 64 v.toNat := by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)]
      have hv_beq64 : (BitVec.ofNat 64 v.toNat == 0#64) = false := by
        apply beq_false_of_ne; intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)] at this; omega
      iterate 6 wp_step
      refine u8Display_last_digit_wp lutAddr sp0 3 v.toNat [] ⟨by decide, by decide⟩ hlt10
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx29])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
      intro s' hpc' hrun' hsp' hx29' hx1' hx8' hcs' hsys'
      rw [show (3 - 1 : Nat) = 3 - (formatDecimalNat v.toNat).length by omega] at hx8' ⊢
      rw [← hds_eq]
      exact hnext s' hpc' hrun'
        (by simpa [wp_norm, arm64_norm] using hsp') hx29'
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx8'
        (CalleeSavedPreserved.trans
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
        (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')
  · have hv_ult : (BitVec.ofNat 32 v.toNat).ult 10#32 = false := by
      apply Bool.eq_false_iff.mpr; simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 32)]; omega
    have hv_toNat_ne : v.toNat ≠ 0 := by omega
    have hv_beq64 : (BitVec.setWidth 64 v == 0#64) = false := by
      apply beq_false_of_ne; intro h; have := congrArg BitVec.toNat h; simp at this; omega
    have hnez32 : BitVec.ofNat 32 v.toNat ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 32)] at this; omega
    obtain ⟨hdiv_tr, hdiv_and, hdiv_zext⟩ := bv_u8_magic_div100 hn
    have hrem100 := bv_msub32_rem v.toNat 100 (by decide) (by omega)
    have hq_tr : BitVec.truncate 32 (BitVec.ofNat 64 (v.toNat / 100)) = BitVec.ofNat 32 (v.toNat / 100) := by
      rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rw [hq_tr] at hrem100
    rw [htr10] at hdiv_tr hdiv_and hrem100
    obtain ⟨_, _, hrem_zext, _, hrem_and8, hrem_lsl1⟩ := bv_uxtw_lsl1 (d := v.toNat % 100) (by omega)
    have hx29_sub2 : (sp0 - 16#64) - 2#64 = bufBase + 1#64 := by
      dsimp only [bufBase]; simp [bv_lin_norm]
    have hmr_split2 : memRegion bufBase 3 ⊢
        memRegion bufBase 1 ∗ (∃∗ u : BitVec 16, (bufBase + 1#64) ↦₁₆ u) := by
      rw [memRegion_split_le bufBase 1 3 (by decide) (by decide)]
      exact sepConj_mono_right (memRegion2_entails _)
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right hmr_split2)) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro u0
    conv =>
      arg 4; arg 1; arg 1
      rw [decDigitsLut_focus16 lutAddr (i := v.toNat % 100) (by omega)]
    iterate 12 wp_step
    have hrepack2 :
        ((((lutAddr + BitVec.ofNat 64 (2 * (v.toNat % 100))) ↦₁₆ᵣ
            pack16 (decDigit8 ((v.toNat % 100) / 10)) (decDigit8 ((v.toNat % 100) % 10))) ∗
          (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * (v.toNat % 100)) ∗
            (lutAddr + BitVec.ofNat 64 (2 * (v.toNat % 100) + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * (v.toNat % 100) + 2))) ∗
         (memRegion bufBase 1 ∗
          ((bufBase + 1#64) ↦₁₆
            pack16 (decDigit8 ((v.toNat % 100) / 10)) (decDigit8 ((v.toNat % 100) % 10))))) ∗ Fr ⊢
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase 1 ∗
          ((bufBase + BitVec.ofNat 64 1) ↦ₛ
            [decDigit8 ((v.toNat % 100) / 10), decDigit8 ((v.toNat % 100) % 10)])) ∗ Fr) := by
      apply sepConj_mono_left
      rw [← decDigitsLut_focus16 lutAddr (i := v.toNat % 100) (by omega)]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      unfold pack16
      rw [← pointsTo8_pair_eq_16, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
          show bufBase + 1#64 + 1#64 = bufBase + 2#64 by simp [bv_lin_norm]]
      exact Entails.refl _
    refine SepWP.weaken_pre hrepack2 ?_
    by_cases hlt100 : v.toNat < 100
    · have hq0 : v.toNat / 100 = 0 := Nat.div_eq_of_lt hlt100
      have hmod100 : v.toNat % 100 = v.toNat := Nat.mod_eq_of_lt hlt100
      have hds_eq : formatDecimalNat v.toNat =
          [decDigit8 ((v.toNat % 100) / 10), decDigit8 ((v.toNat % 100) % 10)] := by
        rw [hmod100]; exact h2d (by omega) hlt100
      have hidx_eq : 3 - (formatDecimalNat v.toNat).length = 1 := by rw [hds_eq]; rfl
      rw [hq0] at hdiv_tr hdiv_and hdiv_zext
      wp_step
      rw [← hds_eq, ← hidx_eq]
      exact hnext _
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx29])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by rw [hidx_eq]; simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    · have hq_beq64 : (BitVec.ofNat 64 (v.toNat / 100) == 0#64) = false := by
        apply beq_false_of_ne; intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : v.toNat / 100 < 2 ^ 64)] at this; omega
      have hds_eq : formatDecimalNat v.toNat =
          [decDigit8 (v.toNat / 100), decDigit8 ((v.toNat % 100) / 10), decDigit8 ((v.toNat % 100) % 10)] :=
        h3d (by omega)
      have hidx_eq : 3 - (formatDecimalNat v.toNat).length = 0 := by rw [hds_eq]; rfl
      wp_step
      refine u8Display_last_digit_wp lutAddr sp0 1 (v.toNat / 100)
        [decDigit8 ((v.toNat % 100) / 10), decDigit8 ((v.toNat % 100) % 10)]
        ⟨by decide, by decide⟩ (by omega)
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx29])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
      intro s' hpc' hrun' hsp' hx29' hx1' hx8' hcs' hsys'
      rw [show (1 - 1 : Nat) = 3 - (formatDecimalNat v.toNat).length by omega] at hx8' ⊢
      rw [← hds_eq]
      exact hnext s' hpc' hrun'
        (by simpa [wp_norm, arm64_norm] using hsp') hx29'
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx8'
        (CalleeSavedPreserved.trans
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
        (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')

private theorem u8DisplayFmt_gen_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    {keep padKeep : Nat → Bool}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hkeep6 : keep 6 = true)
    (hpad_sub : ∀ k, k < coreFmtMultiLib.blocks.length → padKeep k = true → keep k = true)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 6)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere keep mpl
        (u8DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_u8Display hpl]
  apply subroutine_ok_of_sepWPp_init
  intro ⟨st, f⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, u8DisplayFmtSpec] at hpre
  rw [sepConj_assoc (⌜_⌝ ∗ _), satisfies_sepConj_pure_assoc] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hno_alt⟩, hpre⟩
  have hm0 : s0.mem ⊨ stackFrameAt s0.sp (192 + stackBytes) ∗
      (fmtRef8 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
       formatterAt f out vt opts ∗ W st s0 ∗ R) :=
    Satisfies.mono (by sep_frame) hpre
  obtain ⟨_, hfr⟩ := frozen_of_codeLoaded (hcl 6 (by decide) hkeep6)
    (by simp only [MultiPlacedLib.blockProgram, PlacedLib.program, Obj.CodeBlock.length_patched]; decide)
  have hstk_lt : 192 + stackBytes < 2 ^ 64 := stackFrameAt_lt_pow64_of_frozen hfr hm0
  have hm1 := Satisfies.mono (sepConj_mono_left (localFrame32_full_split s0.sp stackBytes 13 3 (by decide) hstk_lt)) hm0
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨u29, u30, hm1⟩
  let bufBase := (s0.sp - 32#64) + 13#64
  let ds := formatDecimalNat v.toNat
  have hds_bounds : 1 ≤ ds.length ∧ ds.length ≤ 3 := (formatDecimalNat_u8_cases v.isLt).1
  let idx := 3 - ds.length
  let dsPtr := bufBase + BitVec.ofNat 64 idx
  let P0 : SepProp :=
    (((s0.sp - 16#64) ↦₆₄ u29) ∗ ((s0.sp - 8#64) ↦₆₄ u30)) ∗
    fmtRef8 ro valPtr v ∗
    ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 3) ∗
    (formatterAt f out vt opts ∗ W st s0 ∗
     memRegion (s0.sp - 32#64) 13 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes))
  refine ⟨P0, Satisfies.mono (by dsimp only [P0, bufBase]; sep_frame) hm1, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
    6 ⟨by decide, hkeep6⟩ hnoext coreFmtNoSvc0_06
    (mid := coreFmtMultiLib.resolve mpl formatterPadIntegralSym) hcl
  intro s' hcpu_in
  change SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl06.base := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  have hx0' : s'.readReg64 (.gpr 0#5) = valPtr := (hcpu_in.readReg64 .x0).trans hx0
  have hx1' : s'.readReg64 (.gpr 1#5) = f := (hcpu_in.readReg64 .x1).trans hx1
  have hfp' : s'.readReg64 (.gpr 29#5) = s0.readReg64 Reg.fp := hcpu_in.readReg64 Reg.fp
  have hlr' : s'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
  dsimp only [P0]
  iterate 3 wp_step
  refine SepWP.weaken_pre (by sep_frame :
    _ ⊢ fmtRef8 ro valPtr v ∗
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 3) ∗
       (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        formatterAt f out vt opts ∗ W st s0 ∗
        memRegion (s0.sp - 32#64) 13 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes)))) ?_
  apply step_u8Load_val ro valPtr v
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
  apply coreFmtPC06_pairStep_0x10 coreFmtPl06.base (fun _ => none) rfl
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
  have hlut_rho : coreFmtPl06.ρ "rust_core_fmt:.rodata..Lanon.203" = lutAddr := by
    rw [hlut, resolve_decDigitsLut]; rfl
  refine SepWP.weaken_pre (by sep_frame :
    _ ⊢ ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 3) ∗
      (fmtRef8 ro valPtr v ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       formatterAt f out vt opts ∗ W st s0 ∗
       memRegion (s0.sp - 32#64) 13 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes))) ?_
  refine u8Display_digits_wp lutAddr s0.sp v
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hlut_rho])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
  intro sd hpcd hrund hspd hx29d hx1d hx8d hcsd hsysd
  have hx1d_eq : sd.readReg64 (.gpr 1#5) = f := by
    simpa (config := { decide := true }) [wp_norm, arm64_norm, hx1'] using hx1d
  have hspd_eq : sd.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm, hsp'] using hspd
  have hsub_len : 3#64 - BitVec.ofNat 64 (3 - (formatDecimalNat v.toNat).length) =
      BitVec.ofNat 64 ds.length :=
    (bv_ofNat_sub_small (by dsimp only [ds] at hds_bounds; omega)).trans
      (by dsimp only [ds] at hds_bounds ⊢; congr 1; omega)
  have hx29_sub3 : (s0.sp - 16#64) - 3#64 = bufBase := by dsimp only [bufBase]; simp [bv_lin_norm]
  iterate 8 wp_step
  apply step_u8CallPad_bl
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrund])
  apply SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hrund])
  intro s1 hcpu1 hcl1 hpseg1
  have hfw01 : FmtWriteFrame s0 s1 := intFmtWriteFrame_of_seg hcpu_in hcpu1 hpseg1
    (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
      (SysRegsEq.trans hsysd ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩))
  have hcl1_pad : coreFmtMultiLib.CodeLoadedWhere padKeep mpl s1.mem :=
    fun k hk hpk => hcl1 k hk (hpad_sub k hk hpk)
  have hsp1 : s1.sp = s0.sp - 32#64 := hcpu1.sp_eq.trans (by simp [wp_norm, arm64_norm, hspd_eq])
  have hsp1_align : s1.spAligned = true := by
    rw [State.spAligned.eq_1, hsp1]; exact s0.spAligned_sub 32#64 hsp_align
  have hcs01 : CalleeSavedPreserved (s0.writeReg64 Reg.fp (s0.sp - 16#64)) s1 :=
    SameCpuState.calleeSavedPreserved (sameCpu_writeReg64 hcpu_in Reg.fp (s0.sp - 16#64)) hcpu1
      (CalleeSavedPreserved.trans
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm])
        (CalleeSavedPreserved.trans hcsd
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])))
  let F_call : SepProp :=
    (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗ fmtRef8 ro valPtr v ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    memRegion (s0.sp - 32#64) 13
  refine sepWPp_call_keepsFrozen (hPad f dsPtr ds) (x := st) (F := F_call)
    (ret_pc := coreFmtPl06.base + 0x98#64)
    (hpc := hcpu1.pc_eq)
    (hrun := hcpu1.status_eq.trans (by simp [wp_norm, arm64_norm, hrund]))
    (hsp_align := hsp1_align)
    (hlr := (hcpu1.readReg64 Reg.lr).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
    (hpre := ?_) (hexit_eq := fun _ _ => rfl) (hpanic := ?_) (hnext := ?_) (hoom := ?_)
  · intro R' hm'
    have hx0_1 : s1.readReg64 .x0 = f :=
      (hcpu1.readReg64 .x0).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    have hx1_1 : s1.readReg32 .x1 = 1#32 :=
      (hcpu1.readReg32 .x1).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    have hx4_1 : s1.readReg64 .x4 = dsPtr :=
      (hcpu1.readReg64 .x4).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]; rfl)
    have hx5_1 : (s1.readReg64 .x5).toNat = ds.length := by
      have hx5_eq : s1.readReg64 .x5 = BitVec.ofNat 64 ds.length :=
        (hcpu1.readReg64 .x5).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm])
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
    refine Entails.trans (by sep_frame :
      _ ⊢ W st s0 ∗ (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗ (dsPtr ↦ₛ ds)) ∗
         (fmtRef8 ro valPtr v ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗ formatterAt f out vt opts ∗
          memRegion (s0.sp - 32#64) 13 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes)) ∗ R')) ?_
    refine Entails.trans (sepConj_mono_left (hW st s0 s1 hfw01)) ?_; sep_frame
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
    apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
      6 ⟨by decide, hkeep6⟩ hnoext coreFmtNoSvc0_06 (mid := s0.readReg64 Reg.lr) hcl2
    intro s2' hcpu2
    change SepWP (coreFmtPC06.rebase coreFmtPl06.base (fun _ => none)) _ _ _ _
    have hpc2' : s2'.pc = coreFmtPl06.base + 0x98#64 := hcpu2.pc_eq.trans hpc2
    have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun2
    have hsp2' : s2'.sp = s0.sp - 32#64 := hcpu2.sp_eq.trans (hsp2.trans hsp1)
    have hw0_2' : s2'.readReg32 .x0 = (if ok then 0#32 else 1#32) := (hcpu2.readReg32 .x0).trans hw0_2
    refine SepWP.weaken_pre (by dsimp only [F_call]; rw [hsp1]; sep_frame :
      _ ⊢ (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
        ((if ok then formatterAt f out vt opts else memRegion f 24) ∗
         (dsPtr ↦ₛ ds) ∗ W st' s2 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ∗
         (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗
         fmtRef8 ro valPtr v ∗ memRegion (s0.sp - 32#64) 13)) ?_
    have hsp_epi : (s0.sp - 32#64) + 16#64 = s0.sp - 16#64 := by simp [bv_lin_norm]
    have hsp_epi2 : (s0.sp - 32#64) + 32#64 = s0.sp := by simp [bv_lin_norm]
    iterate 3 wp_step
    apply SepWP.done (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun2'])
    intro s3 hcpu3 _ hpseg3
    have hfw23 : FmtWriteFrame s2 s3 :=
      intFmtWriteFrame_of_seg hcpu2 hcpu3 hpseg3 ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    have hw0_3 : s3.readReg32 .x0 = (if ok then 0#32 else 1#32) :=
      (hcpu3.readReg32 .x0).trans (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hw0_2')
    have hsp3 : s3.sp = s0.sp := hcpu3.sp_eq.trans (by simp [wp_norm, arm64_norm])
    have hcs23 : CalleeSavedPreserved (s2.writeReg64 Reg.fp (s0.readReg64 Reg.fp)) s3 :=
      SameCpuState.calleeSavedPreserved (sameCpu_writeReg64 hcpu2 Reg.fp (s0.readReg64 Reg.fp)) hcpu3
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm])
    apply SepWPp.done
      (hcpu3.pc_eq.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
      (hcpu3.status_eq.trans (by simp [wp_norm, arm64_norm, hrun2']))
    refine ⟨?_, hsp3, calleeSaved_of_fp_saved hcs01 hcs12 hcs23⟩
    intro hmf3
    have hrepack32 := localFrame32_repack s0.sp 13 3 (by decide)
      (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr) ds hds_bounds.2
    have hstk_join : stackFrameAt s0.sp 32 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ⊢
        stackFrameAt s0.sp (192 + stackBytes) := by
      rw [show 192 + stackBytes = 32 + (160 + stackBytes) by omega,
          stackFrameAt_split s0.sp 32 (160 + stackBytes) (by omega)]
      exact Entails.refl _
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, u8DisplayFmtSpec]
    refine Satisfies.mono ?_ hmf3
    refine Entails.sepExists_intro_frame ok ?_
    refine Entails.sepExists_intro_frame st' ?_
    rw [pure_sepConj_of_true ⟨hw0_3, hops⟩]
    apply sepConj_mono_left
    refine Entails.trans (by sep_frame :
      _ ⊢ (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
           memRegion (s0.sp - 32#64) 13 ∗ memRegion bufBase idx ∗ (dsPtr ↦ₛ ds)) ∗
          stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ∗ W st' s2 ∗
          (fmtRef8 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
           (if ok then formatterAt f out vt opts else memRegion f 24))) ?_
    refine Entails.trans (sepConj_mono hrepack32 (sepConj_mono_right (sepConj_mono_left (hW st' s2 s3 hfw23)))) ?_
    rw [← sepConj_assoc]
    refine Entails.trans (sepConj_mono_left hstk_join) ?_; sep_frame
  · intro sf R' _ hoom
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec, u8DisplayFmtSpec] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

/-- `<u8 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block `6`) satisfies `u8DisplayFmtSpec`
    under `u8DisplaySelfKeep`, block-local hook tolerance, and a `pad_integral` contract `hPad`. -/
theorem u8DisplayFmt_of_padIntegral_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 6)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u8DisplaySelfKeep mpl
        (u8DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  refine u8DisplayFmt_gen_ok (keep := u8DisplaySelfKeep) (padKeep := fun _ => false)
    hpl (by decide) (fun _ _ h => Bool.noConfusion h) hnoext hW stackBytes lutAddr out vt opts hlut ?_ ro valPtr v
  intro f dsPtr ds
  exact subroutine_ok_mono_entails (hPad f dsPtr ds)
    (fun _ _ => by dsimp only [MultiPlacedLib.withCodeLoadedWhere]; rw [sepConj_comm]; exact Entails.pure_left fun _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

/-- `<u8 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block `6`) with `pad_integral` supplied
    under `withCodeLoadedWhere padIntegralKeep`. -/
theorem u8DisplayFmt_of_padIntegralWhere_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 6)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u8DisplayKeep mpl
        (u8DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) :=
  u8DisplayFmt_gen_ok hpl (by decide)
    (fun k _ h => by simp [u8DisplayKeep, h]) hnoext hW stackBytes lutAddr out vt opts hlut hPad ro valPtr v

end VerifiedLibraries.RustStd.CoreFmt
