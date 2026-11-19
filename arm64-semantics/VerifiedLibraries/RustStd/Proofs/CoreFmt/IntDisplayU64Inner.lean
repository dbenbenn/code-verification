/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayLemmas

/-!
# `core::fmt::num::<impl u64>::_fmt_inner` Proofs

Proves `u64FmtInner_wp` (`coreFmtMultiLib` block `3`), showing that `<u64>::_fmt_inner`
renders the decimal digits of a `u64` right-aligned into a 20-byte buffer via the two-digit
lookup table over the rebased single-block program `coreFmtPC03`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd
open IntDisplayAux

private theorem bv_div_10000 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 m) * 0x346dc5d63886594b#128) >>> 64) >>> 11 =
      BitVec.ofNat 64 (m / 10000) := by
  have hc128 : (0x346dc5d63886594b#128) = BitVec.zeroExtend 128 0x346dc5d63886594b#64 := rfl
  rw [hc128]
  change (((BitVec.ofNat 64 m).setWidth 128 * (0x346dc5d63886594b#64).setWidth 128) >>> 64).setWidth 64 >>> 11 =
    BitVec.ofNat 64 (m / 10000)
  rw [BitVec.setWidth_umulh]
  apply BitVec.eq_of_toNat_eq
  have hb : (0x346dc5d63886594b#64).toNat = 3777893186295716171 := rfl
  simp only [BitVec.toNat_ushiftRight, hb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hm]
  have hhi : m * 3777893186295716171 / 18446744073709551616 < 2 ^ 64 := by omega
  have hq : m / 10000 < 2 ^ 64 := by omega
  have hpow64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hpow11 : (2 : Nat) ^ 11 = 2048 := by decide
  rw [hpow64, hpow11] at *
  rw [Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hq, Nat.div_div_eq_div_mul]
  have hmagic := magic_u64_div_10000 hm
  omega

private theorem bv_ult_9999999 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.ult 9999999#64 (BitVec.ofNat 64 m) = decide (9999999 < m) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ult, Nat.mod_eq_of_lt hm]

private theorem bv_inner_iter_k (bufBase : BitVec 64) {k' : Nat} (hk' : k' ≤ 4) :
    let x11 := -BitVec.ofNat 64 (16 - 4 * k')
    let x12 := bufBase - BitVec.ofNat 64 (18 - 4 * k')
    (20#64 + x11 - 4#64).ult 20#64 = true ∧
    (20#64 + x11 - 3#64).ult 20#64 = true ∧
    (20#64 + x11 - 2#64).ult 20#64 = true ∧
    (20#64 + x11 - 1#64).ult 20#64 = true ∧
    x12 + 20#64 + (-2#64) = bufBase + BitVec.ofNat 64 (4 * k') ∧
    x12 + 20#64 + (-1#64) = bufBase + BitVec.ofNat 64 (4 * k') + 1#64 ∧
    x12 + 20#64 = bufBase + BitVec.ofNat 64 (4 * k') + 2#64 ∧
    x12 + 20#64 + 1#64 = bufBase + BitVec.ofNat 64 (4 * k') + 3#64 ∧
    x11 - 4#64 = -BitVec.ofNat 64 (20 - 4 * k') ∧
    x12 - 4#64 = bufBase - BitVec.ofNat 64 (22 - 4 * k') ∧
    20#64 + (-BitVec.ofNat 64 (20 - 4 * k')) = BitVec.ofNat 64 (4 * k') := by
  rcases (by omega : k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 ∨ k' = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := { decide := true }) [bv_lin_norm]

private theorem u64FmtInner_div10000_iter_wp [CoreFmtPlacement] {lutAddr : BitVec 64}
    {tgt bufBase : BitVec 64} {k' m : Nat} {suffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk' : k' ≤ 4) (hm_lo : 1000 ≤ m) (hm64 : m < 2 ^ 64)
    (hpc : s.pc = coreFmtPl03.base + 0x48#64) (hrun : s.status = .Running)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = 20#64)
    (hx9  : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx11 : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (16 - 4 * k'))
    (hx12 : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (18 - 4 * k'))
    (hx13 : s.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64)
    (hx14 : s.readReg64 (.gpr 14#5) = 10000#64)
    (hx15 : s.readReg64 (.gpr 15#5) = 5243#64)
    (hx16 : s.readReg64 (.gpr 16#5) = 100#64)
    (hx17 : s.readReg64 (.gpr 17#5) = 9999999#64)
    (hx18 : s.readReg64 (.gpr 18#5) = BitVec.ofNat 64 m)
    (hnext : ∀ s' : State,
      s'.pc = (if 9999999 < m then coreFmtPl03.base + 0x48#64 else coreFmtPl03.base + 0xe0#64) →
      s'.status = .Running → s'.sp = s.sp →
      SysRegsEq s s' → CalleeSavedPreserved s s' →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 1#5) = bufBase →
      s'.readReg64 (.gpr 2#5) = 20#64 →
      s'.readReg64 (.gpr 9#5) = lutAddr →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (m / 10000) →
      s'.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (20 - 4 * k') →
      s'.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (22 - 4 * k') →
      s'.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64 →
      s'.readReg64 (.gpr 14#5) = 10000#64 →
      s'.readReg64 (.gpr 15#5) = 5243#64 →
      s'.readReg64 (.gpr 16#5) = 100#64 →
      s'.readReg64 (.gpr 17#5) = 9999999#64 →
      s'.readReg64 (.gpr 18#5) = BitVec.ofNat 64 (m / 10000) →
      SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (4 * k') ∗
          ((bufBase + BitVec.ofNat 64 (4 * k')) ↦ₛ (fourDecimalDigits (m % 10000) ++ suffix))) ∗ F)
        post oom) :
    SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * (k' + 1)) ∗
        ((bufBase + BitVec.ofNat 64 (4 * (k' + 1))) ↦ₛ suffix)) ∗ F)
      post oom := by
  have _ := hm_lo
  have hdiv := bv_div_10000 hm64
  have hrem := bv_msub32_rem m 10000 (by decide) (by omega)
  obtain ⟨hlsr2a, hlsr2b⟩ := bv_lsr2_32 (r := m % 10000) (by omega)
  obtain ⟨hdiv100a, humull, hdiv100b⟩ := bv_magic_div100_step (r := m % 10000) (by omega)
  have hrem100 := bv_msub32_rem (m % 10000) 100 (by decide) (by omega)
  obtain ⟨hd1_uxtw, _, _, _, _, _⟩ := bv_uxtw_lsl1 (d := (m % 10000) / 100) (by omega)
  obtain ⟨_, hd2_uxth, hd2_zext, hd2_and, _, hd2_lsl⟩ := bv_uxtw_lsl1 (d := (m % 10000) % 100) (by omega)
  obtain ⟨hcmp1, hcmp2, hcmp3, hcmp4, haddr0, haddr1, haddr2, haddr3, hx11_step, hx12_step, _⟩ :=
    bv_inner_iter_k bufBase hk'
  have hult9 := bv_ult_9999999 hm64
  have hpre_split : memRegion bufBase (4 * (k' + 1)) ⊢
      memRegion bufBase (4 * k') ∗
        ((∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k')) ↦₈ b0) ∗
         (∃∗ b1 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 1#64) ↦₈ b1) ∗
         (∃∗ b2 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 2#64) ↦₈ b2) ∗
         (∃∗ b3 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 3#64) ↦₈ b3)) := by
    rw [memRegion_split_le bufBase (4 * k') (4 * (k' + 1)) (by omega) (by omega),
        show 4 * (k' + 1) - 4 * k' = 4 by omega]
    exact sepConj_mono_right (memRegion4_entails8 (bufBase + BitVec.ofNat 64 (4 * k')))
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre_split))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro b0
  apply SepWP.exists_elim; intro b1
  apply SepWP.exists_elim; intro b2
  apply SepWP.exists_elim; intro b3
  conv =>
    arg 4; arg 1; arg 1
    rw [decDigitsLut_focus8_pair lutAddr (i := (m % 10000) / 100) (by omega)]
  iterate 23 wp_step
  conv =>
    arg 4; arg 1; arg 1
    rw [← decDigitsLut_focus8_pair lutAddr (i := (m % 10000) / 100) (by omega),
        decDigitsLut_focus8_pair lutAddr (i := (m % 10000) % 100) (by omega)]
  iterate 15 wp_step
  have hent_out :
      ((((lutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100))) ↦₈ᵣ
            decDigit8 (m % 10000 % 100 / 10) ∗
          (lutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100)) + 1#64) ↦₈ᵣ
            decDigit8 (m % 10000 % 100 % 10)) ∗
        (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * (m % 10000 % 100)) ∗
          (lutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100) + 2)) ↦ᵣ
            decDigitsLutBytes.drop (2 * (m % 10000 % 100) + 2))) ∗
      (memRegion bufBase (4 * k') ∗
        ((bufBase + BitVec.ofNat 64 (4 * k')) ↦₈ decDigit8 (m % 10000 / 100 / 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 1#64) ↦₈ decDigit8 (m % 10000 / 100 % 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 2#64) ↦₈ decDigit8 (m % 10000 % 100 / 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 3#64) ↦₈ decDigit8 (m % 10000 % 100 % 10))) ∗
      (bufBase + BitVec.ofNat 64 (4 * (k' + 1))) ↦ₛ suffix) ∗ F ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * k') ∗
        ((bufBase + BitVec.ofNat 64 (4 * k')) ↦ₛ (fourDecimalDigits (m % 10000) ++ suffix))) ∗ F) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus8_pair lutAddr (i := (m % 10000) % 100) (by omega)]
    refine sepConj_mono_right ?_
    rw [sepConj_assoc, pointsTo8_quad_eq_fourDecimalDigits,
        ← pointsToBytes_append_off bufBase (4 * k') (4 * (k' + 1)) _ _
          (by rw [fourDecimalDigits_length]; omega)]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx13])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx14])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx15])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx16])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx17])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm]))

private theorem u64FmtInner_div10000_loop_wp [CoreFmtPlacement] {lutAddr : BitVec 64}
    {tgt bufBase : BitVec 64} {k m : Nat} {suffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ 5) (hm_lo : 1000 ≤ m) (hm_pow : m < 10000 ^ k) (hm64 : m < 2 ^ 64)
    (hpc : s.pc = coreFmtPl03.base + 0x48#64) (hrun : s.status = .Running)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = 20#64)
    (hx9  : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx11 : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (20 - 4 * k))
    (hx12 : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (22 - 4 * k))
    (hx13 : s.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64)
    (hx14 : s.readReg64 (.gpr 14#5) = 10000#64)
    (hx15 : s.readReg64 (.gpr 15#5) = 5243#64)
    (hx16 : s.readReg64 (.gpr 16#5) = 100#64)
    (hx17 : s.readReg64 (.gpr 17#5) = 9999999#64)
    (hx18 : s.readReg64 (.gpr 18#5) = BitVec.ofNat 64 m)
    (hnext : ∀ (s' : State) (idx0 q : Nat) (outSuffix : List (BitVec 8)),
      s'.pc = coreFmtPl03.base + 0xe0#64 →
      s'.status = .Running → s'.sp = s.sp →
      SysRegsEq s s' → CalleeSavedPreserved s s' →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 1#5) = bufBase →
      s'.readReg64 (.gpr 2#5) = 20#64 →
      s'.readReg64 (.gpr 9#5) = lutAddr →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q →
      20#64 + s'.readReg64 (.gpr 11#5) = BitVec.ofNat 64 idx0 →
      idx0 ≤ 4 * (k - 1) →
      idx0 + outSuffix.length = 4 * k + suffix.length →
      q < 1000 →
      ((q = 0 ∧ outSuffix = formatDecimalNat m ++ suffix) ∨
       (1 ≤ q ∧ 4 ≤ idx0 ∧ formatDecimalNat q ++ outSuffix = formatDecimalNat m ++ suffix)) →
      SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗
          ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix)) ∗ F)
        post oom) :
    SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * k) ∗
        ((bufBase + BitVec.ofNat 64 (4 * k)) ↦ₛ suffix)) ∗ F)
      post oom := by
  induction k generalizing s m suffix with
  | zero => omega
  | succ k' ih =>
    have hx11' : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (16 - 4 * k') := by
      rw [hx11, show 20 - 4 * (k' + 1) = 16 - 4 * k' by omega]
    have hx12' : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (18 - 4 * k') := by
      rw [hx12, show 22 - 4 * (k' + 1) = 18 - 4 * k' by omega]
    refine u64FmtInner_div10000_iter_wp (by omega) hm_lo hm64 hpc hrun hx1 hx2 hx9 hx11' hx12'
      hx13 hx14 hx15 hx16 hx17 hx18 ?_
    intro s₁ hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11₁ hx12₁ hx13₁ hx14₁ hx15₁ hx16₁ hx17₁ hx18₁
    by_cases hhi : 9999999 < m
    · simp only [hhi, ↓reduceIte] at hpc₁
      have hk1 : 1 ≤ k' := by cases k' with | zero => simp at hm_pow; omega | succ _ => omega
      have hm_pow' : m / 10000 < 10000 ^ k' := by
        rw [Nat.pow_succ'] at hm_pow; exact Nat.div_lt_of_lt_mul hm_pow
      refine ih hk1 (by omega) (by omega) hm_pow' (by omega) hpc₁ hrun₁ hx1₁ hx2₁ hx9₁ hx11₁ hx12₁
        hx13₁ hx14₁ hx15₁ hx16₁ hx17₁ hx18₁ ?_
      intro s' idx0 q outSuffix hpc' hrun' hsp' haux' hcs' hx0' hx1' hx2' hx9' hx10' hx11'' hidx hlen hq hdisj
      have hfmt : formatDecimalNat (m / 10000) ++ (fourDecimalDigits (m % 10000) ++ suffix) =
          formatDecimalNat m ++ suffix := by
        rw [← List.append_assoc, ← formatDecimalNat_div_10000 (by omega)]
      exact hnext s' idx0 q outSuffix hpc' hrun' (hsp'.trans hsp₁)
        (SysRegsEq.trans haux₁ haux')
        (CalleeSavedPreserved.trans hcs₁ hcs') (hx0'.trans hx0₁) hx1' hx2' hx9'
        hx10' hx11'' (by omega)
        (by simp only [List.length_append, fourDecimalDigits_length] at hlen; omega) hq
        (hdisj.imp (fun ⟨hq0, ho⟩ => ⟨hq0, ho.trans hfmt⟩)
                   (fun ⟨hq1, hi4, ho⟩ => ⟨hq1, hi4, ho.trans hfmt⟩))
    · simp only [hhi, ↓reduceIte] at hpc₁
      have hx11_add : 20#64 + s₁.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (4 * k') := by
        rw [hx11₁]
        exact (bv_inner_iter_k bufBase (k' := k') (by omega)).2.2.2.2.2.2.2.2.2.2
      refine hnext s₁ (4 * k') (m / 10000) (fourDecimalDigits (m % 10000) ++ suffix)
        hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11_add
        (by omega) (by simp [fourDecimalDigits_length]; omega) (by omega) ?_
      by_cases h10k : m < 10000
      · left; refine ⟨by omega, ?_⟩
        rw [Nat.mod_eq_of_lt h10k, ← formatDecimalNat_of_1000_lt_10000 hm_lo h10k]
      · right
        have hk1 : 1 ≤ k' := by cases k' with | zero => simp at hm_pow; omega | succ _ => omega
        refine ⟨by omega, by omega, ?_⟩
        rw [← List.append_assoc, ← formatDecimalNat_div_10000 (by omega)]

private theorem bv_ubfiz_q1 {q1 : Nat} (hq1 : q1 < 10) :
    evalBitfield .W64 .UBFM 0#64 (BitVec.ofNat 64 q1) 63 3 = BitVec.ofNat 64 (2 * q1) ∧
    ((BitVec.ofNat 64 q1 &&& 15#64) <<< 1) = BitVec.ofNat 64 (2 * q1) ∧
    (BitVec.ofNat 64 q1 <<< 1) &&& 30#64 = BitVec.ofNat 64 (2 * q1) := by
  rcases (by omega : q1 = 0 ∨ q1 = 1 ∨ q1 = 2 ∨ q1 = 3 ∨ q1 = 4 ∨
    q1 = 5 ∨ q1 = 6 ∨ q1 = 7 ∨ q1 = 8 ∨ q1 = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem calleeSavedPreserved_write_fp {s0 s1 s2 : State} {fp : BitVec 64}
    (h01 : CalleeSavedPreserved s0 (s1.writeReg64 (.gpr 29#5) fp))
    (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 (s2.writeReg64 (.gpr 29#5) fp) := by
  simp (config := { decide := true }) only [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm] at h01 h12 ⊢
  exact ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem u64FmtInner_last_digit_wp [CoreFmtPlacement] {lutAddr : BitVec 64}
    {tgt ret_pc sp_frame savedFp bufBase v : BitVec 64} {idx1 q1 : Nat} {suf1 : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl03.base + 0x128#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_frame) (hsp_align : s.spAligned = true)
    (hx0  : s.readReg64 (.gpr 0#5) = v)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 idx1)
    (hx9  : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q1)
    (hq1_lt : q1 < 10) (hlen : idx1 + suf1.length = 20)
    (hcases : (v = 0#64 ∧ q1 = 0 ∧ idx1 = 20 ∧ suf1 = []) ∨
              (v ≠ 0#64 ∧ q1 = 0 ∧ suf1 = formatDecimalNat v.toNat) ∨
              (v ≠ 0#64 ∧ 1 ≤ q1 ∧ 1 ≤ idx1 ∧ decDigit8 q1 :: suf1 = formatDecimalNat v.toNat))
    (hnext : ∀ s' : State,
      s'.pc = ret_pc →
      s'.status = .Running → s'.sp = sp_frame + 16#64 →
      SysRegsEq s s' →
      CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) savedFp) s' →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
        post oom) :
    SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase idx1 ∗
        ((bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf1) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
      post oom := by
  subst hsp
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hv0, rfl, rfl⟩ | ⟨hv0, hq1_lo, hidx1_lo, hsuf⟩
  · have hpre : memRegion bufBase 20 ⊢
        memRegion bufBase 19 ∗ ∃∗ b0 : BitVec 8, (bufBase + 19#64) ↦₈ b0 := by
      rw [memRegion_split_le bufBase 19 20 (by decide) (by decide)]
      exact sepConj_mono_right (memRegion1_entails _)
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b0
    conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus8_odd lutAddr (i := 0) (by decide)]
    iterate 9 wp_step
    have hent :
        (((lutAddr + BitVec.ofNat 64 (2 * 0 + 1)) ↦₈ᵣ decDigit8 0 ∗
          (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * 0 + 1) ∗
            (lutAddr + BitVec.ofNat 64 (2 * 0 + 2)) ↦ᵣ
              decDigitsLutBytes.drop (2 * 0 + 2))) ∗
        (memRegion bufBase 19 ∗ (bufBase + 19#64) ↦₈ decDigit8 0) ∗
        (bufBase + BitVec.ofNat 64 20) ↦ₛ [] ∗
        (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat (0#64).toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat (0#64).toNat).length)) ↦ₛ
            formatDecimalNat (0#64).toNat) ∗
          (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
      apply sepConj_mono_left
      rw [← decDigitsLut_focus8_odd lutAddr (i := 0) (by decide)]
      refine sepConj_mono_right ?_
      have hf0 : formatDecimalNat (0#64).toNat = [decDigit8 0] := rfl
      rw [hf0, List.length_singleton, show 20 - 1 = 19 from rfl, sepConj_assoc,
          ← sepConj_assoc ((bufBase + 19#64) ↦₈ decDigit8 0),
          ← pointsToBytes_cons_off bufBase 19 (decDigit8 0) []]
      exact Entails.refl _
    exact SepWP.weaken_pre hent (hnext _ (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  · have hv_beq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
    iterate 5 wp_step
    have hidx_eq : idx1 = 20 - (formatDecimalNat v.toNat).length := by omega
    subst hidx_eq
    exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
  · have hv_beq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
    have hq1_ne : BitVec.ofNat 64 q1 ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt (by omega : q1 < 2 ^ 64)] at this; omega
    have hq1_beq : (BitVec.ofNat 64 q1 == 0#64) = false := beq_eq_false_iff_ne.mpr hq1_ne
    obtain ⟨hubfiz1, hubfiz2, hubfiz3⟩ := bv_ubfiz_q1 hq1_lt
    have hsub1 := bv_ofNat_sub_small hidx1_lo
    have hlut_off : (lutAddr + BitVec.ofNat 64 (2 * q1)) + 1#64 =
        lutAddr + BitVec.ofNat 64 (2 * q1 + 1) := by
      rw [BitVec.add_assoc, ← @BitVec.ofNat_add 64 (2 * q1) 1]
    have hpre : memRegion bufBase idx1 ⊢
        memRegion bufBase (idx1 - 1) ∗
          ∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ b0 := by
      rw [memRegion_split_le bufBase (idx1 - 1) idx1 (by omega) (by omega),
          show idx1 - (idx1 - 1) = 1 by omega]
      exact sepConj_mono_right (memRegion1_entails _)
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b0
    conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus8_odd lutAddr (i := q1) hq1_lt]
    iterate 10 wp_step
    have hidx_eq : idx1 - 1 = 20 - (formatDecimalNat v.toNat).length := by
      have := congrArg List.length hsuf; simp at this; omega
    have hent :
        (((lutAddr + BitVec.ofNat 64 (2 * q1 + 1)) ↦₈ᵣ decDigit8 q1 ∗
          (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * q1 + 1) ∗
            (lutAddr + BitVec.ofNat 64 (2 * q1 + 2)) ↦ᵣ
              decDigitsLutBytes.drop (2 * q1 + 2))) ∗
        (memRegion bufBase (idx1 - 1) ∗
          (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigit8 q1) ∗
        (bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf1 ∗
        (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
      apply sepConj_mono_left
      rw [← decDigitsLut_focus8_odd lutAddr (i := q1) hq1_lt]
      refine sepConj_mono_right ?_
      have hcons := pointsToBytes_cons_off bufBase (idx1 - 1) (decDigit8 q1) suf1
      rw [show (idx1 - 1) + 1 = idx1 by omega] at hcons
      rw [sepConj_assoc, ← sepConj_assoc ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigit8 q1),
          ← hcons, hsuf, ← hidx_eq]
      exact Entails.refl _
    exact SepWP.weaken_pre hent (hnext _ (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hidx_eq]))

private theorem u64FmtInner_two_digits_wp [CoreFmtPlacement] {lutAddr : BitVec 64}
    {tgt ret_pc sp_frame savedFp bufBase v : BitVec 64} {idx0 q : Nat} {outSuffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl03.base + 0xfc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_frame) (hsp_align : s.spAligned = true)
    (hx0  : s.readReg64 (.gpr 0#5) = v)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 idx0)
    (hx9  : s.readReg64 (.gpr 9#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q)
    (hv0 : v ≠ 0#64) (hq_lo : 10 ≤ q) (hq_lt : q < 1000)
    (hidx_lo : 4 ≤ idx0) (hlen : idx0 + outSuffix.length = 20)
    (hfmt : formatDecimalNat q ++ outSuffix = formatDecimalNat v.toNat)
    (hnext : ∀ s' : State,
      s'.pc = ret_pc →
      s'.status = .Running → s'.sp = sp_frame + 16#64 →
      SysRegsEq s s' →
      CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) savedFp) s' →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
        post oom) :
    SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase idx0 ∗
        ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
      post oom := by
  obtain ⟨hlsr2a, hlsr2b⟩ := bv_lsr2_32 (r := q) (by omega)
  obtain ⟨hdiv100a, humull, hdiv100b⟩ := bv_magic_div100_step (r := q) (by omega)
  have hrem100 := bv_msub32_rem q 100 (by decide) (by omega)
  obtain ⟨_, _, hd_zext, hd_and, _, hd_lsl⟩ := bv_uxtw_lsl1 (d := q % 100) (by omega)
  obtain ⟨_, _, hq100_zext, _, _, _⟩ := bv_uxtw_lsl1 (d := q / 100) (by omega)
  have hsub2 := bv_ofNat_sub_small (show 2 ≤ idx0 by omega)
  have hpre : memRegion bufBase idx0 ⊢
      memRegion bufBase (idx0 - 2) ∗
        ∃∗ w0 : BitVec 16, (bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆ w0 := by
    rw [memRegion_split_le bufBase (idx0 - 2) idx0 (by omega) (by omega),
        show idx0 - (idx0 - 2) = 2 by omega]
    exact sepConj_mono_right (memRegion2_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus16 lutAddr (i := q % 100) (by omega)]
  iterate 11 wp_step
  let suf1 := [decDigit8 (q % 100 / 10), decDigit8 (q % 100 % 10)] ++ outSuffix
  have hent :
      (((lutAddr + BitVec.ofNat 64 (2 * (q % 100))) ↦₁₆ᵣ
          pack16 (decDigit8 (q % 100 / 10)) (decDigit8 (q % 100 % 10)) ∗
        (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * (q % 100)) ∗
          (lutAddr + BitVec.ofNat 64 (2 * (q % 100) + 2)) ↦ᵣ
            decDigitsLutBytes.drop (2 * (q % 100) + 2))) ∗
      (memRegion bufBase (idx0 - 2) ∗
        (bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆
          pack16 (decDigit8 (q % 100 / 10)) (decDigit8 (q % 100 % 10))) ∗
      (bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix ∗
      (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (idx0 - 2) ∗
        ((bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦ₛ suf1) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus16 lutAddr (i := q % 100) (by omega)]
    refine sepConj_mono_right ?_
    unfold pack16 suf1
    rw [sepConj_assoc,
        ← sepConj_assoc ((bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆ _),
        ← pointsToBytes2_eq_pointsTo16,
        ← pointsToBytes_append_off bufBase (idx0 - 2) idx0 _ _ (by simp; omega)]
    exact Entails.refl _
  refine SepWP.weaken_pre hent (u64FmtInner_last_digit_wp (v := v) (idx1 := idx0 - 2) (q1 := q / 100)
    (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp)
    (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by omega) (by simp [suf1]; omega) ?_ ?_)
  · by_cases h100 : q < 100
    · right; left; refine ⟨hv0, by omega, ?_⟩
      rw [← hfmt, formatDecimalNat_two_digits hq_lo h100]; simp [suf1, Nat.mod_eq_of_lt h100]
    · right; right; refine ⟨hv0, by omega, by omega, ?_⟩
      rw [← hfmt, formatDecimalNat_three_digits (by omega) hq_lt]
      simp only [suf1, List.cons_append, List.nil_append]
      rw [show q % 100 / 10 = q / 10 % 10 by omega, show q % 100 % 10 = q % 10 by omega]
  · intro s' hpc' hrun' hsp' haux' hcs' hx0'
    refine hnext s' hpc' hrun' hsp'
      (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux')
      (CalleeSavedPreserved.trans
        (calleeSavedPreserved_write_fp (CalleeSavedPreserved.rfl _)
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
        hcs')
      hx0'

/-- `<u64>::_fmt_inner` (block `3`) writes the decimal digits of `v` right-aligned into the
20-byte buffer at `bufBase`, returning the start index `20 - len` in `x0`. -/
theorem u64FmtInner_wp [CoreFmtPlacement] {lutAddr tgt ret_pc bufBase v : BitVec 64}
    {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlut_rho : coreFmtPl03.ρ "rust_core_fmt:.rodata..Lanon.203" = lutAddr)
    (hpc : s0.pc = coreFmtPl03.base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hlr' : s0.readReg64 (.gpr 30#5) = ret_pc)
    (hx0' : s0.readReg64 (.gpr 0#5) = v)
    (hx1' : s0.readReg64 (.gpr 1#5) = bufBase)
    (hx2' : s0.readReg64 (.gpr 2#5) = 20#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      SysRegsEq s0 sf → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt sf
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          stackFrameAt s0.sp 0x10) ∗ F)
        post oom) :
    SepWP (coreFmtPC03.rebase coreFmtPl03.base (fun _ => none)) tgt s0
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        stackFrameAt s0.sp 0x10) ∗ F)
      post oom := by
  conv =>
    arg 4
    rw [← stackAt_eq_stackFrameAt s0.sp 16, stackAt_eq_cells s0.sp 2]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  iterate 2 (apply SepWP.exists_elim; intro _)
  iterate 3 wp_step
  refine coreFmtPC03_pairStep_0xc coreFmtPl03.base (fun _ => none) rfl
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  rw [hlut_rho]
  let sp_frame := s0.sp - 16#64
  let savedFp := s0.readReg64 (.gpr 29#5)
  have hpre_norm :
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        (((s0.sp - 16#64) ↦₆₄ savedFp) ∗ ((s0.sp - 8#64) ↦₆₄ ret_pc))) ∗ F) ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        ((bufBase + BitVec.ofNat 64 20) ↦ₛ []) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
    rw [pointsToBytes_nil]
    apply sepConj_mono_left
    refine sepConj_mono_right (sepConj_mono_right ?_)
    dsimp only [sp_frame]
    rw [emp_sepConj, show s0.sp - 16#64 + 8#64 = s0.sp - 8#64 by simp [bv_lin_norm]]
    exact Entails.refl _
  refine SepWP.weaken_pre hpre_norm ?_
  have hrepack :
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
        ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
          formatDecimalNat v.toNat) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
        ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
          formatDecimalNat v.toNat) ∗
        stackFrameAt s0.sp 0x10) ∗ F) := by
    apply sepConj_mono_left
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    dsimp only [sp_frame]
    rw [show s0.sp - 16#64 + 8#64 = s0.sp - 8#64 by simp [bv_lin_norm],
        ← stackAt_eq_stackFrameAt s0.sp 16, stackAt_eq_cells s0.sp 2]
    simp only [Nat.reduceMul]
    refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub]
    exact cells_one_entails _ _
  by_cases hlt1000 : v.toNat < 1000
  · have hv_ult : v.ult 1000#64 = true := by simp [BitVec.ult, hlt1000]
    by_cases hlt10 : v.toNat < 10
    · have hv_ult10 : v.ult 10#64 = true := by simp [BitVec.ult, hlt10]
      iterate 4 wp_step
      refine u64FmtInner_last_digit_wp (v := v) (idx1 := 20) (q1 := v.toNat) (suf1 := [])
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
        (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat])
        hlt10 rfl ?_ ?_
      · by_cases hv0 : v = 0#64
        · subst hv0; left; exact ⟨rfl, rfl, rfl, rfl⟩
        · right; right
          have hv_pos : 1 ≤ v.toNat := by
            cases h : v.toNat with
            | zero => exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv0
            | succ _ => omega
          exact ⟨hv0, hv_pos, by decide, (formatDecimalNat_of_lt_10 hlt10).symm⟩
      · intro s' hpc' hrun' hsp' haux' hcs' hx0'
        refine SepWP.weaken_pre hrepack (hnext s' hpc' hrun' ?_ ?_ ?_ hx0')
        · exact SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux'
        · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
        · exact CalleeSavedPreserved.trans
            (by dsimp only [savedFp]
                simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
            hcs'
    · have hv_ult10 : v.ult 10#64 = false := by
        apply Bool.eq_false_iff.mpr; simp [BitVec.ult]; omega
      have hv0 : v ≠ 0#64 := by rintro rfl; simp at hlt10
      iterate 4 wp_step
      refine u64FmtInner_two_digits_wp (v := v) (idx0 := 20) (q := v.toNat) (outSuffix := [])
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
        (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat])
        hv0 (by omega) hlt1000 (by decide) rfl (List.append_nil _) ?_
      intro s' hpc' hrun' hsp' haux' hcs' hx0'
      refine SepWP.weaken_pre hrepack (hnext s' hpc' hrun' ?_ ?_ ?_ hx0')
      · exact SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux'
      · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
      · exact CalleeSavedPreserved.trans
          (by dsimp only [savedFp]
              simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
          hcs'
  · have hv_ult : v.ult 1000#64 = false := by
      apply Bool.eq_false_iff.mpr; simp [BitVec.ult]; omega
    have hv0 : v ≠ 0#64 := by rintro rfl; simp at hlt1000
    iterate 13 wp_step
    rw [show (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase 20 ∗ ((bufBase + BitVec.ofNat 64 20) ↦ₛ []) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) =
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (4 * 5) ∗
          ((bufBase + BitVec.ofNat 64 (4 * 5)) ↦ₛ [])) ∗
         ((sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc) ∗ F)) by ac_rfl]
    refine u64FmtInner_div10000_loop_wp (k := 5) (m := v.toNat) (suffix := [])
      (by decide) (by decide) (by omega) (Nat.lt_trans v.isLt (by decide)) v.isLt
      (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat]) ?_
    intro s₁ idx0 q outSuffix hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11_add _ hlen₁ hq_lt hdisj
    rw [show (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗ ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix)) ∗
         ((sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc) ∗ F)) =
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗ ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) by ac_rfl]
    have hsp₁' : s₁.sp = sp_frame :=
      hsp₁.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
    have hsp_align₁ : s₁.spAligned = true := by
      unfold State.spAligned at *; rw [hsp₁']
      simpa (config := { decide := true }) [wp_norm, arm64_norm, sp_frame] using hsp_align
    have hx0₁' : s₁.readReg64 (.gpr 0#5) = v :=
      hx0₁.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
    have haux₁' : SysRegsEq s0 s₁ :=
      SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux₁
    have hcs₁' : CalleeSavedPreserved s0 (s₁.writeReg64 (.gpr 29#5) savedFp) :=
      calleeSavedPreserved_write_fp
        (by dsimp only [savedFp]
            simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        hcs₁
    by_cases hlt10 : q < 10
    · have hule10 : (10#64).ule (BitVec.ofNat 64 q) = false := by
        apply Bool.eq_false_iff.mpr; simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]; omega
      iterate 4 wp_step
      refine u64FmtInner_last_digit_wp (v := v) (idx1 := idx0) (q1 := q) (suf1 := outSuffix)
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun₁])
        (by simpa [wp_norm, arm64_norm] using hsp₁')
        (by unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align₁)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0₁'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10₁])
        hlt10 (by simpa using hlen₁) ?_ ?_
      · rcases hdisj with ⟨rfl, ho⟩ | ⟨hq1, hi4, ho⟩
        · right; left; rw [List.append_nil] at ho; exact ⟨hv0, rfl, ho⟩
        · right; right
          rw [formatDecimalNat_of_lt_10 hlt10, List.singleton_append, List.append_nil] at ho
          exact ⟨hv0, hq1, by omega, ho⟩
      · intro s' hpc' hrun' hsp' haux' hcs' hx0'
        refine SepWP.weaken_pre hrepack (hnext s' hpc' hrun' ?_ ?_ ?_ hx0')
        · exact haux₁'.trans (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux')
        · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
        · exact CalleeSavedPreserved.trans
            (calleeSavedPreserved_write_fp hcs₁'
              (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
            hcs'
    · have hule10 : (10#64).ule (BitVec.ofNat 64 q) = true := by
        simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]; omega
      rcases hdisj with ⟨rfl, _⟩ | ⟨_, hi4, hfmt⟩
      · omega
      rw [List.append_nil] at hfmt
      iterate 3 wp_step
      refine u64FmtInner_two_digits_wp (v := v) (idx0 := idx0) (q := q) (outSuffix := outSuffix)
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun₁])
        (by simpa [wp_norm, arm64_norm] using hsp₁')
        (by unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align₁)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0₁'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10₁])
        hv0 (by omega) hq_lt hi4 (by simpa using hlen₁) hfmt ?_
      intro s' hpc' hrun' hsp' haux' hcs' hx0'
      refine SepWP.weaken_pre hrepack (hnext s' hpc' hrun' ?_ ?_ ?_ hx0')
      · exact haux₁'.trans (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ haux')
      · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
      · exact CalleeSavedPreserved.trans
          (calleeSavedPreserved_write_fp hcs₁'
            (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
          hcs'

end VerifiedLibraries.RustStd.CoreFmt
