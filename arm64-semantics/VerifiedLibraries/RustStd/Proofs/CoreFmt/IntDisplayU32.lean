/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayLemmas

/-!
# `<u32 as core::fmt::Display>::fmt` Proofs

Proves `u32DisplayFmt_of_padIntegral_ok` and `u32DisplayFmt_of_padIntegralWhere_ok` for
`coreFmtMultiLib` block `8`, conditional on a `formatterPadIntegralSpec` contract.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd
open IntDisplayAux

private theorem bv_u32_div_10000 {x : Nat} (hx : x < 2 ^ 32) :
    ((BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 x)) *
      3518437209#64) >>> 45) =
      BitVec.ofNat 64 (x / 10000) := by
  have hm := magic_u32_div_10000 hx
  have hx64 : x < 2 ^ 64 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by decide))
  have htr : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx64]
  have hprod : x * 3518437209 < 2 ^ 64 := by
    have : x * 3518437209 < 2 ^ 32 * 2 ^ 32 :=
      Nat.mul_lt_mul_of_lt_of_le hx (by decide) (by decide)
    rwa [← Nat.pow_add] at this
  rw [htr]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt (by decide : 3518437209 < 2 ^ 64),
    Nat.mod_eq_of_lt hprod, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 45 = 35184372088832 from rfl, hm,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx64)]

private theorem step_u32CallPad_bl [CoreFmtPlacement]
    {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl08.base + 0x11c#64) (hrun : s.status = .Running)
    (hnext : SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 30#5) (coreFmtPl08.base + 0x120#64)).setPC
        (coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym))
      Pre post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s Pre post oom := by
  have hf := coreFmtPC08_rebase_fetch_0x11c coreFmtPl08.base (fun _ => none)
  have hrho : coreFmtPl08.ρ "<core::fmt::Formatter>::pad_integral" =
      coreFmtMultiLib.resolve coreFmtMpl formatterPadIntegralSym := rfl
  exact SepWP.step_pure hpc hrun hf
    (by simp [wp_norm, arm64_norm, Reg.lr, hrho, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem step_u32Load_val [CoreFmtPlacement] (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32)
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = coreFmtPl08.base + 0xc#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = valPtr)
    (hnext : SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt
      ((s.writeReg64 (.gpr 9#5) (BitVec.ofNat 64 v.toNat)).setPC (coreFmtPl08.base + 0x10#64))
      (fmtRef32 ro valPtr v ∗ Fr) post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (fmtRef32 ro valPtr v ∗ Fr) post oom := by
  cases ro
  · rw [fmtRef32_false] at hnext ⊢
    wp_step
    simpa [hx0] using hnext
  · rw [fmtRef32_true] at hnext ⊢
    wp_step
    simpa [hx0] using hnext

private theorem u32Display_last_digit_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (idx1 q1 : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hidx1 : 1 ≤ idx1 ∧ idx1 ≤ 10) (hq1 : q1 < 10)
    (hpc : s.pc = coreFmtPl08.base + 0xe4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx1)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q1)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xfc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (idx1 - 1) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) (idx1 - 1) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (idx1 - 1)) ↦ₛ (decDigit8 q1 :: suf))) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx1 ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx1) ↦ₛ suf)) ∗ Fr)
      post oom := by
  let bufBase := (sp0 - 32#64) + 6#64
  obtain ⟨_, _, hubf32, _, _, hand15_32, _, _, hsh30_32, hzext2q⟩ := bv_ubfiz_digit hq1
  have htr11 : BitVec.truncate 32 (BitVec.ofNat 64 q1) = BitVec.ofNat 32 q1 := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hsub10 : BitVec.ofNat 64 idx1 - 1#64 = BitVec.ofNat 64 (idx1 - 1) := bv_ofNat_sub_small hidx1.1
  have hlut_off : lutAddr + BitVec.ofNat 64 (2 * q1) + 1#64 = lutAddr + BitVec.ofNat 64 (2 * q1 + 1) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  have hmr_split : memRegion bufBase idx1 ⊢
      memRegion bufBase (idx1 - 1) ∗ (∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ b0) := by
    rw [memRegion_split_le bufBase (idx1 - 1) idx1 (by omega) (by omega),
        show idx1 - (idx1 - 1) = 1 by omega]
    exact sepConj_mono_right (memRegion1_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hmr_split))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro b0
  conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus8_odd lutAddr (i := q1) hq1]
  have hand15 : (BitVec.ofNat 64 q1 &&& 15#64) <<< 1 = BitVec.ofNat 64 (2 * q1) :=
    (bv_ubfiz_digit hq1).2.2.2.1
  have hze32 : BitVec.zeroExtend 64 (BitVec.ofNat 32 q1) = BitVec.ofNat 64 q1 := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : q1 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : q1 < 2 ^ 64)]
  have htr2q : BitVec.truncate 32 (BitVec.ofNat 64 (2 * q1)) = BitVec.ofNat 32 (2 * q1) := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hlut_addr : lutAddr + BitVec.zeroExtend 64
      (BitVec.truncate 32 ((BitVec.zeroExtend 64 (BitVec.ofNat 32 q1) &&& 15#64) <<< 1)) + 1#64 =
      lutAddr + BitVec.ofNat 64 (2 * q1 + 1) := by
    rw [hze32, hand15, htr2q, hzext2q, hlut_off]
  have hbuf_addr : sp0 - 26#64 + BitVec.ofNat 64 (idx1 - 1) =
      bufBase + BitVec.ofNat 64 (idx1 - 1) := by
    dsimp only [bufBase]; simp [bv_lin_norm]
  iterate 6 wp_step
  have hent_out :
      ((((lutAddr + BitVec.ofNat 64 (2 * q1 + 1)) ↦₈ᵣ decDigit8 q1) ∗
        (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * q1 + 1) ∗
          (lutAddr + BitVec.ofNat 64 (2 * q1 + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * q1 + 2))) ∗
       (memRegion bufBase (idx1 - 1) ∗ ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigit8 q1)) ∗
       ((bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf)) ∗ Fr ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase (idx1 - 1) ∗
        ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦ₛ (decDigit8 q1 :: suf))) ∗ Fr) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus8_odd lutAddr (i := q1) hq1]
    refine sepConj_mono_right ?_; rw [sepConj_assoc]; refine sepConj_mono_right ?_
    rw [pointsToBytes_cons, show bufBase + BitVec.ofNat 64 (idx1 - 1) + 1#64 = bufBase + BitVec.ofNat 64 idx1 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add (idx1 - 1) 1, show idx1 - 1 + 1 = idx1 by omega]]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)

private theorem u32Display_two_digits_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (idx q : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hidx : 2 ≤ idx ∧ idx ≤ 10) (hq : 10 ≤ q ∧ q < 1000)
    (hpc : s.pc = coreFmtPl08.base + 0xac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xdc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 8#5) = lutAddr →
      s'.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (idx - 2) →
      s'.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (q / 100) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) (idx - 2) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (idx - 2)) ↦ₛ
            (decDigit8 ((q % 100) / 10) :: decDigit8 ((q % 100) % 10) :: suf))) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr)
      post oom := by
  let bufBase := (sp0 - 32#64) + 6#64
  obtain ⟨hlsr2, hand14⟩ := bv_lsr2_32 (r := q) (by omega)
  obtain ⟨hdiv_tr, hdiv_zext, hrem100⟩ := bv_magic_div100_step (r := q) (by omega)
  obtain ⟨_, _, hrem_zext, hrem_and16, _, hrem_lsl1⟩ := bv_uxtw_lsl1 (d := q % 100) (by omega)
  have hrem100' := bv_msub32_rem q 100 (by decide) (by omega)
  have haddr : sp0 - 26#64 + BitVec.ofNat 64 (idx - 2) = bufBase + BitVec.ofNat 64 (idx - 2) := by
    dsimp only [bufBase]; simp [bv_lin_norm]
  have hsub2 : BitVec.ofNat 64 idx - 2#64 = BitVec.ofNat 64 (idx - 2) := bv_ofNat_sub_small hidx.1
  have hmr_split : memRegion bufBase idx ⊢
      memRegion bufBase (idx - 2) ∗ (∃∗ u : BitVec 16, (bufBase + BitVec.ofNat 64 (idx - 2)) ↦₁₆ u) := by
    rw [memRegion_split_le bufBase (idx - 2) idx (by omega) (by omega),
        show idx - (idx - 2) = 2 by omega]
    exact sepConj_mono_right (memRegion2_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hmr_split))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u0
  conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus16 lutAddr (i := q % 100) (by omega)]
  iterate 12 wp_step
  have hent_out :
      ((((lutAddr + BitVec.ofNat 64 (2 * (q % 100))) ↦₁₆ᵣ
          pack16 (decDigit8 ((q % 100) / 10)) (decDigit8 ((q % 100) % 10))) ∗
        (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * (q % 100)) ∗
          (lutAddr + BitVec.ofNat 64 (2 * (q % 100) + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * (q % 100) + 2))) ∗
       (memRegion bufBase (idx - 2) ∗
         ((bufBase + BitVec.ofNat 64 (idx - 2)) ↦₁₆
           pack16 (decDigit8 ((q % 100) / 10)) (decDigit8 ((q % 100) % 10)))) ∗
       ((bufBase + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase (idx - 2) ∗
        ((bufBase + BitVec.ofNat 64 (idx - 2)) ↦ₛ
          (decDigit8 ((q % 100) / 10) :: decDigit8 ((q % 100) % 10) :: suf))) ∗ Fr) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus16 lutAddr (i := q % 100) (by omega)]
    refine sepConj_mono_right ?_; rw [sepConj_assoc]; refine sepConj_mono_right ?_
    unfold pack16
    rw [← pointsTo8_pair_eq_16, sepConj_assoc, pointsToBytes_cons, pointsToBytes_cons,
        show bufBase + BitVec.ofNat 64 (idx - 2) + 1#64 + 1#64 = bufBase + BitVec.ofNat 64 idx by
          rw [BitVec.add_assoc, BitVec.add_assoc, show (1#64 + 1#64 : BitVec 64) = 2#64 from rfl,
              ← BitVec.ofNat_add (idx - 2) 2, show idx - 2 + 2 = idx by omega],
        show bufBase + BitVec.ofNat 64 (idx - 2) + 1#64 =
          bufBase + BitVec.ofNat 64 (idx - 2) + 1#64 from rfl]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hdiv_zext])
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)

private theorem bv_ult32_9999999 {m : Nat} (hm : m < 2 ^ 32) :
    BitVec.ult (9999999#32) (BitVec.ofNat 32 m) = decide (9999999 < m) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ult, Nat.mod_eq_of_lt hm]

private theorem u32Display_div10000_iter_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (k m : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk : k ≤ 1) (hm : m < 2 ^ 32)
    (hpc : s.pc = coreFmtPl08.base + 0x48#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = -BitVec.ofNat 64 (4 * k))
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 m)
    (hx12 : s.readReg64 (.gpr 12#5) = 0xd1b71759#64)
    (hx13 : s.readReg64 (.gpr 13#5) = 10000#64)
    (hx14 : s.readReg64 (.gpr 14#5) = 5243#64)
    (hx15 : s.readReg64 (.gpr 15#5) = 100#64)
    (hx16 : s.readReg64 (.gpr 16#5) = (sp0 - 32#64) + 6#64)
    (hx17 : s.readReg64 (.gpr 17#5) = 9999999#64)
    (hnext : ∀ s' : State,
      s'.pc = (if 9999999 < m then coreFmtPl08.base + 0x48#64 else coreFmtPl08.base + 0x8c#64) →
      s'.status = .Running → s'.sp = sp0 - 32#64 →
      s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 8#5) = lutAddr →
      s'.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) →
      s'.readReg64 (.gpr 10#5) = -BitVec.ofNat 64 (4 * (k + 1)) →
      s'.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (m / 10000) →
      s'.readReg64 (.gpr 12#5) = 0xd1b71759#64 →
      s'.readReg64 (.gpr 13#5) = 10000#64 →
      s'.readReg64 (.gpr 14#5) = 5243#64 →
      s'.readReg64 (.gpr 15#5) = 100#64 →
      s'.readReg64 (.gpr 16#5) = (sp0 - 32#64) + 6#64 →
      s'.readReg64 (.gpr 17#5) = 9999999#64 →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 6#64) (6 - 4 * k) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (6 - 4 * k)) ↦ₛ
            (fourDecimalDigits (m % 10000) ++ suf))) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion ((sp0 - 32#64) + 6#64) (10 - 4 * k) ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (10 - 4 * k)) ↦ₛ suf)) ∗ Fr)
      post oom := by
  let bufBase := (sp0 - 32#64) + 6#64
  have hdiv := bv_u32_div_10000 hm
  have hrem := bv_msub32_rem m 10000 (by decide) (by omega)
  obtain ⟨hlsr2a, hlsr2b⟩ := bv_lsr2_32 (r := m % 10000) (by omega)
  obtain ⟨hdiv100a, hdiv100z, hdiv100b⟩ := bv_magic_div100_step (r := m % 10000) (by omega)
  obtain ⟨hd1_uxtw, _, _, _, _, hd1_lsl⟩ := bv_uxtw_lsl1 (d := (m % 10000) / 100) (by omega)
  obtain ⟨_, _, hd2_zext, hd2_and, _, hd2_lsl⟩ := bv_uxtw_lsl1 (d := (m % 10000) % 100) (by omega)
  have hult9 := bv_ult32_9999999 hm
  have htr100 : BitVec.truncate 32 (BitVec.ofNat 64 (m % 10000 / 100)) =
      BitVec.ofNat 32 (m % 10000 / 100) := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hlsr2c : BitVec.ofNat 64 (m % 10000) >>> 2 = BitVec.ofNat 64 (m % 10000 / 4) := by
    have h := hlsr2a
    rwa [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64),
      show BitVec.zeroExtend 64 (BitVec.ofNat 32 (m % 10000)) = BitVec.ofNat 64 (m % 10000) by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt (by omega : m % 10000 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : m % 10000 < 2 ^ 64)]] at h
  have hst1 : sp0 - 26#64 - BitVec.ofNat 64 (4 * k) + 6#64 =
      bufBase + BitVec.ofNat 64 (6 - 4 * k) := by
    dsimp only [bufBase]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [bv_lin_norm]
  have hst2 : sp0 - 26#64 - BitVec.ofNat 64 (4 * k) + 8#64 =
      bufBase + BitVec.ofNat 64 (6 - 4 * k) + 2#64 := by
    dsimp only [bufBase]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [bv_lin_norm]
  have hsplit : memRegion bufBase (10 - 4 * k) ⊢
      memRegion bufBase (6 - 4 * k) ∗
        ((∃∗ u : BitVec 16, (bufBase + BitVec.ofNat 64 (6 - 4 * k)) ↦₁₆ u) ∗
         (∃∗ u : BitVec 16, (bufBase + BitVec.ofNat 64 (6 - 4 * k) + 2#64) ↦₁₆ u)) := by
    rw [memRegion_split_le bufBase (6 - 4 * k) (10 - 4 * k) (by omega) (by omega),
        show 10 - 4 * k - (6 - 4 * k) = 2 + 2 by omega]
    refine sepConj_mono_right ?_
    rw [memRegion_split_le _ 2 (2 + 2) (by omega) (by omega), show 2 + 2 - 2 = 2 from rfl]
    exact sepConj_mono (memRegion2_entails _) (memRegion2_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hsplit))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u0
  apply SepWP.exists_elim; intro u1
  conv =>
    arg 4; arg 1; arg 1
    rw [decDigitsLut_focus16 lutAddr (i := (m % 10000) / 100) (by omega)]
  iterate 14 wp_step
  conv =>
    arg 4; arg 1; arg 1
    rw [← decDigitsLut_focus16 lutAddr (i := (m % 10000) / 100) (by omega),
        decDigitsLut_focus16 lutAddr (i := (m % 10000) % 100) (by omega)]
  iterate 3 wp_step
  have htrm : BitVec.truncate 32 (BitVec.ofNat 64 m) = BitVec.ofNat 32 m := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hx10' : -BitVec.ofNat 64 (4 * k) - 4#64 = -BitVec.ofNat 64 (4 * (k + 1)) := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [bv_lin_norm]
  have hent_out :
      ((((lutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100))) ↦₁₆ᵣ
            pack16 (decDigit8 (m % 10000 % 100 / 10)) (decDigit8 (m % 10000 % 100 % 10))) ∗
          (lutAddr ↦ᵣ decDigitsLutBytes.take (2 * (m % 10000 % 100)) ∗
            (lutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100) + 2)) ↦ᵣ
              decDigitsLutBytes.drop (2 * (m % 10000 % 100) + 2))) ∗
        (memRegion bufBase (6 - 4 * k) ∗
          ((bufBase + BitVec.ofNat 64 (6 - 4 * k)) ↦₁₆
              pack16 (decDigit8 (m % 10000 / 100 / 10)) (decDigit8 (m % 10000 / 100 % 10)) ∗
            (bufBase + BitVec.ofNat 64 (6 - 4 * k) + 2#64) ↦₁₆
              pack16 (decDigit8 (m % 10000 % 100 / 10)) (decDigit8 (m % 10000 % 100 % 10)))) ∗
        ((bufBase + BitVec.ofNat 64 (10 - 4 * k)) ↦ₛ suf)) ∗ Fr ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (6 - 4 * k) ∗
        ((bufBase + BitVec.ofNat 64 (6 - 4 * k)) ↦ₛ (fourDecimalDigits (m % 10000) ++ suf))) ∗ Fr) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus16 lutAddr (i := (m % 10000) % 100) (by omega)]
    refine sepConj_mono_right ?_
    rw [sepConj_assoc, pointsTo16_pair_eq_fourDecimalDigits,
        ← pointsToBytes_append_off bufBase (6 - 4 * k) (10 - 4 * k) _ _
          (by rw [fourDecimalDigits_length]; omega)]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, htrm, hult9])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10'])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx12])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx13])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx14])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx15])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx16])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx17])
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)

private theorem u32Display_tail_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (n q idx : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hn : n < 2 ^ 32) (hq : q < 10) (hidx : idx + suf.length = 10)
    (hfmt : (if q = 0 ∧ n ≠ 0 then suf else decDigit8 q :: suf) = formatDecimalNat n)
    (hpc : s.pc = coreFmtPl08.base + 0xdc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 n)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xfc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (10 - (formatDecimalNat n).length) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 6#64) (10 - (formatDecimalNat n).length) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (10 - (formatDecimalNat n).length)) ↦ₛ
            formatDecimalNat n)) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr)
      post oom := by
  have hlen := formatDecimalNat_u32_length_bounds hn
  have htr9 : BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have htr11 : BitVec.truncate 32 (BitVec.ofNat 64 q) = BitVec.ofNat 32 q := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hwrite : (formatDecimalNat n = decDigit8 q :: suf) → ∀ s1 : State,
      s1.pc = coreFmtPl08.base + 0xe4#64 → s1.status = .Running → s1.sp = sp0 - 32#64 →
      s1.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s1.readReg64 (.gpr 8#5) = lutAddr → s1.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx →
      s1.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q →
      CalleeSavedPreserved s s1 → SysRegsEq s s1 →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s1
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr)
        post oom := by
    intro hds s1 hpc1 hrun1 hsp1 hx1_1 hx8_1 hx10_1 hx11_1 hcs1 hsys1
    have hl : (formatDecimalNat n).length = suf.length + 1 := by rw [hds]; rfl
    refine u32Display_last_digit_wp lutAddr sp0 idx q suf ⟨by omega, by omega⟩ hq
      hpc1 hrun1 hsp1 hx8_1 hx10_1 hx11_1 ?_
    intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
    have hidx' : idx - 1 = 10 - (formatDecimalNat n).length := by omega
    rw [hidx'] at hx10' ⊢
    rw [← hds]
    exact hnext s' hpc' hrun' hsp' (hx1'.trans hx1_1) hx10'
      (CalleeSavedPreserved.trans hcs1 hcs') (SysRegsEq.trans hsys1 hsys')
  split at hfmt
  ·
    rename_i hcond
    obtain ⟨hq0, hn0⟩ := hcond
    subst hq0
    have hnez32 : BitVec.ofNat 32 n ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt hn] at this; omega
    have hidx' : idx = 10 - (formatDecimalNat n).length := by rw [← hfmt]; omega
    subst hidx'
    rw [← hfmt] at hnext ⊢
    iterate 2 wp_step
    exact hnext _
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10, hfmt])
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
  · rename_i hcond
    have hds := hfmt.symm
    by_cases hn0 : n = 0
    · subst hn0
      have hq0 : q = 0 := by
        have h := congrArg List.head? hds
        simp only [formatDecimalNat_zero, List.head?_cons, Option.some.injEq] at h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : 0x30 + q < 256)] at this; omega
      subst hq0
      wp_step
      exact hwrite hds _
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11])
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    · have hq0 : q ≠ 0 := fun h => hcond ⟨h, hn0⟩
      have hnez32 : BitVec.ofNat 32 n ≠ 0#32 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hn] at this; omega
      have hqz32 : BitVec.ofNat 32 q ≠ 0#32 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)] at this; omega
      have hnz64 : (BitVec.zeroExtend 64 (BitVec.ofNat 32 n) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hn] at this; omega
      have hqz64 : (BitVec.zeroExtend 64 (BitVec.ofNat 32 q) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)] at this; omega
      have hnz64' : ¬ BitVec.zeroExtend 64 (BitVec.ofNat 32 n) = 0#64 := by
        simpa using hnz64
      have hqz64' : ¬ BitVec.zeroExtend 64 (BitVec.ofNat 32 q) = 0#64 := by
        simpa using hqz64
      iterate 2 wp_step
      exact hwrite hds _
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11])
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩

private theorem bv_ult32_9 {q : Nat} (hq : q < 2 ^ 32) :
    BitVec.ult (9#32) (BitVec.ofNat 32 q) = decide (9 < q) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hq]

private theorem u32Display_finish_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (n q idx : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hn : n < 2 ^ 32) (hq : q < 1000) (hidx : idx + suf.length = 10)
    (hfmt : (if q = 0 ∧ n ≠ 0 then suf else formatDecimalNat q ++ suf) = formatDecimalNat n)
    (hpc : s.pc = coreFmtPl08.base + 0x90#64 ∨ s.pc = coreFmtPl08.base + 0xa4#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 n)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xfc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (10 - (formatDecimalNat n).length) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 6#64) (10 - (formatDecimalNat n).length) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (10 - (formatDecimalNat n).length)) ↦ₛ
            formatDecimalNat n)) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr)
      post oom := by
  have hlen := formatDecimalNat_u32_length_bounds hn
  have htr11 : BitVec.truncate 32 (BitVec.ofNat 64 q) = BitVec.ofNat 32 q := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hult9 := bv_ult32_9 (q := q) (by omega)
  have hule9 : BitVec.ule (BitVec.ofNat 32 q) (9#32) = decide (q ≤ 9) := by
    simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)]
  by_cases hq9 : q ≤ 9
  ·
    have hfmt' : (if q = 0 ∧ n ≠ 0 then suf else decDigit8 q :: suf) = formatDecimalNat n := by
      rw [← hfmt, formatDecimalNat_of_lt_10 (by omega)]; rfl
    have h9q : decide (9 < q) = false := by simp; omega
    rcases hpc with hpc | hpc
    · iterate 3 wp_step
      refine u32Display_tail_wp lutAddr sp0 n q idx suf hn (by omega) hidx hfmt'
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11]) ?_
      intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
      exact hnext s' hpc' hrun' hsp'
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx10'
        (CalleeSavedPreserved.trans
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
        (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')
    · iterate 2 wp_step
      refine u32Display_tail_wp lutAddr sp0 n q idx suf hn (by omega) hidx hfmt'
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11]) ?_
      intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
      exact hnext s' hpc' hrun' hsp'
        (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx10'
        (CalleeSavedPreserved.trans
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
        (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')
  ·
    have hq0 : q ≠ 0 := by omega
    have hfq : formatDecimalNat q ++ suf = formatDecimalNat n := by
      rw [← hfmt]; simp [hq0]
    have hdig : formatDecimalNat q =
        (if q / 100 = 0 then [] else [decDigit8 (q / 100)]) ++
          [decDigit8 ((q % 100) / 10), decDigit8 ((q % 100) % 10)] := by
      by_cases h100 : q < 100
      · rw [formatDecimalNat_two_digits (by omega) h100]
        simp [show q / 100 = 0 by omega, Nat.mod_eq_of_lt h100]
      · rw [formatDecimalNat_three_digits (by omega) hq]
        simp [show q / 100 ≠ 0 by omega, show q % 100 % 10 = q % 10 by omega]
    have hlenq : (formatDecimalNat q).length ≥ 2 := by rw [hdig]; split <;> simp
    have hlensum : (formatDecimalNat q).length + suf.length = (formatDecimalNat n).length := by
      rw [← hfq, List.length_append]
    have hfmt' : (if q / 100 = 0 ∧ n ≠ 0 then
          decDigit8 ((q % 100) / 10) :: decDigit8 ((q % 100) % 10) :: suf
        else decDigit8 (q / 100) ::
          decDigit8 ((q % 100) / 10) :: decDigit8 ((q % 100) % 10) :: suf) =
          formatDecimalNat n := by
      have hn0 : n ≠ 0 := by
        intro h; subst h; simp at hlensum; omega
      rw [← hfq, hdig]
      by_cases h100 : q / 100 = 0 <;> simp [h100, hn0]
    have h9q : decide (9 < q) = true := by simp; omega
    have htwo : ∀ s1 : State,
        s1.pc = coreFmtPl08.base + 0xac#64 → s1.status = .Running → s1.sp = sp0 - 32#64 →
        s1.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
        s1.readReg64 (.gpr 8#5) = lutAddr → s1.readReg64 (.gpr 9#5) = BitVec.ofNat 64 n →
        s1.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idx →
        s1.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q →
        CalleeSavedPreserved s s1 → SysRegsEq s s1 →
        SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s1
          (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) idx ∗
            (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 idx) ↦ₛ suf)) ∗ Fr)
          post oom := by
      intro s1 hpc1 hrun1 hsp1 hx1_1 hx8_1 hx9_1 hx10_1 hx11_1 hcs1 hsys1
      refine u32Display_two_digits_wp lutAddr sp0 idx q suf ⟨by omega, by omega⟩ ⟨by omega, hq⟩
        hpc1 hrun1 hsp1 hx8_1 hx10_1 hx11_1 ?_
      intro s2 hpc2 hrun2 hsp2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hcs2 hsys2
      refine u32Display_tail_wp lutAddr sp0 n (q / 100) (idx - 2) _ hn (by omega)
        (by simp; omega) hfmt' hpc2 hrun2 hsp2 hx8_2 (hx9_2.trans hx9_1) hx10_2 hx11_2 ?_
      intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
      exact hnext s' hpc' hrun' hsp' ((hx1'.trans hx1_2).trans hx1_1) hx10'
        (CalleeSavedPreserved.trans hcs1 (CalleeSavedPreserved.trans hcs2 hcs'))
        (SysRegsEq.trans hsys1 (SysRegsEq.trans hsys2 hsys'))
    rcases hpc with hpc | hpc
    · iterate 2 wp_step
      exact htwo _
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11])
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
    · iterate 2 wp_step
      exact htwo _
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11])
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩

private theorem u32Display_exit_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (k n q : Nat) (suf : List (BitVec 8))
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk : k ≤ 1) (hn : n < 2 ^ 32) (hq : q < 1000) (hsuf : suf.length = 4 + 4 * k)
    (hfmt : (if q = 0 ∧ n ≠ 0 then suf else formatDecimalNat q ++ suf) = formatDecimalNat n)
    (hpc : s.pc = coreFmtPl08.base + 0x8c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 n)
    (hx10 : s.readReg64 (.gpr 10#5) = -BitVec.ofNat 64 (4 * (k + 1)))
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 q)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xfc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (10 - (formatDecimalNat n).length) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 6#64) (10 - (formatDecimalNat n).length) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (10 - (formatDecimalNat n).length)) ↦ₛ
            formatDecimalNat n)) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) (6 - 4 * k) ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (6 - 4 * k)) ↦ₛ suf)) ∗ Fr)
      post oom := by
  have hx10e : -BitVec.ofNat 64 (4 * (k + 1)) + 10#64 = BitVec.ofNat 64 (6 - 4 * k) := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals decide
  wp_step
  refine u32Display_finish_wp lutAddr sp0 n q (6 - 4 * k) suf hn hq (by omega) hfmt
    (Or.inl (by simp [wp_norm, arm64_norm, bv_lin_norm])) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx11]) ?_
  intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
  exact hnext s' hpc' hrun' hsp'
    (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx10'
    (CalleeSavedPreserved.trans
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
    (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')

private theorem bv_ult32_1000 {v : Nat} (hv : v < 2 ^ 32) :
    BitVec.ult (BitVec.ofNat 32 v) (1000#32) = decide (v < 1000) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hv]

private theorem u32Display_digits_wp [CoreFmtPlacement]
    (lutAddr sp0 : BitVec 64) (v : Nat)
    {tgt : BitVec 64} {s : State} {Fr : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : v < 2 ^ 32)
    (hpc : s.pc = coreFmtPl08.base + 0x18#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64)
    (hx8 : s.readReg64 (.gpr 8#5) = lutAddr)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 v)
    (hnext : ∀ s' : State,
      s'.pc = coreFmtPl08.base + 0xfc#64 → s'.status = .Running →
      s'.sp = sp0 - 32#64 → s'.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (10 - (formatDecimalNat v).length) →
      CalleeSavedPreserved s s' → SysRegsEq s s' →
      SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s'
        (((lutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion ((sp0 - 32#64) + 6#64) (10 - (formatDecimalNat v).length) ∗
          (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 (10 - (formatDecimalNat v).length)) ↦ₛ
            formatDecimalNat v)) ∗ Fr)
        post oom) :
    SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) tgt s
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) 10) ∗ Fr)
      post oom := by
  have htr9 : BitVec.truncate 32 (BitVec.ofNat 64 v) = BitVec.ofNat 32 v := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
  have hzext9 : BitVec.zeroExtend 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
  have hult := bv_ult32_1000 hv
  have hpre_nil :
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) 10) ∗ Fr) ⊢
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion ((sp0 - 32#64) + 6#64) 10 ∗
        (((sp0 - 32#64) + 6#64 + BitVec.ofNat 64 10) ↦ₛ [])) ∗ Fr) := by
    rw [pointsToBytes_nil, sepConj_emp]; exact Entails.refl _
  refine SepWP.weaken_pre hpre_nil ?_
  by_cases hsmall : v < 1000
  · iterate 4 wp_step
    refine u32Display_finish_wp lutAddr sp0 v v 10 [] hv hsmall rfl (by simp)
      (Or.inr (by simp [wp_norm, arm64_norm, bv_lin_norm])) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
    intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
    exact hnext s' hpc' hrun' hsp'
      (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hx1') hx10'
      (CalleeSavedPreserved.trans
        (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs')
      (SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys')
  · iterate 12 wp_step
    refine u32Display_div10000_iter_wp lutAddr sp0 0 v [] (by decide) hv
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
    intro s1 hpc1 hrun1 hsp1 hx1_1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hx15_1
      hx16_1 hx17_1 hcs1 hsys1
    have hcs01 : CalleeSavedPreserved s s1 := CalleeSavedPreserved.trans
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]) hcs1
    have hsys01 : SysRegsEq s s1 :=
      SysRegsEq.trans ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩ hsys1
    have hx1_01 : s1.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) := by
      rw [hx1_1]; simp (config := { decide := true }) [wp_norm, arm64_norm]
    have hx9_01 : s1.readReg64 (.gpr 9#5) = BitVec.ofNat 64 v := by
      rw [hx9_1]; simp (config := { decide := true }) [wp_norm, arm64_norm, hx9]
    by_cases hbig : 9999999 < v
    · simp only [hbig, ↓reduceIte] at hpc1
      refine u32Display_div10000_iter_wp lutAddr sp0 1 (v / 10000)
        (fourDecimalDigits (v % 10000)) (by decide) (by omega)
        hpc1 hrun1 hsp1 hx8_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hx15_1 hx16_1 hx17_1 ?_
      intro s2 hpc2 hrun2 hsp2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 _ _ _ _ _ _ hcs2 hsys2
      simp only [show ¬ 9999999 < v / 10000 by omega, ↓reduceIte] at hpc2
      have hfmt : (if v / 10000 / 10000 = 0 ∧ v ≠ 0 then
            fourDecimalDigits (v / 10000 % 10000) ++ fourDecimalDigits (v % 10000)
          else formatDecimalNat (v / 10000 / 10000) ++
            (fourDecimalDigits (v / 10000 % 10000) ++ fourDecimalDigits (v % 10000))) =
          formatDecimalNat v := by
        rw [formatDecimalNat_div_10000 (by omega : 10000 ≤ v)]
        by_cases hq0 : v / 10000 / 10000 = 0
        · rw [formatDecimalNat_of_1000_lt_10000 (n := v / 10000) (by omega) (by omega)]
          have : v / 10000 % 10000 = v / 10000 := Nat.mod_eq_of_lt (by omega)
          simp [hq0, show v ≠ 0 by omega, this]
        · rw [formatDecimalNat_div_10000 (n := v / 10000) (by omega)]
          simp [hq0]
      refine u32Display_exit_wp lutAddr sp0 1 v (v / 10000 / 10000) _ (by decide) hv (by omega)
        (by simp) hfmt hpc2 hrun2 hsp2 hx8_2 (hx9_2.trans hx9_01) hx10_2 hx11_2 ?_
      intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
      exact hnext s' hpc' hrun' hsp' ((hx1'.trans hx1_2).trans hx1_01) hx10'
        (CalleeSavedPreserved.trans hcs01 (CalleeSavedPreserved.trans hcs2 hcs'))
        (SysRegsEq.trans hsys01 (SysRegsEq.trans hsys2 hsys'))
    · simp only [hbig, ↓reduceIte] at hpc1
      have hfmt : (if v / 10000 = 0 ∧ v ≠ 0 then fourDecimalDigits (v % 10000) ++ []
          else formatDecimalNat (v / 10000) ++ (fourDecimalDigits (v % 10000) ++ [])) =
          formatDecimalNat v := by
        by_cases hq0 : v / 10000 = 0
        · rw [formatDecimalNat_of_1000_lt_10000 (n := v) (by omega) (by omega)]
          simp [hq0, show v ≠ 0 by omega, Nat.mod_eq_of_lt (by omega : v < 10000)]
        · rw [formatDecimalNat_div_10000 (n := v) (by omega)]
          simp [hq0]
      refine u32Display_exit_wp lutAddr sp0 0 v (v / 10000) _ (by decide) hv (by omega)
        (by simp) hfmt hpc1 hrun1 hsp1 hx8_1 hx9_01 hx10_1 hx11_1 ?_
      intro s' hpc' hrun' hsp' hx1' hx10' hcs' hsys'
      exact hnext s' hpc' hrun' hsp' (hx1'.trans hx1_01) hx10'
        (CalleeSavedPreserved.trans hcs01 hcs')
        (SysRegsEq.trans hsys01 hsys')

private theorem u32DisplayFmt_gen_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    {keep padKeep : Nat → Bool}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hkeep8 : keep 8 = true)
    (hpad_sub : ∀ k, k < coreFmtMultiLib.blocks.length → padKeep k = true → keep k = true)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 8)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere keep mpl
        (u32DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  letI : CoreFmtPlacement := ⟨mpl, hpl⟩
  rw [fnAddr_u32Display hpl]
  apply subroutine_ok_of_sepWPp_init
  intro ⟨st, f⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, u32DisplayFmtSpec] at hpre
  rw [sepConj_assoc (⌜_⌝ ∗ _), satisfies_sepConj_pure_assoc] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hno_alt⟩, hpre⟩
  have hm0 : s0.mem ⊨ stackFrameAt s0.sp (192 + stackBytes) ∗
      (fmtRef32 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
       formatterAt f out vt opts ∗ W st s0 ∗ R) :=
    Satisfies.mono (by sep_frame) hpre
  obtain ⟨_, hfr⟩ := frozen_of_codeLoaded (hcl 8 (by decide) hkeep8)
    (by simp only [MultiPlacedLib.blockProgram, PlacedLib.program, Obj.CodeBlock.length_patched]; decide)
  have hstk_lt : 192 + stackBytes < 2 ^ 64 := stackFrameAt_lt_pow64_of_frozen hfr hm0
  have hm1 := Satisfies.mono (sepConj_mono_left (localFrame32_full_split s0.sp stackBytes 6 10 (by decide) hstk_lt)) hm0
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨u29, u30, hm1⟩
  let bufBase := (s0.sp - 32#64) + 6#64
  let ds := formatDecimalNat v.toNat
  have hds_bounds : 1 ≤ ds.length ∧ ds.length ≤ 10 := formatDecimalNat_u32_length_bounds v.isLt
  let idx := 10 - ds.length
  let dsPtr := bufBase + BitVec.ofNat 64 idx
  let P0 : SepProp :=
    (((s0.sp - 16#64) ↦₆₄ u29) ∗ ((s0.sp - 8#64) ↦₆₄ u30)) ∗
    fmtRef32 ro valPtr v ∗
    ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 10) ∗
    (formatterAt f out vt opts ∗ W st s0 ∗
     memRegion (s0.sp - 32#64) 6 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes))
  refine ⟨P0, Satisfies.mono (by dsimp only [P0, bufBase]; sep_frame) hm1, ?_⟩
  apply sepWPp_seg_lib_block_pureWhere (lib := coreFmtMultiLib) (keep := keep) (mpl := mpl)
    8 ⟨by decide, hkeep8⟩ hnoext coreFmtNoSvc0_08
    (mid := coreFmtMultiLib.resolve mpl formatterPadIntegralSym) hcl
  intro s' hcpu_in
  change SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) _ _ _ _
  have hpc' : s'.pc = coreFmtPl08.base := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  have hx0' : s'.readReg64 (.gpr 0#5) = valPtr := (hcpu_in.readReg64 .x0).trans hx0
  have hx1' : s'.readReg64 (.gpr 1#5) = f := (hcpu_in.readReg64 .x1).trans hx1
  have hfp' : s'.readReg64 (.gpr 29#5) = s0.readReg64 Reg.fp := hcpu_in.readReg64 Reg.fp
  have hlr' : s'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
  dsimp only [P0]
  iterate 3 wp_step
  refine SepWP.weaken_pre (by sep_frame :
    _ ⊢ fmtRef32 ro valPtr v ∗
      (((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 10) ∗
       (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        formatterAt f out vt opts ∗ W st s0 ∗
        memRegion (s0.sp - 32#64) 6 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes)))) ?_
  apply step_u32Load_val ro valPtr v
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
  apply coreFmtPC08_pairStep_0x10 coreFmtPl08.base (fun _ => none) rfl
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
  have hlut_rho : coreFmtPl08.ρ "rust_core_fmt:.rodata..Lanon.203" = lutAddr := by
    rw [hlut, resolve_decDigitsLut]; rfl
  refine SepWP.weaken_pre (by sep_frame :
    _ ⊢ ((lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 10) ∗
      (fmtRef32 ro valPtr v ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       formatterAt f out vt opts ∗ W st s0 ∗
       memRegion (s0.sp - 32#64) 6 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes))) ?_
  refine u32Display_digits_wp lutAddr s0.sp v.toNat v.isLt
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun'])
    (by simp [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hlut_rho])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm]) ?_
  intro sd hpcd hrund hspd hx1d hx10d hcsd hsysd
  have hx1d_eq : sd.readReg64 (.gpr 1#5) = f := by
    simpa (config := { decide := true }) [wp_norm, arm64_norm, hx1'] using hx1d
  have hspd_eq : sd.sp = s0.sp - 32#64 := hspd
  have hsub_len : 10#64 - BitVec.ofNat 64 (10 - (formatDecimalNat v.toNat).length) =
      BitVec.ofNat 64 ds.length :=
    (bv_ofNat_sub_small (by dsimp only [ds] at hds_bounds; omega)).trans
      (by dsimp only [ds] at hds_bounds ⊢; congr 1; omega)
  iterate 8 wp_step
  apply step_u32CallPad_bl
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
    (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗ fmtRef32 ro valPtr v ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    memRegion (s0.sp - 32#64) 6
  refine sepWPp_call_keepsFrozen (hPad f dsPtr ds) (x := st) (F := F_call)
    (ret_pc := coreFmtPl08.base + 0x120#64)
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
      (hcpu1.readReg64 .x4).trans (by simp (config := { decide := true }) [wp_norm, arm64_norm]; dsimp only [dsPtr, bufBase, idx, ds]; simp [bv_lin_norm])
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
         (fmtRef32 ro valPtr v ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗ formatterAt f out vt opts ∗
          memRegion (s0.sp - 32#64) 6 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes)) ∗ R')) ?_
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
      8 ⟨by decide, hkeep8⟩ hnoext coreFmtNoSvc0_08 (mid := s0.readReg64 Reg.lr) hcl2
    intro s2' hcpu2
    change SepWP (coreFmtPC08.rebase coreFmtPl08.base (fun _ => none)) _ _ _ _
    have hpc2' : s2'.pc = coreFmtPl08.base + 0x120#64 := hcpu2.pc_eq.trans hpc2
    have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun2
    have hsp2' : s2'.sp = s0.sp - 32#64 := hcpu2.sp_eq.trans (hsp2.trans hsp1)
    have hw0_2' : s2'.readReg32 .x0 = (if ok then 0#32 else 1#32) := (hcpu2.readReg32 .x0).trans hw0_2
    refine SepWP.weaken_pre (by dsimp only [F_call]; rw [hsp1]; sep_frame :
      _ ⊢ (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
        ((if ok then formatterAt f out vt opts else memRegion f 24) ∗
         (dsPtr ↦ₛ ds) ∗ W st' s2 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ∗
         (lutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase idx ∗
         fmtRef32 ro valPtr v ∗ memRegion (s0.sp - 32#64) 6)) ?_
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
    have hrepack32 := localFrame32_repack s0.sp 6 10 (by decide)
      (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr) ds hds_bounds.2
    have hstk_join : stackFrameAt s0.sp 32 ∗ stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ⊢
        stackFrameAt s0.sp (192 + stackBytes) := by
      rw [show 192 + stackBytes = 32 + (160 + stackBytes) by omega,
          stackFrameAt_split s0.sp 32 (160 + stackBytes) (by omega)]
      exact Entails.refl _
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, u32DisplayFmtSpec]
    refine Satisfies.mono ?_ hmf3
    refine Entails.sepExists_intro_frame ok ?_
    refine Entails.sepExists_intro_frame st' ?_
    rw [pure_sepConj_of_true ⟨hw0_3, hops⟩]
    apply sepConj_mono_left
    refine Entails.trans (by sep_frame :
      _ ⊢ (((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
           memRegion (s0.sp - 32#64) 6 ∗ memRegion bufBase idx ∗ (dsPtr ↦ₛ ds)) ∗
          stackFrameAt (s0.sp - 32#64) (160 + stackBytes) ∗ W st' s2 ∗
          (fmtRef32 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
           (if ok then formatterAt f out vt opts else memRegion f 24))) ?_
    refine Entails.trans (sepConj_mono hrepack32 (sepConj_mono_right (sepConj_mono_left (hW st' s2 s3 hfw23)))) ?_
    rw [← sepConj_assoc]
    refine Entails.trans (sepConj_mono_left hstk_join) ?_; sep_frame
  · intro sf R' _ hoom
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, formatterPadIntegralSpec, u32DisplayFmtSpec] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom ⊢
    exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩

theorem u32DisplayFmt_of_padIntegral_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 8)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u32DisplaySelfKeep mpl
        (u32DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) := by
  refine u32DisplayFmt_gen_ok (keep := u32DisplaySelfKeep) (padKeep := fun _ => false)
    hpl (by decide) (fun _ _ h => Bool.noConfusion h) hnoext hW stackBytes lutAddr out vt opts hlut ?_ ro valPtr v
  intro f dsPtr ds
  exact subroutine_ok_mono_entails (hPad f dsPtr ds)
    (fun _ _ => by dsimp only [MultiPlacedLib.withCodeLoadedWhere]; rw [sepConj_comm]; exact Entails.pure_left fun _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

theorem u32DisplayFmt_of_padIntegralWhere_ok {σ : Type} {P : Program} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl)
    (hnoext : LibBlockNoExtern coreFmtMultiLib mpl P 8)
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
    (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u32DisplayKeep mpl
        (u32DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v)) :=
  u32DisplayFmt_gen_ok hpl (by decide)
    (fun k _ h => by simp [u32DisplayKeep, h]) hnoext hW stackBytes lutAddr out vt opts hlut hPad ro valPtr v

end VerifiedLibraries.RustStd.CoreFmt
