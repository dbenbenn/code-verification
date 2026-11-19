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
public import ProofLib.AsciiNum

/-!
# Shared Lemmas for Unsigned Integer Display Proofs

Lookup-table focusing lemmas (`DEC_DIGITS_LUT`), magic-multiplier base-10 division identities,
stack-frame and state-preservation helpers, and the generic `fmtArgCallSpec` callback lift
(`intDisplay_fmtArg_ok`) shared by unsigned integer `core::fmt::Display` proofs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd

/-! ## Lookup Table Focusing and Decimal Division Identities -/

abbrev decDigit8 (d : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (0x30 + d)

@[simp] theorem decDigitsLutBytes_length : decDigitsLutBytes.length = 200 := by
  decide

private theorem decDigitsLutBytes_fin_even :
    ∀ j : Fin 100, decDigitsLutBytes.getD (2 * j.val) 0#8 = decDigit8 (j.val / 10) := by
  decide

private theorem decDigitsLutBytes_fin_odd :
    ∀ j : Fin 100, decDigitsLutBytes.getD (2 * j.val + 1) 0#8 = decDigit8 (j.val % 10) := by
  decide

theorem decDigitsLutBytes_getD_even {i : Nat} (hi : i < 100) :
    decDigitsLutBytes.getD (2 * i) 0#8 = decDigit8 (i / 10) :=
  decDigitsLutBytes_fin_even ⟨i, hi⟩

theorem decDigitsLutBytes_getD_odd {i : Nat} (hi : i < 100) :
    decDigitsLutBytes.getD (2 * i + 1) 0#8 = decDigit8 (i % 10) :=
  decDigitsLutBytes_fin_odd ⟨i, hi⟩

theorem decDigitsLut_focus16 (lut : BitVec 64) {i : Nat} (hi : i < 100) :
    (lut ↦ᵣ decDigitsLutBytes) =
      ((lut + BitVec.ofNat 64 (2 * i)) ↦₁₆ᵣ
        pack16 (decDigit8 (i / 10)) (decDigit8 (i % 10))) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have hlen : 2 * i + 2 ≤ decDigitsLutBytes.length := by
    rw [decDigitsLutBytes_length]; omega
  have hsplit := pointsToBytesRO_split3 lut decDigitsLutBytes (2 * i) 2 hlen
  have h16 := pointsToBytesRO_take2_eq_pointsTo16RO (lut + BitVec.ofNat 64 (2 * i))
    decDigitsLutBytes (2 * i) hlen
  rw [decDigitsLutBytes_getD_even hi, decDigitsLutBytes_getD_odd hi] at h16
  rw [h16] at hsplit
  exact hsplit

theorem decDigitsLut_focus8_pair (lut : BitVec 64) {i : Nat} (hi : i < 100) :
    (lut ↦ᵣ decDigitsLutBytes) =
      (((lut + BitVec.ofNat 64 (2 * i)) ↦₈ᵣ decDigit8 (i / 10)) ∗
       ((lut + BitVec.ofNat 64 (2 * i) + 1#64) ↦₈ᵣ decDigit8 (i % 10))) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have h1 := pointsToBytesRO_append (lut + BitVec.ofNat 64 (2 * i))
    [decDigit8 (i / 10)] [decDigit8 (i % 10)]
  dsimp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at h1
  rw [decDigitsLut_focus16 lut hi]
  unfold pack16
  rw [← pointsToBytesRO2_eq_pointsTo16RO, h1, pointsToBytesRO_singleton, pointsToBytesRO_singleton]

theorem decDigitsLut_focus8_odd (lut : BitVec 64) {i : Nat} (hi : i < 10) :
    (lut ↦ᵣ decDigitsLutBytes) =
      ((lut + BitVec.ofNat 64 (2 * i + 1)) ↦₈ᵣ decDigit8 i) ∗
      ((lut ↦ᵣ decDigitsLutBytes.take (2 * i + 1)) ∗
        ((lut + BitVec.ofNat 64 (2 * i + 2)) ↦ᵣ decDigitsLutBytes.drop (2 * i + 2))) := by
  have hlen : (2 * i + 1) + 1 ≤ decDigitsLutBytes.length := by
    rw [decDigitsLutBytes_length]; omega
  have hsplit := pointsToBytesRO_split3 lut decDigitsLutBytes (2 * i + 1) 1 hlen
  have h8 := pointsToBytesRO_take1_eq_pointsTo8RO (lut + BitVec.ofNat 64 (2 * i + 1))
    decDigitsLutBytes (2 * i + 1) hlen
  rw [decDigitsLutBytes_getD_odd (by omega), show i % 10 = i by omega] at h8
  rw [h8] at hsplit
  exact hsplit

theorem magic_u8_div_100 {n : Nat} (hn : n < 256) :
    (n * 41) / 4096 = n / 100 := by
  omega

theorem magic_div_100 {m : Nat} (hm : m < 10000) :
    ((m / 4) * 5243) / 131072 = m / 100 := by
  omega

theorem magic_u32_div_10000 {m : Nat} (hm : m < 2 ^ 32) :
    (m * 3518437209) / 35184372088832 = m / 10000 := by
  omega

theorem magic_u64_div_10000 {m : Nat} (hm : m < 2 ^ 64) :
    (m * 3777893186295716171) / 37778931862957161709568 = m / 10000 := by
  omega

theorem formatDecimalNat_u8_cases {n : Nat} (hn : n < 256) :
    (1 ≤ (formatDecimalNat n).length ∧ (formatDecimalNat n).length ≤ 3) ∧
    (n < 10 → formatDecimalNat n = [decDigit8 n]) ∧
    (10 ≤ n → n < 100 → formatDecimalNat n = [decDigit8 (n / 10), decDigit8 (n % 10)]) ∧
    (100 ≤ n →
      formatDecimalNat n =
        [decDigit8 (n / 100), decDigit8 ((n % 100) / 10), decDigit8 ((n % 100) % 10)]) := by
  refine ⟨?_, fun h10 => formatDecimalNat_of_lt_10 h10,
    fun hlo hhi => formatDecimalNat_two_digits hlo hhi, fun hlo => ?_⟩
  · by_cases h1 : n < 10
    · rw [formatDecimalNat_of_lt_10 h1]; simp
    · by_cases h2 : n < 100
      · rw [formatDecimalNat_two_digits (by omega) h2]; simp
      · rw [formatDecimalNat_three_digits (by omega) (by omega)]; simp
  · rw [formatDecimalNat_three_digits hlo (by omega)]
    rw [show (n % 100) % 10 = n % 10 by omega]

theorem formatDecimalNat_u32_length_bounds {n : Nat} (hn : n < 2 ^ 32) :
    1 ≤ (formatDecimalNat n).length ∧ (formatDecimalNat n).length ≤ 10 := by
  by_cases h1 : n < 10
  · rw [formatDecimalNat_of_lt_10 h1]; simp
  · by_cases h2 : n < 100
    · rw [formatDecimalNat_two_digits (by omega) h2]; simp
    · by_cases h3 : n < 1000
      · rw [formatDecimalNat_three_digits (by omega) h3]; simp
      · by_cases h4 : n < 10000
        · rw [formatDecimalNat_of_1000_lt_10000 (by omega) h4]; simp
        · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
          by_cases h5 : n / 10000 < 10
          · rw [formatDecimalNat_of_lt_10 h5]; simp
          · by_cases h6 : n / 10000 < 100
            · rw [formatDecimalNat_two_digits (by omega) h6]; simp
            · by_cases h7 : n / 10000 < 1000
              · rw [formatDecimalNat_three_digits (by omega) h7]; simp
              · by_cases h8 : n / 10000 < 10000
                · rw [formatDecimalNat_of_1000_lt_10000 (by omega) h8]; simp
                · rw [formatDecimalNat_div_10000 (by omega), List.length_append,
                      fourDecimalDigits_length]
                  by_cases h9 : n / 10000 / 10000 < 10
                  · rw [formatDecimalNat_of_lt_10 h9]; simp
                  · rw [formatDecimalNat_two_digits (by omega) (by omega)]; simp

namespace IntDisplayAux

theorem memRegion1_entails (p : BitVec 64) :
    memRegion p 1 ⊢ ∃∗ b : BitVec 8, p ↦₈ b := by
  have h := memRegion_succ_off p 0 0 (by decide)
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  rw [h0, memRegion_zero, sepConj_emp] at h
  exact Entails.of_eq h

theorem pointsTo8_pair_eq_16 (p : BitVec 64) (b0 b1 : BitVec 8) :
    ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1)) = (p ↦₁₆ (b1 ++ b0)) := by
  have h := pointsToBytes_cons_off p 0 b0 [b1]
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have h1 : p + BitVec.ofNat 64 1 = p + 1#64 := rfl
  rw [h0, h1, pointsToBytes_singleton, pointsToBytes2_eq_pointsTo16] at h
  exact h.symm

theorem memRegion2_entails (p : BitVec 64) :
    memRegion p 2 ⊢ ∃∗ w : BitVec 16, p ↦₁₆ w := by
  have h2 := memRegion_succ_off p 0 1 (by decide)
  have h1 := memRegion_succ_off p 1 0 (by decide)
  have hp0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have hp1 : p + BitVec.ofNat 64 1 = p + 1#64 := rfl
  rw [hp1, memRegion_zero, sepConj_emp] at h1
  rw [hp0, hp1, h1, show (1 + 1 : Nat) = 2 from rfl] at h2
  rw [h2, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b0 => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b1 => ?_
  rw [pointsTo8_pair_eq_16]
  exact Entails.sepExists_intro (b1 ++ b0)

theorem memRegion4_entails8 (p : BitVec 64) :
    memRegion p 4 ⊢
      (∃∗ b0 : BitVec 8, p ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (p + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (p + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (p + 3#64) ↦₈ b3) := by
  rw [memRegion_split_le p 2 4 (by decide) (by decide),
      memRegion_split_le p 1 2 (by decide) (by decide),
      memRegion_split_le (p + 2#64) 1 2 (by decide) (by decide),
      show p + 2#64 + 1#64 = p + 3#64 by simp [bv_lin_norm],
      sepConj_assoc]
  exact sepConj_mono (memRegion1_entails p)
    (sepConj_mono (memRegion1_entails (p + 1#64))
      (sepConj_mono (memRegion1_entails (p + 2#64)) (memRegion1_entails (p + 3#64))))

theorem pointsTo16_pair_eq_fourDecimalDigits (p : BitVec 64) (r : Nat) :
    ((p ↦₁₆ pack16 (decDigit8 (r / 100 / 10)) (decDigit8 (r / 100 % 10))) ∗
     ((p + 2#64) ↦₁₆ pack16 (decDigit8 (r % 100 / 10)) (decDigit8 (r % 100 % 10)))) =
    (p ↦ₛ fourDecimalDigits r) := by
  unfold pack16 fourDecimalDigits decDigit8
  rw [← pointsToBytes2_eq_pointsTo16, ← pointsToBytes2_eq_pointsTo16]
  have happ := pointsToBytes_append p
    [BitVec.ofNat 8 (0x30 + r / 100 / 10), BitVec.ofNat 8 (0x30 + r / 100 % 10)]
    [BitVec.ofNat 8 (0x30 + r % 100 / 10), BitVec.ofNat 8 (0x30 + r % 100 % 10)]
  simpa only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] using happ.symm

theorem pointsTo8_quad_eq_fourDecimalDigits (p : BitVec 64) (r : Nat) :
    ((p ↦₈ decDigit8 (r / 100 / 10)) ∗
     ((p + 1#64) ↦₈ decDigit8 (r / 100 % 10)) ∗
     ((p + 2#64) ↦₈ decDigit8 (r % 100 / 10)) ∗
     ((p + 3#64) ↦₈ decDigit8 (r % 100 % 10))) =
    (p ↦ₛ fourDecimalDigits r) := by
  have h1 := pointsTo8_pair_eq_16 p (decDigit8 (r / 100 / 10)) (decDigit8 (r / 100 % 10))
  have h2 := pointsTo8_pair_eq_16 (p + 2#64) (decDigit8 (r % 100 / 10)) (decDigit8 (r % 100 % 10))
  rw [show p + 2#64 + 1#64 = p + 3#64 by simp [bv_lin_norm]] at h2
  rw [← sepConj_assoc, h1, h2]
  exact pointsTo16_pair_eq_fourDecimalDigits p r

theorem cells_one_entails (base : BitVec 64) (v : BitVec 64) :
    (base ↦₆₄ v) ⊢ ProofLib.cells base 1 := by
  rw [ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_intro v

theorem localFrame32_unpack (sp0 : BitVec 64) (pad bufLen : Nat) (hsum : pad + bufLen = 16) :
    stackFrameAt sp0 32 =
      stackFrameAt sp0 16 ∗ memRegion (sp0 - 32#64) pad ∗
        memRegion ((sp0 - 32#64) + BitVec.ofNat 64 pad) bufLen := by
  have hle : pad ≤ 16 := by omega
  have hdiff : 16 - pad = bufLen := by omega
  rw [show (32 : Nat) = 16 + 16 from rfl, stackFrameAt_split sp0 16 16 (by decide),
      stackFrameAt_eq_memRegion (sp0 - BitVec.ofNat 64 16) 16 (by decide),
      show sp0 - BitVec.ofNat 64 16 - BitVec.ofNat 64 16 = sp0 - 32#64 by simp [bv_lin_norm],
      memRegion_split_le (sp0 - 32#64) pad 16 hle (by decide), hdiff]

theorem stackFrameSlotsCont_drop_prefix (sp : BitVec 64) (k j : Nat) :
    ∀ (d : Nat) (R : SepProp) {m : Memory},
      (m ⊨ stackFrameSlotsCont sp k (j + 1 + d) (fun rest => rest ∗ R)) →
      ∃ R' : SepProp, m ⊨ stackFrameSlotsCont sp k (j + 1) (fun rest => rest ∗ R') := by
  intro d
  induction d with
  | zero => intro R m h; exact ⟨R, h⟩
  | succ d ih =>
    intro R m h
    rw [show j + 1 + (d + 1) = (j + d) + 2 by omega] at h
    dsimp only [stackFrameSlotsCont] at h
    rcases (satisfies_sepExists _ _).mp h with ⟨v, hv⟩
    have hfun : (fun rest => (((sp - BitVec.ofNat 64 ((k + (j + d) + 2) * 8)) ↦₆₄ v) ∗ rest) ∗ R) =
        (fun rest => rest ∗ (((sp - BitVec.ofNat 64 ((k + (j + d) + 2) * 8)) ↦₆₄ v) ∗ R)) := by
      funext rest
      rw [sepConj_comm ((sp - BitVec.ofNat 64 ((k + (j + d) + 2) * 8)) ↦₆₄ v) rest, sepConj_assoc]
    rw [show j + d + 1 = j + 1 + d by omega, hfun] at hv
    exact ih _ hv

theorem stackFrameSlotsCont_pull_right (sp : BitVec 64) (k : Nat) (R : SepProp) :
    ∀ (s : Nat) (cont : SepProp → SepProp),
      stackFrameSlotsCont sp k s cont ∗ R =
        stackFrameSlotsCont sp k s (fun rest => cont rest ∗ R) := by
  intro s
  induction s using Nat.strongRecOn generalizing R with
  | ind s ihs =>
    intro cont
    match s with
    | 0 => rfl
    | 1 => simp [stackFrameSlotsCont, sepExists_sepConj_left]
    | s' + 2 =>
      simp only [stackFrameSlotsCont, sepExists_sepConj_left]
      congr 1; funext v
      exact ihs (s' + 1) (by omega) R _

theorem stackFrameAt_lt_pow64_of_frozen {m : Memory} {sp a0 : BitVec 64} {n : Nat}
    {R : SepProp} (hfroz : (m.perm a0).frozen = true)
    (hm : m ⊨ stackFrameAt sp n ∗ R) : n < 2 ^ 64 := by
  refine Classical.byContradiction fun hge => ?_
  have hlen : 2 ^ 64 ≤ n := by omega
  have hex_mr : ∃ (b : BitVec 64) (len : Nat) (R' : SepProp),
      2 ^ 64 ≤ len ∧ (m ⊨ memRegion b len ∗ R') := by
    by_cases h8 : n % 8 = 0
    · have hn0 : n ≠ 0 := by omega
      have hsf_eq : stackFrameAt sp n = stackFrameSlotsFrom sp 0 (n / 8) := by
        unfold stackFrameAt; simp [hn0, h8]
      rw [hsf_eq, stackFrameSlotsFrom, stackFrameSlotsCont_pull_right] at hm
      have hd : n / 8 = (2 ^ 61 - 1) + 1 + (n / 8 - 2 ^ 61) := by omega
      rw [hd] at hm
      obtain ⟨R', hm'⟩ := stackFrameSlotsCont_drop_prefix sp 0 (2 ^ 61 - 1) (n / 8 - 2 ^ 61) R hm
      have h261 : (2 ^ 61 - 1) + 1 = 2 ^ 61 := by decide
      rw [h261, ← stackFrameSlotsCont_pull_right] at hm'
      have hsf264 : stackFrameSlotsFrom sp 0 (2 ^ 61) = memRegion (sp - BitVec.ofNat 64 (2 ^ 64)) (2 ^ 64) := by
        rw [← stackFrameAt_eq_memRegion sp (2 ^ 64) (Nat.le_refl _)]
        unfold stackFrameAt
        have hmod : (2 ^ 64) % 8 = 0 := by decide
        have hdiv : (2 ^ 64) / 8 = 2 ^ 61 := by decide
        simp [hmod, hdiv]
      rw [← stackFrameSlotsFrom, hsf264] at hm'
      exact ⟨sp - BitVec.ofNat 64 (2 ^ 64), 2 ^ 64, R', Nat.le_refl _, hm'⟩
    · have hn0 : n ≠ 0 := by omega
      have hsf_eq : stackFrameAt sp n = memRegion (sp - BitVec.ofNat 64 n) n := by
        unfold stackFrameAt; simp [hn0, h8]
      rw [hsf_eq] at hm
      exact ⟨sp - BitVec.ofNat 64 n, n, R, hlen, hm⟩
  obtain ⟨b, len, R', hlen', hmr⟩ := hex_mr
  have hall := Satisfies.allPerm_not_frozen_of_memRegion hmr
  have hi : (a0 - b).toNat < len := Nat.lt_of_lt_of_le (BitVec.isLt _) hlen'
  have hnf := (Memory.allPerm_iff m (fun p => !p.frozen) b len).mp hall (a0 - b).toNat hi
  have hadd : b + BitVec.ofNat 64 (a0 - b).toNat = a0 := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_arith
  rw [hadd, hfroz] at hnf
  exact Bool.noConfusion hnf

theorem localFrame32_repack (sp0 : BitVec 64) (pad bufLen : Nat) (hsum : pad + bufLen = 16)
    (fp lr : BitVec 64) (ds : List (BitVec 8)) (hhi : ds.length ≤ bufLen) :
    ((sp0 - 16#64) ↦₆₄ fp) ∗ ((sp0 - 8#64) ↦₆₄ lr) ∗
      memRegion (sp0 - 32#64) pad ∗
      memRegion ((sp0 - 32#64) + BitVec.ofNat 64 pad) (bufLen - ds.length) ∗
      (((sp0 - 32#64) + BitVec.ofNat 64 pad + BitVec.ofNat 64 (bufLen - ds.length)) ↦ₛ ds) ⊢
      stackFrameAt sp0 32 := by
  have h16 : ((sp0 - 16#64) ↦₆₄ fp) ∗ ((sp0 - 8#64) ↦₆₄ lr) ⊢ stackFrameAt sp0 16 := by
    rw [← stackAt_eq_stackFrameAt sp0 16, stackAt_eq_cells sp0 2]
    simp only [Nat.reduceMul]
    refine cells_sub_succ_entails 16 2 ?_; simp only [Nat.reduceSub]
    exact cells_one_entails (sp0 - 8#64) lr
  have hds : (((sp0 - 32#64) + BitVec.ofNat 64 pad + BitVec.ofNat 64 (bufLen - ds.length)) ↦ₛ ds) ⊢
      memRegion ((sp0 - 32#64) + BitVec.ofNat 64 pad + BitVec.ofNat 64 (bufLen - ds.length)) ds.length := by
    have h := pointsToBytes_memRegion_entails
      ((sp0 - 32#64) + BitVec.ofNat 64 pad + BitVec.ofNat 64 (bufLen - ds.length)) ds ds.length
      (Nat.le_refl _) (by omega)
    simpa [Nat.sub_self, memRegion_zero, sepConj_emp] using h
  rw [localFrame32_unpack sp0 pad bufLen hsum, ← sepConj_assoc]
  refine sepConj_mono h16 (Entails.trans (sepConj_mono_right (sepConj_mono_right hds)) ?_)
  have hm := memRegion_split_le ((sp0 - 32#64) + BitVec.ofNat 64 pad)
    (bufLen - ds.length) bufLen (by omega) (by omega)
  rw [show bufLen - (bufLen - ds.length) = ds.length by omega] at hm
  rw [← hm]
  exact Entails.refl _

theorem bv_ofNat_sub_small {n d : Nat} (hd : d ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 d = BitVec.ofNat 64 (n - d) := by
  conv => lhs; arg 1; rw [show n = (n - d) + d by omega]
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem bv_msub32_rem (x c : Nat) (hc : 0 < c) (hr : x % c < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 x) -
      BitVec.truncate 32 (BitVec.ofNat 64 (x / c)) * BitVec.ofNat 32 c) =
      BitVec.ofNat 64 (x % c) := by
  have hx : x = x % c + (x / c) * c := by have := Nat.div_add_mod' x c; omega
  have h32 : BitVec.truncate 32 (BitVec.ofNat 64 x) -
      BitVec.truncate 32 (BitVec.ofNat 64 (x / c)) * BitVec.ofNat 32 c = BitVec.ofNat 32 (x % c) := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    conv => lhs; arg 1; rw [hx]
    rw [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_sub_cancel]
  rw [h32]
  apply BitVec.eq_of_toNat_eq
  have _ := hc
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : x % c < 2 ^ 64)]

theorem bv_lsr2_32 {r : Nat} (hr : r < 10000) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 r))) >>> 2 =
      BitVec.ofNat 64 (r / 4) ∧
    (BitVec.ofNat 64 (r / 4) &&& 16383#64) = BitVec.ofNat 64 (r / 4) := by
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : r < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r < 2 ^ 32), Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 64)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 64)]
    have hm14 : (16383#64).toNat = 2 ^ 14 - 1 := rfl
    rw [hm14, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 14)]

theorem bv_magic_div100_step {r : Nat} (hr : r < 10000) :
    BitVec.truncate 32
      ((BitVec.zeroExtend 64 (0#32 + BitVec.truncate 32 (BitVec.ofNat 64 (r / 4)) * 5243#32)) >>> 17) =
      BitVec.ofNat 32 (r / 100) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (r / 100)) = BitVec.ofNat 64 (r / 100) ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 r) -
      BitVec.ofNat 32 (r / 100) * 100#32) = BitVec.ofNat 64 (r % 100) := by
  have hm := magic_div_100 hr
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (r / 4) * 5243 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (r / 4) * 5243 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 32)]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 64)]
  · have hrem := bv_msub32_rem r 100 (by decide) (by omega)
    have hq32 : BitVec.truncate 32 (BitVec.ofNat 64 (r / 100)) = BitVec.ofNat 32 (r / 100) := by
      rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rwa [hq32] at hrem

theorem bv_uxtw_lsl1 {d : Nat} (hd : d < 100) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 d))) <<< 1 = BitVec.ofNat 64 (2 * d) ∧
    (BitVec.zeroExtend 64 (BitVec.truncate 16 (BitVec.ofNat 64 d))) <<< 1 = BitVec.ofNat 64 (2 * d) ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 d)) = BitVec.ofNat 64 d ∧
    (BitVec.ofNat 64 d &&& 0xffff#64) = BitVec.ofNat 64 d ∧
    (BitVec.ofNat 64 d &&& 0xff#64) = BitVec.ofNat 64 d ∧
    (BitVec.ofNat 64 d) <<< 1 = BitVec.ofNat 64 (2 * d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 16), Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega
  · simp [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
    have hmask : (0xffff#64).toNat = 2 ^ 16 - 1 := rfl
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : d < 2 ^ 16)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
    have hmask : (0xff#64).toNat = 2 ^ 8 - 1 := rfl
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : d < 2 ^ 8)]
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega

theorem bv_ubfiz_digit {q1 : Nat} (hq1 : q1 < 10) :
    evalBitfield .W64 .UBFM 0#64 (BitVec.ofNat 64 q1) 63 3 = BitVec.ofNat 64 (2 * q1) ∧
    evalBitfield .W64 .UBFM 0#64 (BitVec.ofNat 64 q1) 63 6 = BitVec.ofNat 64 (2 * q1) ∧
    evalBitfield .W32 .UBFM 0#64 (BitVec.ofNat 64 q1) 31 3 = BitVec.ofNat 64 (2 * q1) ∧
    ((BitVec.ofNat 64 q1 &&& 15#64) <<< 1) = BitVec.ofNat 64 (2 * q1) ∧
    ((BitVec.ofNat 64 q1 &&& 127#64) <<< 1) = BitVec.ofNat 64 (2 * q1) ∧
    ((BitVec.ofNat 32 q1 &&& 15#32) <<< 1) = BitVec.ofNat 32 (2 * q1) ∧
    (BitVec.ofNat 64 q1 <<< 1) &&& 30#64 = BitVec.ofNat 64 (2 * q1) ∧
    (BitVec.ofNat 64 q1 <<< 1) &&& 254#64 = BitVec.ofNat 64 (2 * q1) ∧
    (BitVec.ofNat 32 q1 <<< 1) &&& 30#32 = BitVec.ofNat 32 (2 * q1) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (2 * q1)) = BitVec.ofNat 64 (2 * q1) := by
  rcases (by omega : q1 = 0 ∨ q1 = 1 ∨ q1 = 2 ∨ q1 = 3 ∨ q1 = 4 ∨
    q1 = 5 ∨ q1 = 6 ∨ q1 = 7 ∨ q1 = 8 ∨ q1 = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def SysRegsEq (s s' : State) : Prop :=
  s'.sigActions = s.sigActions ∧ s'.tpidrEl0 = s.tpidrEl0

theorem SysRegsEq.refl (s : State) : SysRegsEq s s := ⟨rfl, rfl⟩

theorem SysRegsEq.trans {s0 s1 s2 : State}
    (h01 : SysRegsEq s0 s1) (h12 : SysRegsEq s1 s2) : SysRegsEq s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.trans h01.2⟩

theorem intFmtWriteFrame_of_seg {s0 s' sm' sm : State}
    (h_in : SameCpuState s' s0) (h_out : SameCpuState sm sm')
    (hp : PureSegPreserved s0 sm)
    (hsys : SysRegsEq s' sm') :
    FmtWriteFrame s0 sm :=
  fmtWriteFrame_of_pureSeg hp
    (h_out.sigActions_eq.trans (hsys.1.trans h_in.sigActions_eq))
    (h_out.tpidrEl0_eq.trans (hsys.2.trans h_in.tpidrEl0_eq))

theorem frozen_of_codeLoaded {prog : Program} {m : Memory}
    (hcl : prog.CodeLoaded m) (hne : 0 < prog.code.length) :
    ∃ a : BitVec 64, (m.perm a).frozen = true := by
  obtain ⟨_, _, hbytes⟩ := Program.codeLoaded_iff.mp hcl
  exact ⟨prog.base + 0#64, by rw [(hbytes 0 hne).2.1]; rfl⟩

theorem calleeSaved_of_fp_saved {s0 s1 s2 s3 : State} {fp1 : BitVec 64}
    (h01 : CalleeSavedPreserved (s0.writeReg64 Reg.fp fp1) s1)
    (h12 : CalleeSavedPreserved s1 s2)
    (h23 : CalleeSavedPreserved (s2.writeReg64 Reg.fp (s0.readReg64 Reg.fp)) s3) :
    CalleeSavedPreserved s0 s3 := by
  have h02 := CalleeSavedPreserved.trans h01 h12
  simp (config := { decide := true }) only [CalleeSavedPreserved, Reg.fp, wp_norm, arm64_norm]
    at h02 h23 ⊢
  exact ⟨h23.1.trans h02.1, h23.2.1.trans h02.2.1, h23.2.2.1.trans h02.2.2.1,
    h23.2.2.2.1.trans h02.2.2.2.1, h23.2.2.2.2.1.trans h02.2.2.2.2.1,
    h23.2.2.2.2.2.1.trans h02.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h02.2.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.2.1.trans h02.2.2.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.2.2.1.trans h02.2.2.2.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.2.2.2.1.trans h02.2.2.2.2.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.2.2.2.2.1, h23.2.2.2.2.2.2.2.2.2.2.2.trans h02.2.2.2.2.2.2.2.2.2.2.2⟩

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hm'⟩ := hm
  rw [← sepConj_assoc] at hm'
  exact h x R hm' hL

theorem codeLoadedWhere_of_keepsFrozen {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mpl : MultiPlacement} {m m' : Memory}
    (hcl : lib.CodeLoadedWhere keep mpl m) (hkf : m.KeepsFrozen m') :
    lib.CodeLoadedWhere keep mpl m' :=
  fun k hk hkeep => (hcl k hk hkeep).of_keepsFrozen hkf

theorem sepWPp_call_keepsFrozen {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R')) :
    SepWPp prog target_pc s P Q Qp oom := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hsteps.keepsFrozen R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hex : ∃ R'', sm.mem ⊨ spec.onPanic x s sm ∗ R'' := ⟨F ∗ R', hpost⟩
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpanic sm hpan_st hex⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R' hoom_st hpost⟩)⟩

theorem fmtRef8_false (p : BitVec 64) (v : BitVec 8) : fmtRef8 false p v = (p ↦₈ v) := by
  simp only [fmtRef8, Bool.false_eq_true, ↓reduceIte]

theorem fmtRef8_true (p : BitVec 64) (v : BitVec 8) : fmtRef8 true p v = (p ↦₈ᵣ v) := by
  simp only [fmtRef8, ↓reduceIte]

theorem fmtRef32_false (p : BitVec 64) (v : BitVec 32) :
    fmtRef32 false p v = (p ↦₃₂ v) := by
  simp only [fmtRef32, Bool.false_eq_true, ↓reduceIte]

theorem fmtRef32_true (p : BitVec 64) (v : BitVec 32) :
    fmtRef32 true p v = (p ↦₃₂ᵣ v) := by
  simp only [fmtRef32, ↓reduceIte]
theorem stackFrame16_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 16 ⊢
      ∃∗ u29 : BitVec 64, ∃∗ u30 : BitVec 64,
        ((sp0 - 16#64) ↦₆₄ u29) ∗ ((sp0 - 8#64) ↦₆₄ u30) := by
  rw [← stackAt_eq_stackFrameAt sp0 16, stackAt_eq_cells sp0 2]
  simp only [Nat.reduceMul, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right,
    show (sp0 - 16#64) + 8#64 = sp0 - 8#64 by simp [bv_lin_norm]]
  exact Entails.refl _

theorem localFrame32_full_split (sp0 : BitVec 64) (stackBytes pad bufLen : Nat)
    (hsum : pad + bufLen = 16) (hlt : 192 + stackBytes < 2 ^ 64) :
    stackFrameAt sp0 (192 + stackBytes) ⊢
      ∃∗ u29 : BitVec 64, ∃∗ u30 : BitVec 64,
        (((sp0 - 16#64) ↦₆₄ u29) ∗ ((sp0 - 8#64) ↦₆₄ u30)) ∗
        memRegion (sp0 - 32#64) pad ∗
        memRegion ((sp0 - 32#64) + BitVec.ofNat 64 pad) bufLen ∗
        stackFrameAt (sp0 - 32#64) (160 + stackBytes) := by
  rw [show 192 + stackBytes = 32 + (160 + stackBytes) by omega,
      stackFrameAt_split sp0 32 (160 + stackBytes) (by omega),
      localFrame32_unpack sp0 pad bufLen hsum]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left (stackFrame16_unpack sp0))) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u29 => Entails.sepExists_right u29 ?_
  refine Entails.sepExists_elim fun u30 => Entails.sepExists_right u30 ?_
  sep_frame

theorem sameCpu_writeReg64 {a b : State} (h : SameCpuState a b)
    (r : Reg) (v : BitVec 64) :
    SameCpuState (a.writeReg64 r v) (b.writeReg64 r v) := by
  rcases h with ⟨hr, hv, hsp_e, hpc_e, hps_e, htp_e, hfp_e, hst_e, hsig_e⟩
  cases r with
  | gpr i => exact ⟨by simp [State.writeReg64, hr], hv, hsp_e, hpc_e, hps_e, htp_e, hfp_e, hst_e, hsig_e⟩
  | sp => exact ⟨hr, hv, rfl, hpc_e, hps_e, htp_e, hfp_e, hst_e, hsig_e⟩
  | xzr => exact ⟨hr, hv, hsp_e, hpc_e, hps_e, htp_e, hfp_e, hst_e, hsig_e⟩

/-! ## Callback Lift for Integer Display Contracts -/

private theorem fa_satisfies_of_eq {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

private theorem fa_entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem fa_ownsRW_formatterAt (f out vt : BitVec 64) (opts : FmtOptions) :
    OwnsRW (formatterAt f out vt opts) f := by
  unfold formatterAt
  exact ownsRW_sepConj_left (ownsRW_pointsTo64_at f out f (by simp [InRegion]))

private theorem fa_stackFrameSlotsCont_pull (sp : BitVec 64) (k m : Nat) :
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

private theorem fa_stackFrameSlotsFrom_succ_pos (sp : BitVec 64) {m : Nat} (hm : 0 < m) :
    stackFrameSlotsFrom sp 0 (m + 1) =
      (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 ((m + 1) * 8)) ↦₆₄ v) ∗
        stackFrameSlotsFrom sp 0 m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold stackFrameSlotsFrom
  simp only [stackFrameSlotsCont, Nat.zero_add]
  rw [funext fun v => fa_stackFrameSlotsCont_pull sp 0 (d + 1)
    ((sp - BitVec.ofNat 64 ((d + 2) * 8)) ↦₆₄ v) (fun P => P)]
  exact (sepExists_sepConj_left _ _).symm

private theorem fa_satisfies_drop_slotsFrom {m : Memory} {Q R : SepProp} (sp : BitVec 64)
    (extra : Nat) :
    (m ⊨ Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61 + extra) ∗ R)) →
    (m ⊨ Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61) ∗ R)) := by
  induction extra with
  | zero => exact id
  | succ extra ih =>
    intro h
    rw [show 2 ^ 61 + (extra + 1) = (2 ^ 61 + extra) + 1 by omega,
        fa_stackFrameSlotsFrom_succ_pos sp (by omega)] at h
    have h' : m ⊨ (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 (((2 ^ 61 + extra) + 1) * 8)) ↦₆₄ v) ∗
        (Q ∗ (stackFrameSlotsFrom sp 0 (2 ^ 61 + extra) ∗ R)) :=
      fa_satisfies_of_eq (by ac_rfl) h
    exact ih (Satisfies.drop_left h')

theorem le_pow64_of_formatterAt_stackFrameAt' {m : Memory}
    {f out vt sp : BitVec 64} {opts : FmtOptions} {n : Nat} {R : SepProp}
    (hm : m ⊨ formatterAt f out vt opts ∗ (stackFrameAt sp n ∗ R)) : n ≤ 2 ^ 64 := by
  apply Classical.byContradiction; intro hgt
  have hlt : 2 ^ 64 < n := Nat.lt_of_not_ge hgt
  have hne0 : (n == 0) = false := beq_false_of_ne (by omega)
  by_cases h8 : n % 8 = 0
  · rw [show stackFrameAt sp n = stackFrameSlotsFrom sp 0 (n / 8) by simp [stackFrameAt, hne0, h8],
        show n / 8 = 2 ^ 61 + (n / 8 - 2 ^ 61) by omega] at hm
    have hm64 := fa_satisfies_drop_slotsFrom sp (n / 8 - 2 ^ 61) hm
    have h64 : stackFrameSlotsFrom sp 0 (2 ^ 61) = memRegion (sp - BitVec.ofNat 64 (2 ^ 64)) (2 ^ 64) := by
      have heq := stackFrameAt_eq_memRegion sp (2 ^ 64) (by decide)
      simpa [stackFrameAt] using heq
    rw [h64] at hm64
    exact not_satisfies_ownsRW_ownsRW (fa_ownsRW_formatterAt f out vt opts)
      (ownsRW_sepConj_left (ownsRW_memRegion _ (2 ^ 64) f (BitVec.isLt _))) hm64
  · rw [show stackFrameAt sp n = memRegion (sp - BitVec.ofNat 64 n) n by
        simp [stackFrameAt, hne0, h8]] at hm
    exact not_satisfies_ownsRW_ownsRW (fa_ownsRW_formatterAt f out vt opts)
      (ownsRW_sepConj_left (ownsRW_memRegion _ n f (Nat.lt_trans (BitVec.isLt _) hlt))) hm

theorem formatterAt_entails_memRegion24' (f outPtr vtPtr : BitVec 64)
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

/-- Common shape of the unsigned integer `Display::fmt` contracts (`u8DisplayFmtSpec`,
    `u32DisplayFmtSpec`, `u64DisplayFmtSpec`): value reference `F_ref`, digit string `ds`,
    `frameBytes` bytes of stack. Each of those specs is definitionally an instance. -/
def intDisplayShapeSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (frameBytes : Nat)
    (lutAddr out vt : BitVec 64) (opts : FmtOptions) (valPtr : BitVec 64)
    (F_ref : SepProp) (ds : List (BitVec 8)) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ opts.flags.getLsbD 23 = false⌝ ∗
      F_ref ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
      formatterAt f out vt opts ∗ W st s ∗ stackFrameAt s.sp frameBytes
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true ds) st ok st'⌝ ∗
        F_ref ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
        (if ok then formatterAt f out vt opts else memRegion f 24) ∗
        W st' sf ∗ stackFrameAt s0.sp frameBytes
  onPanic := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true ds) st sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true ds) st sf⌝

/-- Lift an unsigned integer `Display::fmt` contract (`intDisplayShapeSpec`) to a
    `core::fmt::write` argument callback contract (`fmtArgCallSpec`) when `W` frames the value
    reference `F_ref` and the read-only `DEC_DIGITS_LUT` around `W_inner`, and
    `opts.flags.getLsbD 23 = false`. -/
theorem intDisplay_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {frameBytes argStackBytes idx : Nat}
    {lutAddr out vt valPtr fmtFn : BitVec 64} {opts : FmtOptions}
    {F_ref : SepProp} {ds : List (BitVec 8)}
    (hfmt : subroutine_ok P fmtFn
      (intDisplayShapeSpec W_inner StrStep CharStep Panic Oom frameBytes lutAddr out vt opts
        valPtr F_ref ds))
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st', FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true ds) st ok st' →
      Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf, FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true ds) st sf →
      PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf, FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true ds) st sf →
      OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : frameBytes ≤ argStackBytes)
    (hW : ∀ (st : σ) (s : State),
      W st s = F_ref ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗ W_inner st s) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) := by
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [fmtArgCallSpec] at hpre ⊢
  have harg_le : argStackBytes ≤ 2 ^ 64 :=
    le_pow64_of_formatterAt_stackFrameAt' (f := f) (out := out) (vt := vt) (sp := s0.sp)
      (opts := opts) (R := ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f⌝ ∗ W st s0 ∗ R)
      (fa_satisfies_of_eq (by ac_rfl) hpre)
  have hstk :
      stackFrameAt s0.sp argStackBytes =
        stackFrameAt s0.sp frameBytes ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 frameBytes) (argStackBytes - frameBytes) := by
    conv => lhs; rw [show argStackBytes = frameBytes + (argStackBytes - frameBytes) by omega]
    exact stackFrameAt_split s0.sp frameBytes (argStackBytes - frameBytes) (by omega)
  have hpre' :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((formatterAt f out vt opts ∗ W st s0 ∗ stackFrameAt s0.sp argStackBytes) ∗ R) :=
    fa_satisfies_of_eq (by ac_rfl) hpre
  rw [satisfies_pure_sepConj] at hpre'; rcases hpre' with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  let F_stk : SepProp := stackFrameAt (s0.sp - BitVec.ofNat 64 frameBytes) (argStackBytes - frameBytes)
  refine SepWPp.tailcall (x := (st, f)) (F := F_stk) hfmt hpc0 hrun0 hsp0 rfl
    (fun R' hm => ?_) (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ hm_pan => ?_) (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => ?_, hspf, hcs_sf⟩)
    (fun sf R' _ h_oom => ?_)
  · rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [intDisplayShapeSpec, F_stk]; rw [hW st s0, hstk]; conv => rhs; rw [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_0, hx1_0, hno_alt⟩ (fa_entails_of_eq (by ac_rfl))
  · dsimp only [intDisplayShapeSpec] at hm_pan
    refine Satisfies.mono (sepConj_mono_left ?_) hm_pan
    rw [sepConj_assoc]
    exact Entails.pure_left fun hp => Entails.pure_right (hpanic st sf hp) (entails_anyHeap _)
  · dsimp only [intDisplayShapeSpec, F_stk] at hm_post
    refine Satisfies.mono (sepConj_mono_left ?_) hm_post
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ok; apply Entails.sepExists_elim; intro st'
    refine Entails.sepExists_right ok (Entails.sepExists_right st' ?_)
    rw [sepConj_assoc]; apply Entails.pure_left; rintro ⟨hw0, hst⟩
    refine Entails.pure_right ⟨by rw [hw0]; cases ok <;> decide, hstep st ok st' hst⟩ ?_
    rw [hW st' sf, hstk]
    have hfm : (if ok then formatterAt f out vt opts else memRegion f 24) ⊢ memRegion f 24 := by
      cases ok
      · exact Entails.refl _
      · exact formatterAt_entails_memRegion24' f out vt opts
    refine Entails.trans (fa_entails_of_eq (show _ = (if ok then formatterAt f out vt opts
        else memRegion f 24) ∗
      ((F_ref ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗ W_inner st' sf) ∗
        (stackFrameAt s0.sp frameBytes ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 frameBytes) (argStackBytes - frameBytes))) by
        ac_rfl)) ?_
    exact sepConj_mono_left hfm
  · dsimp only [intDisplayShapeSpec] at h_oom
    rw [satisfies_pure_sepConj] at h_oom ⊢
    exact ⟨hoom st sf h_oom.1, Satisfies.drop_left h_oom.2⟩

end IntDisplayAux

end VerifiedLibraries.RustStd.CoreFmt
