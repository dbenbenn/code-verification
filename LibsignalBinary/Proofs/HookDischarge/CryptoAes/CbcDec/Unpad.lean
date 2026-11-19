/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon

/-!
# Shared PKCS#7 Unpadding (`CbcDec.Unpad`, `fnAddr + 0xd20#64 -> +0xd64#64 | +0xda8#64`)

Verifies the 17-instruction PKCS#7 unpadding block at `fnAddr + 0xd20#64` (`0x4c9e74..0x4c9eb4`)
together with the 4-instruction valid-padding slice check at `fnAddr + 0xd98#64` (`0x4c9eec..0x4c9ef8`),
delivering execution either to `bl drop_glue` on the bad-padding path (`fnAddr + 0xd64#64`) or
to `bl drop_glue` on the valid-padding path (`fnAddr + 0xda8#64`, with `x21 = ptLen`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Unpad

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open CryptoGames.CBC (pkcs7Unpad)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcUnpadWords cbcOkPreDropWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (pkcs7Unpad_of_bad_last pkcs7Unpad_of_mismatch pkcs7Unpad_of_all_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon (bv64_ofNat_sub_one)

private theorem lsl4_ofNat_eq (n : Nat) (hn : 16 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n) <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    show n * 2 ^ 4 = 16 * n from by omega, Nat.mod_eq_of_lt hn]

private theorem pointsToBytes_focus_at (addr : BitVec 64) (bs : List (BitVec 8))
    {j : Nat} (hj : j < bs.length) :
    (addr ↦ₛ bs) =
      (((addr + BitVec.ofNat 64 j) ↦₈ bs.getD j 0#8) ∗
        ((addr ↦ₛ bs.take j) ∗ ((addr + BitVec.ofNat 64 j + 1#64) ↦ₛ bs.drop (j + 1)))) := by
  have hdrop : bs.drop j = bs.getD j 0#8 :: bs.drop (j + 1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.drop_eq_getElem_cons hj
  rw [pointsToBytes_take_drop addr j bs (by omega), hdrop, pointsToBytes_cons]
  sep_ac_rfl

private theorem getD_drop_eq (bs : List (BitVec 8)) (off j : Nat) :
    (bs.drop off).getD j 0#8 = bs.getD (off + j) 0#8 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

@[local simp]
private theorem truncate32_setWidth64_byte (b : BitVec 8) :
    (b.setWidth 64).truncate 32 = b.setWidth 32 := by bv_bits

@[local simp]
private theorem truncate32_setWidth64_bv32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_bits

private theorem unpad_ule_iff (b : BitVec 8) :
    BitVec.ule (b.setWidth 32 - 17#32) (b.setWidth 32 - 17#32 + 16#32) =
      !decide (1 ≤ b.toNat ∧ b.toNat ≤ 16) := by
  revert b; decide

private theorem bv64_16_sub_byte {b : BitVec 8} (hhi : b.toNat ≤ 16) :
    16#64 - b.setWidth 64 = BitVec.ofNat 64 (16 - b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hb : (b.setWidth 64).toNat = b.toNat := BitVec.toNat_setWidth_of_le (by decide)
  rw [BitVec.toNat_sub_of_le (by change (b.setWidth 64).toNat ≤ 16; omega),
      hb, show (16#64 : BitVec 64).toNat = 16 from rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, decide_eq_true_eq,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem bv64_ofNat_add_one (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

/-- Inner PKCS#7 byte-verification loop (`fnAddr + 0xd48#64` → `+0xd64#64 | +0xda8#64`). -/
private theorem cbc_unpad_inner {P : Program} {fnAddr target_pc sp outBuf : BitVec 64}
    (hUnpad : hasInstrs P (fnAddr + 0xd20#64) (decodeWords cbcUnpadWords))
    (hOkPre : hasInstrs P (fnAddr + 0xd98#64) (decodeWords cbcOkPreDropWords))
    (rawBs : List (BitVec 8)) (numBlocks : Nat) (Other : SepProp) (s0 : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen : rawBs.length = 16 * numBlocks) (hpos : 0 < numBlocks)
    (hlt40 : 16 * numBlocks < 2 ^ 40)
    (hlo : 1 ≤ (rawBs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat)
    (hhi : (rawBs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ 16) :
    let lastOff := 16 * (numBlocks - 1)
    let lb := rawBs.drop lastOff
    let lastBlkPtr := outBuf + BitVec.ofNat 64 lastOff
    let last := rawBs.getD (lastOff + 15) 0#8
    ∀ (k j : Nat) (s : State),
      j + k = 15 →
      16 - last.toNat ≤ j →
      (∀ i, 16 - last.toNat ≤ i → i < j → rawBs.getD (lastOff + i) 0#8 = last) →
      s.pc = fnAddr + 0xd48#64 → s.status = .Running → s.sp = sp →
      s.readReg64 .x8 = BitVec.ofNat 64 (numBlocks - 1) →
      s.readReg64 .x9 = lastBlkPtr →
      s.readReg64 .x10 = last.setWidth 64 →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 - last.toNat) →
      s.readReg64 .x12 = BitVec.ofNat 64 j →
      s.readReg64 .x23 = BitVec.ofNat 64 (16 * numBlocks) →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sf : State,
        sf.status = .Running → sf.sp = sp →
        sf.readReg64 .x0 = sp + 0xb40#64 →
        sf.readReg64 .x23 = BitVec.ofNat 64 (16 * numBlocks) →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        PureStepPreserved s sf →
        ((∃ ptLen : Nat,
            ptLen < 16 * numBlocks ∧
            pkcs7Unpad rawBs = some (rawBs.take ptLen) ∧
            sf.pc = fnAddr + 0xda8#64 ∧
            sf.readReg64 .x21 = BitVec.ofNat 64 ptLen) ∨
          (pkcs7Unpad rawBs = none ∧ sf.pc = fnAddr + 0xd64#64)) →
        SepWP P target_pc sf ((lastBlkPtr ↦ₛ lb) ∗ Other) post oom) →
      SepWP P target_pc s ((lastBlkPtr ↦ₛ lb) ∗ Other) post oom := by
  intro lastOff lb lastBlkPtr last k
  have hlb_len : lb.length = 16 := by dsimp only [lb, lastOff]; rw [List.length_drop, hlen]; omega
  induction k with
  | zero =>
    intro j s hjk _ hall hpc hrun hsp hx8 hx9 hx10 hx11 hx12 hx23 hv hnext
    have hj15 : j = 15 := by omega
    subst hj15
    simp only [arm64_norm] at hx8 hx9 hx10 hx11 hx12 hx23
    have_instrs hUnpad 10 2
    have_instrs hOkPre 0 4
    wp_steps 2
    have hpt_eq : BitVec.ofNat 64 (16 - last.toNat) +
        (BitVec.ofNat 64 (numBlocks - 1)) <<< 4 =
        BitVec.ofNat 64 (16 * numBlocks - last.toNat) := by
      rw [lsl4_ofNat_eq (numBlocks - 1) (by omega), ← BitVec.ofNat_add,
          show (16 - last.toNat) + 16 * (numBlocks - 1) = 16 * numBlocks - last.toNat
            from by dsimp only [last, lastOff] at *; omega]
    have hult_f : BitVec.ult (BitVec.ofNat 64 (16 * numBlocks))
        (BitVec.ofNat 64 (16 * numBlocks - last.toNat)) = false := by
      rw [bv64_ult_ofNat (by omega) (by omega), decide_eq_false_iff_not]
      dsimp only [last, lastOff] at *; omega
    wp_steps 4
    have hpk : pkcs7Unpad rawBs = some (rawBs.take (16 * numBlocks - last.toNat)) :=
      pkcs7Unpad_of_all_eq hlen hpos hlo hhi hall
    exact hnext _
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx23])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
      (PureStepPreserved.of_proj_perm rfl (by simp [wp_norm, arm64_norm]))
      (Or.inl ⟨16 * numBlocks - last.toNat,
        by dsimp only [last, lastOff] at *; omega, hpk,
        by simp [wp_norm, arm64_norm]; try bv_lin,
        by simp [wp_norm, arm64_norm]⟩)
  | succ k ih =>
    intro j s hjk hjlo hall hpc hrun hsp hx8 hx9 hx10 hx11 hx12 hx23 hv hnext
    simp only [arm64_norm] at hx8 hx9 hx10 hx11 hx12 hx23
    have hj_lt15 : j < 15 := by omega
    have hj_lt16 : j < lb.length := by omega
    have hj_ne15 : (BitVec.ofNat 64 j == 15#64) = false := by
      apply beq_false_of_ne; intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at ht
      change j = 15 at ht; omega
    have_instrs hUnpad 10 7
    wp_steps 2
    rw [pointsToBytes_focus_at lastBlkPtr lb hj_lt16, sepConj_assoc]
    wp_steps 4
    rw [← sepConj_assoc, ← pointsToBytes_focus_at lastBlkPtr lb hj_lt16]
    have hget_eq : lb.getD j 0#8 = rawBs.getD (lastOff + j) 0#8 := getD_drop_eq rawBs lastOff j
    wp_if hbyte_eq
    · have hb_eq : rawBs.getD (lastOff + j) 0#8 = last := by
        rw [← hget_eq]; simpa using congrArg (BitVec.truncate 8) hbyte_eq
      refine ih (j + 1) _ (by omega) (by omega)
        (fun i hi1 hi2 => by
          by_cases hij : i = j
          · subst hij; exact hb_eq
          · exact hall i hi1 (by omega))
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hx9])
        (by simp [wp_norm, arm64_norm, hx10])
        (by simp [wp_norm, arm64_norm, hx11])
        (by simp [wp_norm, arm64_norm, bv64_ofNat_add_one j])
        (by simp [wp_norm, arm64_norm, hx23])
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        fun sf hrun_f hsp_f hx0_f hx23_f hv_f hpure_f hout_f =>
          hnext sf hrun_f hsp_f hx0_f hx23_f hv_f
            (PureStepPreserved.trans
              (PureStepPreserved.of_proj_perm rfl (by simp [wp_norm, arm64_norm])) hpure_f)
            hout_f
    · have hb_ne : rawBs.getD (lastOff + j) 0#8 ≠ last := by
        intro heq; apply hbyte_eq; rw [hget_eq, heq]
      wp_step
      have hpk : pkcs7Unpad rawBs = none :=
        pkcs7Unpad_of_mismatch hlen hpos hlo hhi hjlo hj_lt15 hb_ne
      exact hnext _
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx23])
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        (PureStepPreserved.of_proj_perm rfl (by simp [wp_norm, arm64_norm]))
        (Or.inr ⟨hpk, by simp [wp_norm, arm64_norm]; try bv_lin⟩)

/-- Complete PKCS#7 unpadding from the shared join point `fnAddr + 0xd20#64` (`0x4c9e74`) to
    either `bl drop_glue` at `fnAddr + 0xda8#64` (valid padding, `x21 = ptLen`) or
    `bl drop_glue` at `fnAddr + 0xd64#64` (invalid padding). -/
theorem cbc_unpad {P : Program} {fnAddr target_pc sp outBuf : BitVec 64}
    (hUnpad : hasInstrs P (fnAddr + 0xd20#64) (decodeWords cbcUnpadWords))
    (hOkPre : hasInstrs P (fnAddr + 0xd98#64) (decodeWords cbcOkPreDropWords))
    (rawBs : List (BitVec 8)) (numBlocks : Nat) (Rest : SepProp) (s0 s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen : rawBs.length = 16 * numBlocks) (hpos : 0 < numBlocks)
    (hlt40 : 16 * numBlocks < 2 ^ 40)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0xd20#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (16 * numBlocks))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 numBlocks)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State,
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 0xb40#64 →
      sf.readReg64 .x23 = BitVec.ofNat 64 (16 * numBlocks) →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      PureStepPreserved s sf →
      ((∃ ptLen : Nat,
          ptLen < 16 * numBlocks ∧
          pkcs7Unpad rawBs = some (rawBs.take ptLen) ∧
          sf.pc = fnAddr + 0xda8#64 ∧
          sf.readReg64 .x21 = BitVec.ofNat 64 ptLen) ∨
        (pkcs7Unpad rawBs = none ∧ sf.pc = fnAddr + 0xd64#64)) →
      SepWP P target_pc sf (((sp + 40#64) ↦₆₄ outBuf) ∗ (outBuf ↦ₛ rawBs) ∗ Rest) post oom) :
    SepWP P target_pc s (((sp + 40#64) ↦₆₄ outBuf) ∗ (outBuf ↦ₛ rawBs) ∗ Rest) post oom := by
  simp only [arm64_norm] at hx23 hx26
  let lastOff := 16 * (numBlocks - 1)
  let lb := rawBs.drop lastOff
  let lastBlkPtr := outBuf + BitVec.ofNat 64 lastOff
  let last := rawBs.getD (lastOff + 15) 0#8
  have hlb_len : lb.length = 16 := by dsimp only [lb, lastOff]; rw [List.length_drop, hlen]; omega
  have hsplit_raw : (outBuf ↦ₛ rawBs) =
      ((lastBlkPtr ↦ₛ lb) ∗ (outBuf ↦ₛ rawBs.take lastOff)) := by
    rw [pointsToBytes_take_drop outBuf lastOff rawBs (by omega)]
    dsimp only [lastBlkPtr, lb]; sep_ac_rfl
  have h15_lt : 15 < lb.length := by omega
  have hget15 : lb.getD 15 0#8 = last := getD_drop_eq rawBs lastOff 15
  have hx8_sub : BitVec.ofNat 64 numBlocks - 1#64 = BitVec.ofNat 64 (numBlocks - 1) :=
    bv64_ofNat_sub_one hpos (by omega)
  have hx8_sub' : BitVec.ofNat 64 numBlocks + 0xffffffffffffffff#64 = BitVec.ofNat 64 (numBlocks - 1) := by
    rw [show (0xffffffffffffffff#64 : BitVec 64) = -1#64 from rfl, ← BitVec.sub_eq_add_neg, hx8_sub]
  have hx9_calc : outBuf + (BitVec.ofNat 64 (numBlocks - 1)) <<< 4 = lastBlkPtr := by
    rw [lsl4_ofNat_eq (numBlocks - 1) (by omega)]
  have hx9_cur : outBuf + (BitVec.ofNat 64 numBlocks - 1#64) <<< 4 = lastBlkPtr := by
    rw [hx8_sub, hx9_calc]
  have hx9_cur' : outBuf + (BitVec.ofNat 64 numBlocks + 0xffffffffffffffff#64) <<< 4 = lastBlkPtr := by
    rw [hx8_sub', hx9_calc]
  have_instrs hUnpad 0 10
  have_instrs hUnpad 16 1
  rw [hsplit_raw]
  wp_steps 3
  rw [sepConj_left_comm ((sp + 40#64) ↦₆₄ outBuf) _, pointsToBytes_focus_at lastBlkPtr lb h15_lt,
      sepConj_assoc]
  try simp only [hx26, hx9_cur, hx9_cur']
  wp_steps 4
  rw [← sepConj_assoc, ← pointsToBytes_focus_at lastBlkPtr lb h15_lt]
  wp_if hlo_br
  · have hbad_last : ¬ (1 ≤ last.toNat ∧ last.toNat ≤ 16) := by
      intro hgood
      have hd : decide (1 ≤ last.toNat ∧ last.toNat ≤ 16) = true := decide_eq_true hgood
      simp [wp_norm, arm64_norm, unpad_ule_iff, hd] at hlo_br
    wp_step
    rw [← sepConj_left_comm ((sp + 40#64) ↦₆₄ outBuf) _, ← hsplit_raw]
    exact hnext _
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx23])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
      (PureStepPreserved.of_proj_perm rfl (by simp [wp_norm, arm64_norm]))
      (Or.inr ⟨pkcs7Unpad_of_bad_last hlen hpos hbad_last,
        by simp [wp_norm, arm64_norm]; try bv_lin⟩)
  · have hgood : 1 ≤ last.toNat ∧ last.toNat ≤ 16 := by
      by_contra hbad_last
      have hd : decide (1 ≤ last.toNat ∧ last.toNat ≤ 16) = false := decide_eq_false hbad_last
      simp [wp_norm, arm64_norm, unpad_ule_iff, hd] at hlo_br
    wp_steps 3
    rw [sepConj_assoc]
    refine cbc_unpad_inner (sp := sp) (outBuf := outBuf) hUnpad hOkPre rawBs numBlocks
      ((outBuf ↦ₛ rawBs.take lastOff) ∗ (sp + 40#64) ↦₆₄ outBuf ∗ Rest) s0
      hlen hpos hlt40 hgood.1 hgood.2
      (last.toNat - 1) (16 - last.toNat) _
      (by dsimp only [last, lastOff] at *; omega) (Nat.le_refl _)
      (fun _ hi1 hi2 => by dsimp only [last, lastOff] at *; omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      fun sf hrun_f hsp_f hx0_f hx23_f hv_f hpure_f hout_f => ?_
    · simp [wp_norm, arm64_norm]; try bv_lin
    · simp [wp_norm, arm64_norm, hrun]
    · simp [wp_norm, arm64_norm, hsp]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, lastBlkPtr, lastOff]
    · simp [wp_norm, arm64_norm, last, lastOff]
    · simp [wp_norm, arm64_norm]; exact bv64_16_sub_byte hgood.2
    · simp [wp_norm, arm64_norm]; exact bv64_16_sub_byte hgood.2
    · simp [wp_norm, arm64_norm, hx23]
    · simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv
    · rw [← sepConj_assoc, ← sepConj_left_comm ((sp + 40#64) ↦₆₄ outBuf) _, ← hsplit_raw]
      exact hnext sf hrun_f hsp_f hx0_f hx23_f hv_f
        (PureStepPreserved.trans
          (PureStepPreserved.of_proj_perm rfl (by simp [wp_norm, arm64_norm])) hpure_f)
        hout_f

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Unpad
