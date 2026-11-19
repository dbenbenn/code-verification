/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import ProofLib.SepLogic.WPp

/-!
# Base Lemmas and Initial Stages for No-Grow `encode_varint`

Callee-saved register invariants, `BitVec` continuation-byte lemmas, and stepping lemmas for the
prologue, final byte write, and stages 1–3 of `encode_varint` (`0x30a0`) on the spare-capacity path.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeVarintNorm

@[scoped simp, scoped arm64_norm]
theorem false_eq_true' : (false = true) = False := Bool.false_eq_true

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

theorem zext64_trunc32_orr_mask (x : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 18446743528248704896#64)) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 4294967168#64 := by
  simp

theorem ushr_ushr_7 (v : BitVec 64) (k n : Nat) (h : k + 7 = n := by rfl) :
    (v >>> k) >>> 7 = v >>> n := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

end EncodeVarintNorm
open EncodeVarintNorm

/-! ## Callee-Saved Register Invariants -/

@[expose] def EncVarintCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EncVarintCalleeSaved.refl (s : State) : EncVarintCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EncVarintCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EncVarintCalleeSaved s0 s1) (h2 : EncVarintCalleeSaved s1 s2) :
    EncVarintCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2⟩

theorem cap_beq_len_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (cap == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hn : n < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
  omega

theorem bv_len_add_one (bs : List (BitVec 8)) (byte : BitVec 8) :
    BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs ++ [byte]).length := by
  simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]

/-! ## `BitVec` and `encodeVarint` Byte Lemmas -/

@[expose] def varintContByte (v : BitVec 64) : BitVec 8 :=
  ((v &&& 0x7F#64) ||| 0x80#64).setWidth 8

private theorem bv8_and_7f_or_80 :
    ∀ b : BitVec 8, (b &&& 0x7F#8) ||| 0x80#8 = b ||| 0x80#8 := by
  decide

private theorem varintContByte_eq_or_80 (v : BitVec 64) :
    varintContByte v = v.setWidth 8 ||| 0x80#8 := by
  unfold varintContByte
  rw [BitVec.setWidth_or, BitVec.setWidth_and]
  exact bv8_and_7f_or_80 (v.setWidth 8)

@[scoped simp, scoped arm64_norm]
theorem zext8_zext64_trunc32 (x : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) = BitVec.zeroExtend 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w64 (w : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w) ||| 18446743528248704896#64) =
      varintContByte w := by
  rw [varintContByte_eq_or_80]
  have h1 := zext8_zext64_trunc32 w
  simp only [BitVec.zeroExtend, BitVec.setWidth_or] at h1 ⊢
  rw [h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_7 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 7) ||| 18446743528248704896#64) =
      varintContByte (v >>> 7) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 7)).setWidth 8 =
      (v >>> 7).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_14 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 14) ||| 18446743528248704896#64) =
      varintContByte (v >>> 14) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 14)).setWidth 8 =
      (v >>> 14).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_21 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 21) ||| 18446743528248704896#64) =
      varintContByte (v >>> 21) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 21)).setWidth 8 =
      (v >>> 21).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_7 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 7) =
      varintContByte (v >>> 7) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_14 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 14) =
      varintContByte (v >>> 14) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_21 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 21) =
      varintContByte (v >>> 21) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem ult_0x4000_eq (v : BitVec 64) :
    v.ult 16384#64 = (v >>> 7).ult 128#64 := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ule_0x4000_eq (v : BitVec 64) :
    (16384#64 : BitVec 64).ule v = !(v >>> 7).ult 128#64 := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    ← decide_not]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ult_0x200000_eq (v : BitVec 64) :
    v.ult 2097152#64 = (v >>> 14).ult 128#64 := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ule_0x200000_eq (v : BitVec 64) :
    (2097152#64 : BitVec 64).ule v = !(v >>> 14).ult 128#64 := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    ← decide_not]
  exact decide_eq_decide.mpr (by omega)

private theorem beq_zero64_eq_decide (x : BitVec 64) :
    (x == 0#64) = decide (x.toNat = 0) := by
  rcases hx : (x == 0#64) with _ | _
  · rw [beq_eq_false_iff_ne] at hx
    exact (decide_eq_false (fun heq => hx (BitVec.eq_of_toNat_eq heq))).symm
  · rw [beq_iff_eq] at hx
    exact (decide_eq_true (congrArg BitVec.toNat hx)).symm

@[scoped simp, scoped arm64_norm]
theorem shr28_beq_zero (v : BitVec 64) :
    (v >>> 28 == 0#64) = (v >>> 21).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr28_bne_zero (v : BitVec 64) :
    (v >>> 28 != 0#64) = !(v >>> 21).ult 128#64 := by
  simp only [bne, shr28_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr35_beq_zero (v : BitVec 64) :
    (v >>> 35 == 0#64) = (v >>> 28).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr35_bne_zero (v : BitVec 64) :
    (v >>> 35 != 0#64) = !(v >>> 28).ult 128#64 := by
  simp only [bne, shr35_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr42_beq_zero (v : BitVec 64) :
    (v >>> 42 == 0#64) = (v >>> 35).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr42_bne_zero (v : BitVec 64) :
    (v >>> 42 != 0#64) = !(v >>> 35).ult 128#64 := by
  simp only [bne, shr42_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr49_beq_zero (v : BitVec 64) :
    (v >>> 49 == 0#64) = (v >>> 42).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr49_bne_zero (v : BitVec 64) :
    (v >>> 49 != 0#64) = !(v >>> 42).ult 128#64 := by
  simp only [bne, shr49_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr56_beq_zero (v : BitVec 64) :
    (v >>> 56 == 0#64) = (v >>> 49).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr56_bne_zero (v : BitVec 64) :
    (v >>> 56 != 0#64) = !(v >>> 49).ult 128#64 := by
  simp only [bne, shr56_beq_zero]

private theorem bv8_getLsbD_7 :
    ∀ b : BitVec 8, b.getLsbD 7 = !decide (b.toNat < 128) := by
  decide

private theorem bv8_eq_or_80_of_not_lt :
    ∀ b : BitVec 8, decide (b.toNat < 128) = false → b = b ||| 0x80#8 := by
  decide

@[scoped simp, scoped arm64_norm]
theorem getLsbD_63_eq (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  have hv := v.isLt
  have h1 : ((v >>> 56).setWidth 8).getLsbD 7 = v.getLsbD 63 := by
    simp
  have h2 : ((v >>> 56).setWidth 8).toNat = (v >>> 56).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [← h1, bv8_getLsbD_7, h2, BitVec.ult_eq_decide]
  rfl

theorem contByte9_contByte_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    BitVec.zeroExtend 8 (val >>> 56) = varintContByte (val >>> 56) := by
  have hv := val.isLt
  have h2 : ((val >>> 56).setWidth 8).toNat = (val >>> 56).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [varintContByte_eq_or_80]
  apply bv8_eq_or_80_of_not_lt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  rw [h2]
  exact h

theorem contByte9_shr63_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    (1#64 : BitVec 64) = val >>> 63 := by
  have hv := val.isLt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not] at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem shr63_ult_128 (val : BitVec 64) :
    (val >>> 63).ult 128#64 = true := by
  have hv := val.isLt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq]
  omega

/-! ## `encodeVarint` Unfolding and Spare-Capacity Helpers -/

theorem encodeVarintAux_of_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = true) :
    encodeVarintAux (fuel + 1) v = [v.setWidth 8] := by
  have hlt : v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; exact h
  simp [encodeVarintAux, hlt]

theorem encodeVarintAux_of_not_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = false) :
    encodeVarintAux (fuel + 1) v = varintContByte v :: encodeVarintAux fuel (v >>> 7) := by
  have hlt : ¬ v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; omega
  simp [encodeVarintAux, varintContByte, hlt]

theorem encodeVarint_exit_bs {fuel : Nat} {v : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = true) :
    bs ++ [v.setWidth 8] = rhs := by
  rw [← encodeVarintAux_of_ult h, hcur]

theorem encodeVarint_step_bs {fuel : Nat} {v nextV : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = false)
    (hshift : v >>> 7 = nextV) :
    (bs ++ [varintContByte v]) ++ encodeVarintAux fuel nextV = rhs := by
  rw [List.append_assoc, List.singleton_append, ← hshift,
    ← encodeVarintAux_of_not_ult h, hcur]

theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

theorem curBs_length_lt_cap {curBs bs : List (BitVec 8)} {k : Nat} {v cap val : BitVec 64}
    (hcur : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val)
    (hcap : bs.length + (encodeVarint val).length ≤ cap.toNat) :
    curBs.length < cap.toNat := by
  have h1 := congrArg List.length hcur
  simp only [List.length_append] at h1
  have h2 : 1 ≤ (encodeVarintAux (k + 1) v).length := by
    unfold encodeVarintAux; split <;> simp
  omega

theorem stackAt_encodeVarint_eq (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt (sp - 48#64) doReserveStack ∗
      (∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (doReserveStack + 8 * 6) = _
  rw [LibsignalTripleRatchet.stackAt_split_cells sp doReserveStack 6 (by decide)]
  congr 1
  cells_unfold

/-! ## Prologue, Final-Byte, and Stage 1–3 Stepping Lemmas -/

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
