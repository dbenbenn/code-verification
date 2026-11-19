/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopEntry
import LibsignalBinary.Proofs.E2E.Record.L1GX.Fields
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Prologue and outer-header leaf `deserD0X_ok`

Proves the `SessionRecord::deserialize` entry segment (`+0x000` to `+0x254`) in PQXDH scope:
stack frame setup, `SessionStructure::default()` zero-initialization, outer protobuf tag `0x0a`
check, and single- or multi-byte payload length varint decoding.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.DeserD0X

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.RecordX (DeserializeScopeP)
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_d0g (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_d0g (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_d0g (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_d0g (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_d0g (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_d0g (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_d0g (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_d0g (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_d0g (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_d0g (s : State) (pc : BitVec 64) (m : Memory) (w :
    RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[irreducible] private def deserEntry_d0g : BitVec 64 := 0x16ed4#64

private theorem encodeKey_1_ld_d0g : encodeKey 1 .lengthDelimited = [0x0a#8] := rfl

private theorem encodeVarint_length_pos_d0g (v : BitVec 64) :
    0 < (encodeVarint v).length :=
  List.length_pos_iff.mpr (encodeVarint_ne_nil v)

private theorem encodeVarint_of_lt_128_d0g {n : Nat} (hn : n < 128) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem encodeVarint_cons_of_ge_128_d0g {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 20) :
    encodeVarint (BitVec.ofNat 64 n) =
      BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn,
    show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7,
    show (0x80 : BitVec 64).toNat = 128 from rfl,
    Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

private theorem signExtend64_bit63_eq_false_iff_d0g (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

private theorem signExtend64_bit63_eq_true_iff_d0g (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

private theorem signExtend64_eq_zeroExtend64_of_le_d0g (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

private theorem signExtend64_ofNat8_lt_128_d0g {n : Nat} (hn : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_d0g _ hle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-! ## Stack alignment and `prostSSGAt` initialization -/

private theorem sp_sub_1904_aligned_d0g {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'
  have hlt := sp0.isLt
  have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h' ⊢; omega
  · rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h' ⊢; omega

private theorem empty_vecU8_intro_d0g (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A0 v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
      (1#64 : BitVec 64) ≠ 0#64 := by decide
  have heq :
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
          (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
        (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)

private theorem empty_vecChainG_intro_d0g (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A0.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (fun c a => prostChainGAt A0 a c) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

private theorem pointsTo64_zero_split32_d0g (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private def ssRawCells_d0g (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗
  (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗
  (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗
  (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗
  ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGAt_empty_intro_d0g (L : BitVec 64) :
    ssRawCells_d0g L ∗ memRegion (L + 0x4b8#64) 96 ∗
      memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢
      prostSSGAt A0 (L + 0x420#64) SSG.empty := by
  unfold ssRawCells_d0g prostSSGAt SSG.empty; dsimp only
  have h1 := empty_vecU8_intro_d0g (L + 0x420#64)
  have h2 := empty_vecU8_intro_d0g (L + 0x420#64 + 0x18#64)
  have h3 := empty_vecU8_intro_d0g (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_d0g (L + 0x420#64 + 0x48#64)
  have h5 := empty_vecU8_intro_d0g (L + 0x420#64 + 0x60#64)
  have h6 := empty_vecU8_intro_d0g (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_d0g (L + 0x568#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))
  exact Entails.of_eq (by ac_rfl)

/-! ## Stack-offset normalization -/

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1904_sub_96_d0g (L : BitVec 64) :
    L + 1904#64 + 18446744073709551520#64 = L + 1808#64 := by rw [BitVec.add_assoc]; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_1808_d0g (L : BitVec 64) :
    L + 1808#64 - 1808#64 = L := by bv_omega

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_40_d0g (L : BitVec 64) :
    L + 1808#64 + 18446744073709551576#64 = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_d0g (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSavedAt_eq_d0g (s0 : State) :
    deserSavedAt_d0g (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_d0g deserSaved deserSpL; dsimp only
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## `SessionStructure::default()` zero-initialization (`+0x104` to `+0x15c`) -/

private def ssUninitCells_d0g (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) :
    SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗
  ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗
  ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗
  ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗ ((L + 1152#64) ↦₆₄ c12) ∗
  ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗
  ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗
  ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗
  ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)

private def step1aPre_d0g (L p : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗
  ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗
  ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗
  ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗
  ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗
  ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗
  ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗
  ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗
  ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)

private def step1aPost_d0g (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_d0g L s0 ∗ (L ↦₆₄ 0#64) ∗
  ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
  ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
  ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)

private def step2aPre_d0g (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2aPost_d0g (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2bPre_d0g (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))

private def step2bPostPre_d0g (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))

private def step2bPostPost_d0g (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)

private theorem memRegion_succ8_d0g (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_d0g (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64,
      ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64,
      ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_d0g L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20
          c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide),
    memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1
    simp (discharger :=
      decide) only [memRegion_succ8_d0g, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
      BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger :=
      decide) only [memRegion_succ8_d0g, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
      BitVec.reduceAdd]
  unfold ssUninitCells_d0g
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_d0g (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_d0g L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 1808 96 (by decide),
    memRegion_split L 8 1800 (by decide),
    memRegion_split (L + 8#64) 1008 792 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 744 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 408 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 40 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight L, ProofLib.memRegion_eight (L + 1768#64)]
  conv_lhs =>
    arg 1; arg 2
    simp (discharger :=
      decide) only [memRegion_succ8_d0g, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
      BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 1; arg 2; arg 2; arg 1
    simp (discharger :=
      decide) only [memRegion_succ8_d0g, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
      BitVec.reduceAdd]
  unfold step1aPre_d0g
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_d0g (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack =
      stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 =
    memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_d0g (L : BitVec 64) :
    (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocalsG_d0g (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGAt A0 (L + 0x420#64) SSG.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_d0g (L p : BitVec 64) (len1 : Nat) (s0 : State)
    (hL : L = deserSpL s0.sp) :
    ssRawCells_d0g L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗
      memRegion (L + 1360#64) 24 ∗ deserSavedAt_d0g L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
      ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗
      memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_d0g L ∗ deserSaved s0 := by
  have hss := prostSSGAt_empty_intro_d0g L
  have hm0 := memRegion_0_1016_intro_d0g L
  have hds : deserSavedAt_d0g L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_d0g s0
  unfold deserFixedLocalsG_d0g; rw [hds]
  rw [show (0x408#64 : BitVec 64) = 1032#64 from rfl,
    show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl,
    show (0x6f0#64 : BitVec 64) = 1776#64 from rfl,
    show (0x20 : Nat) = 32 from rfl]
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono (sepConj_mono hss hm0)
        (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
          ((L + 1048#64) ↦₆₄ 0#64) ∗ memRegion (L + 1776#64) 32 ∗ deserSaved s0))) ?_)
  · exact Entails.of_eq (by ac_rfl)
  · exact Entails.of_eq (by ac_rfl)

private theorem scratch24_368_fold_d0g (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
      ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) =
      ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_d0g (L + 1400#64)).symm
    rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs; exact hs
  rw [← sepConj_assoc, h0,
    memRegion_split (L + 1400#64) 24 344 (by decide),
    memRegion_split (L + 1400#64) 8 16 (by decide),
    memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
        (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v)
          (pointsTo64_entails_memRegion (L + 1416#64) w)))
      (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

private theorem deserLocalsG_of_2a_d0g (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFieldsX r).flatMap GenFieldX.enc).length) ++
      (recFieldsX r).flatMap GenFieldX.enc)
    (hN : ((recFieldsX r).flatMap GenFieldX.enc).length < 128) :
    let body := (recFieldsX r).flatMap GenFieldX.enc
    step2aPost_d0g L p body.length ∗
      ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_d0g L =
    deserLocalsG L p (encodeRecord r) body SSG.empty := by
  intro body
  have hpfx : encodeRecord r =
      0x0a#8 :: BitVec.ofNat 8 body.length :: body := by
    rw [heq, encodeKey_1_ld_d0g, encodeVarint_of_lt_128_d0g hN]; rfl
  have hsub : (encodeRecord r).length - body.length = 2 := by
    rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗
        ((p + 1#64 + 1#64) ↦ₛ body) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_d0g step2aPost_d0g
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_d0g (L p : BitVec 64) (vlen N : Nat) :
    step2bPostPost_d0g L p vlen N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_d0g
  refine Entails.trans ?_
    (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N))
      (scratch24_368_fold_d0g L (BitVec.ofNat 64 N) (BitVec.ofNat 64 vlen)))
  exact Entails.of_eq (by ac_rfl)

private theorem deserLocalsG_of_2b_d0g (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFieldsX r).flatMap GenFieldX.enc).length) ++
      (recFieldsX r).flatMap GenFieldX.enc) :
    let body := (recFieldsX r).flatMap GenFieldX.enc
    let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_d0g L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_d0g L ⊢
    deserLocalsG L p (encodeRecord r) body SSG.empty := by
  intro body vlen
  refine Entails.trans
    (sepConj_mono_left (step2bPostPost_entails_d0g L p vlen body.length)) ?_
  have hpfx : encodeRecord r =
      0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by
    rw [heq, encodeKey_1_ld_d0g]; rfl
  have hsub : (encodeRecord r).length - body.length = 1 + vlen := by
    rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_d0g
  rw [hsub, hptr, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_d0g (L : BitVec 64) :
    stackAt L deserCalleeStack =
      stackAt L Prost.decodeVarintSliceStack ∗ memRegion (L - 63632#64) 55360 := by
  change memRegion (L - 63632#64) 63632 =
    memRegion (L - 8272#64) 8272 ∗ memRegion (L - 63632#64) 55360
  rw [memRegion_split (L - 63632#64) 55360 8272 (by decide)]
  have h1 : L - 63632#64 + 55360#64 = L - 8272#64 := by bv_omega
  rw [h1, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_d0g {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_d0g {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_d0g htr) h

end CryptoVerification.E2E.Record.L1GX.Leaf.DeserD0X
