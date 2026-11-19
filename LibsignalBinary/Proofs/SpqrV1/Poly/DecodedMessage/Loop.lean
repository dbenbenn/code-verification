/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- proof-setup: allow-public-import
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Loop Lemmas

**Checked by Lean.**

Proves the inner binary-search loop (`0x6bdb8..0x6bdf0`) and both complete and incomplete paths of
the `collectPointsVecs` loop (`0x6bc00..0x6bce0`) in `decoded_message`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-- Combined trace and callee-saved vector registers of `s`, allowing equality
    `traceVRegs sf = traceVRegs s` to be rewritten via `rw`, `rfl`, `.trans`, and `simp`. -/
@[expose] def traceVRegs (s : State) := (s.trace, calleeSavedVRegs s)

theorem traceVRegs_eq_iff (s1 s2 : State) :
    (traceVRegs s1 = traceVRegs s2) ↔
      (s1.trace = s2.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s2) := by
  simp [traceVRegs]

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_advancePC (s : State) : traceVRegs s.advancePC = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_setPC (s : State) (pc : BitVec 64) : traceVRegs (s.setPC pc) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_setMem (s : State) (m : Memory) : traceVRegs (s.setMem m) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_setPState (s : State) (ps : PState) : traceVRegs (s.setPState ps) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeReg64 (s : State) (r : Reg) (val : BitVec 64) :
    traceVRegs (s.writeReg64 r val) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeReg32 (s : State) (r : Reg) (val : BitVec 32) :
    traceVRegs (s.writeReg32 r val) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeReg (s : State) (w : Width) (r : Reg) (val : BitVec 64) :
    traceVRegs (s.writeReg w r val) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    traceVRegs (s.writeVReg128 v val) =
      cond (isCalleeSavedVReg v)
        (s.trace, updateCalleeSavedVRegs v (val.truncate 64) (calleeSavedVRegs s))
        (traceVRegs s) := by
  unfold traceVRegs
  rw [calleeSavedVRegs_writeVReg128_ite, State.trace_writeVReg128]
  cases isCalleeSavedVReg v <;> rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeVReg64 (s : State) (v : BitVec 5) (val : BitVec 64) :
    traceVRegs (s.writeVReg64 v val) =
      traceVRegs (s.writeVReg128 v (val.zeroExtend 128)) := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_writeVReg32 (s : State) (v : BitVec 5) (val : BitVec 32) :
    traceVRegs (s.writeVReg32 v val) =
      traceVRegs (s.writeVReg128 v (val.zeroExtend 128)) := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_setBrk (s : State) (b : BitVec 64) :
    traceVRegs (s.setBrk b) = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_nextOracle (s : State) :
    traceVRegs s.nextOracle = traceVRegs s := rfl

@[simp, arm64_norm, wp_norm]
theorem traceVRegs_setStatus (s : State) (st : ExecStatus) :
    traceVRegs (s.setStatus st) = traceVRegs s := rfl

theorem pointsTo64_pair_eq_pointsTo128 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  rw [cat128_extractLsb_lo, cat128_extractLsb_hi]

theorem pointsTo128_eq_pointsTo64_pair (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) = ((a ↦₆₄ q.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q.extractLsb' 64 64)) := by
  unfold pointsTo128
  rfl

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_lsl4_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  change (n % 18446744073709551616 * 16) % 18446744073709551616 = (16 * n) % 18446744073709551616
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem bv64_lsl4_ofNat {n : Nat} (_hn : 16 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n) <<< 4 = BitVec.ofNat 64 (16 * n) :=
  bv64_lsl4_norm n

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_madd24_norm (base : BitVec 64) (i : Nat) :
    base + BitVec.ofNat 64 i * 24#64 = base + BitVec.ofNat 64 (24 * i) := by
  rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]

theorem bv64_madd24_dec (base : BitVec 64) {i : Nat} (_hi : i < 16) :
    base + BitVec.ofNat 64 i * 24#64 = base + BitVec.ofNat 64 (24 * i) :=
  bv64_madd24_norm base i

theorem bv64_umaddl24_ofNat (base : BitVec 64) {i : Nat} (hi : i < 16) :
    base + BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i)) *
      BitVec.zeroExtend 64 24#32 =
      base + BitVec.ofNat 64 (24 * i) := by
  have h1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [h1]
  exact bv64_madd24_ofNat base hi

theorem bv64_beq_15_ofNat {n : Nat} (hn : n < 16) :
    (BitVec.ofNat 64 n == 15#64) = decide (n = 15) := by
  by_cases h : n = 15
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact h hto

theorem bv64_beq_16_ofNat {n : Nat} (hn : n ≤ 16) :
    (BitVec.ofNat 64 n == 16#64) = decide (n = 16) := by
  by_cases h : n = 16
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact h hto

theorem bv64_bne_16_ofNat {n : Nat} (hn : n ≤ 16) :
    (BitVec.ofNat 64 n != 16#64) = decide (n ≠ 16) := by
  by_cases h : n = 16
  · subst h; rfl
  · simp only [h, not_false_eq_true, decide_true, bne_iff_ne, ne_eq]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact h hto

theorem memRegion_16_eq_exists_pair (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]
  apply sepProp_eq_of_entails
  · rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro v0
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v1
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.refl _))
  · apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    exact sepConj_mono (Entails.sepExists_right v0 (Entails.refl _))
      (Entails.sepExists_right v1 (Entails.refl _))

theorem memRegion_256_focus16 (base : BitVec 64) {i : Nat} (hi : i < 16) :
    memRegion base 256 =
      memRegion base (16 * i) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
          ((base + BitVec.ofNat 64 (16 * i)) ↦₆₄ v0) ∗
          ((base + BitVec.ofNat 64 (16 * i) + 8#64) ↦₆₄ v1)) ∗
        memRegion (base + BitVec.ofNat 64 (16 * (i + 1))) (256 - 16 * (i + 1)) := by
  have h1 : 256 = 16 * i + (16 + (256 - 16 * (i + 1))) := by omega
  have haddr : base + BitVec.ofNat 64 (16 * i) + 16#64 =
      base + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  conv_lhs => rw [h1]
  rw [memRegion_split base (16 * i) (16 + (256 - 16 * (i + 1))) (by omega),
    memRegion_split (base + BitVec.ofNat 64 (16 * i)) 16 (256 - 16 * (i + 1)) (by omega),
    haddr, memRegion_16_eq_exists_pair (base + BitVec.ofNat 64 (16 * i))]

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_8 (sp0 : BitVec 64) : sp0 - 672#64 + 8#64 = sp0 - 664#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_16 (sp0 : BitVec 64) : sp0 - 672#64 + 16#64 = sp0 - 656#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_24 (sp0 : BitVec 64) : sp0 - 672#64 + 24#64 = sp0 - 648#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_32 (sp0 : BitVec 64) : sp0 - 672#64 + 32#64 = sp0 - 640#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_40 (sp0 : BitVec 64) : sp0 - 672#64 + 40#64 = sp0 - 632#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_48 (sp0 : BitVec 64) : sp0 - 672#64 + 48#64 = sp0 - 624#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_56 (sp0 : BitVec 64) : sp0 - 672#64 + 56#64 = sp0 - 616#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_64 (sp0 : BitVec 64) : sp0 - 672#64 + 64#64 = sp0 - 608#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp672_add_72 (sp0 : BitVec 64) : sp0 - 672#64 + 72#64 = sp0 - 600#64 := by bv_omega

theorem sp672_aligned (sp0 : BitVec 64) (hsp0 : sp0 &&& 15#64 = 0#64) :
    (sp0 - 672#64) &&& 15#64 = 0#64 := by
  have h : (sp0 - 672#64) &&& 15#64 = sp0 &&& 15#64 := by bv_bits
  rw [h, hsp0]

theorem memRegion_256_unfocus16 (base : BitVec 64) {i : Nat} (hi : i < 16) (w0 w1 : BitVec 64) :
    memRegion base (16 * i) ∗
      (((base + BitVec.ofNat 64 (16 * i)) ↦₆₄ w0) ∗
        ((base + BitVec.ofNat 64 (16 * i) + 8#64) ↦₆₄ w1)) ∗
      memRegion (base + BitVec.ofNat 64 (16 * (i + 1))) (256 - 16 * (i + 1)) ⊢
      memRegion base 256 := by
  rw [memRegion_256_focus16 base hi]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))

theorem memRegion_16_mul_split_one (base : BitVec 64) {i : Nat} (hi : i < 16) :
    memRegion (base + BitVec.ofNat 64 (16 * i)) (16 * (16 - i)) =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((base + BitVec.ofNat 64 (16 * i)) ↦₆₄ v0) ∗
        ((base + BitVec.ofNat 64 (16 * i) + 8#64) ↦₆₄ v1)) ∗
      memRegion (base + BitVec.ofNat 64 (16 * (i + 1))) (16 * (16 - (i + 1))) := by
  have hmul : 16 * (16 - i) = 16 + 16 * (16 - (i + 1)) := by omega
  have haddr : base + BitVec.ofNat 64 (16 * i) + 16#64 =
      base + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [hmul, memRegion_split (base + BitVec.ofNat 64 (16 * i)) 16 (16 * (16 - (i + 1))) (by omega),
    haddr, memRegion_16_eq_exists_pair (base + BitVec.ofNat 64 (16 * i))]

/-! ## Binary Search Loop (`0x6bdb8..0x6bdf0`, `entry + 568#64` to `entry + 624#64`) -/

end CryptoVerification.SpqrV1.Poly.DecodedMessage

