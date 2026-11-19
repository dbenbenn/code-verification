/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.ByteRegion

/-!
# Shared Byte-Slice, Stack-Frame, and `FieldElement51` Window Helpers

Shared `ByteSlice` window/focus/write lemmas, stack-frame peel/unpeel/callee-resize combinators,
5-limb `FieldElement51` unreduced/biased modular reduction identities, and `modPow` / `fpPow`
bridges imported across the `EdwardsPoint` proof modules.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpNeg fpPow modPow modPowLoop EdExtPoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  readLE_congr_off readLE_slice_eq
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edProjDouble edAsExtended)

/-! ## 1. Read-Only Slice & Stack-Frame Splitting Helpers -/

theorem pointsToBytesRO_take_drop (a : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (h : n ≤ bs.length) :
    (a ↦ᵣ bs) = (a ↦ᵣ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have happ := pointsToBytesRO_append a (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le h] at happ
  exact happ

theorem addWithCarry64_false_c (x y : BitVec 64) :
    (AddWithCarry64 x y false).2.c = BitVec.ult (x + y) x :=
  conditionHolds_cs_adds64 x y

theorem stackFrame_eq_stackFrameAt (s : State) (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) :
    stackFrame s n = stackFrameAt s.sp n :=
  (stackFrameAt_eq_memRegion s.sp n hn).symm

theorem stack_fold_step (sp v : BitVec 64) (n k : Nat) (hmk : 8 + k = n) (hn : n ≤ 2 ^ 64) :
    (((sp - BitVec.ofNat 64 n) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 k) k) ⊢
      memRegion (sp - BitVec.ofNat 64 n) n := by
  rw [memRegion_split_sub sp n 8 k hmk hn]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ v)

theorem stack_fold_last (sp v : BitVec 64) :
    ((sp - 8#64) ↦₆₄ v) ⊢ memRegion (sp - 8#64) 8 :=
  pointsTo64_entails_memRegion (sp - 8#64) v

theorem stack_swap_slice (sp off v : BitVec 64) (p : BitVec 64) (bs : List (BitVec 8))
    (rest : SepProp) :
    (((sp - off) ↦₆₄ v) ∗ ((p ↦ₛ bs) ∗ rest)) = ((p ↦ₛ bs) ∗ (((sp - off) ↦₆₄ v) ∗ rest)) :=
  sepConj_left_comm _ _ _

/-! ## 2. `HasLenGe` / `HasExactLen` & `ByteSlice` Read-Over-Write Lemmas -/

theorem readLE_write64_of_disjoint (bs : List (BitVec 8)) (off1 off2 : Nat) (v : BitVec 64)
    (hdisj : off1 + 8 ≤ off2 ∨ off2 + 8 ≤ off1) (hlen : off1 ≤ bs.length) :
    ByteSlice.readLE (ByteSlice.write64 bs off1 v) off2 8 = ByteSlice.readLE bs off2 8 := by
  apply ByteSlice.readLE_congr
  intro i _hi
  rw [ByteSlice.getD_write64 bs off1 v (off2 + i) 0#8 hlen]
  have : ¬(off1 ≤ off2 + i ∧ off2 + i < off1 + 8) := by omega
  simp [this]

class HasLenGe (bs : List (BitVec 8)) (n : outParam Nat) : Prop where
  le_length : n ≤ bs.length

class HasExactLen (bs : List (BitVec 8)) (n : outParam Nat) : Prop where
  length_eq : bs.length = n

theorem write_length_eq (bs src : List (BitVec 8)) (off : Nat) :
    (ByteSlice.write bs off src).length =
      min off bs.length + src.length + (bs.length - (off + src.length)) := by
  simp only [ByteSlice.write, List.length_append, List.length_take, List.length_drop]

theorem write64_length_eq (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64) :
    (ByteSlice.write64 bs off v).length = min off bs.length + 8 + (bs.length - (off + 8)) := by
  simp only [ByteSlice.write64, ByteSlice.writeLE, write_length_eq, ByteSlice.unpackLE_length]

instance instHasLenGeWrite (bs src : List (BitVec 8)) (off n : Nat)
    [h : HasLenGe bs n] : HasLenGe (ByteSlice.write bs off src) n where
  le_length := by
    have hle := h.le_length
    rw [write_length_eq]
    omega

instance instHasLenGeWrite64 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64) (n : Nat)
    [h : HasLenGe bs n] : HasLenGe (ByteSlice.write64 bs off v) n where
  le_length := by
    have hle := h.le_length
    rw [write64_length_eq]
    omega

theorem readLE_write64_self' (bs : List (BitVec 8)) (off n : Nat) (v : BitVec 64)
    [h : HasLenGe bs n]
    (h1 : decide (off ≤ n) = true) :
    ByteSlice.readLE (ByteSlice.write64 bs off v) off 8 = v :=
  ByteSlice.readLE_write64_self bs off v (Nat.le_trans (of_decide_eq_true h1) h.le_length)

theorem readLE_write64_ne (bs : List (BitVec 8)) (off1 off2 n : Nat) (v : BitVec 64)
    [h : HasLenGe bs n]
    (h1 : decide (off1 ≤ n ∧ (off1 + 8 ≤ off2 ∨ off2 + 8 ≤ off1)) = true) :
    ByteSlice.readLE (ByteSlice.write64 bs off1 v) off2 8 = ByteSlice.readLE bs off2 8 := by
  have hdec := of_decide_eq_true h1
  exact readLE_write64_of_disjoint bs off1 off2 v hdec.2 (Nat.le_trans hdec.1 h.le_length)

theorem readLE_write_inside (bs src : List (BitVec 8)) (off1 off2 m n : Nat)
    [hs : HasExactLen src m] [hb : HasLenGe bs n]
    (h1 : decide (off1 ≤ n ∧ off1 ≤ off2 ∧ off2 + 8 ≤ off1 + m) = true) :
    ByteSlice.readLE (ByteSlice.write bs off1 src) off2 8 =
      ByteSlice.readLE src (off2 - off1) 8 := by
  have hdec := of_decide_eq_true h1
  have hlen : off1 ≤ bs.length := Nat.le_trans hdec.1 hb.le_length
  have hsrc : src.length = m := hs.length_eq
  apply readLE_congr_off
  intro i hi
  rw [ByteSlice.getD_write bs src off1 (off2 + i) 0#8 hlen]
  have hcond : off1 ≤ off2 + i ∧ off2 + i < off1 + src.length := by omega
  have hsub : off2 + i - off1 = off2 - off1 + i := by omega
  simp only [hcond, and_self, ↓reduceIte, hsub]

theorem readLE_write_ne (bs src : List (BitVec 8)) (off1 off2 m n : Nat)
    [hs : HasExactLen src m] [hb : HasLenGe bs n]
    (h1 : decide (off1 ≤ n ∧ (off1 + m ≤ off2 ∨ off2 + 8 ≤ off1)) = true) :
    ByteSlice.readLE (ByteSlice.write bs off1 src) off2 8 =
      ByteSlice.readLE bs off2 8 := by
  have hdec := of_decide_eq_true h1
  have hlen : off1 ≤ bs.length := Nat.le_trans hdec.1 hb.le_length
  have hsrc : src.length = m := hs.length_eq
  apply ByteSlice.readLE_congr
  intro i hi
  rw [ByteSlice.getD_write bs src off1 (off2 + i) 0#8 hlen]
  have hcond : ¬(off1 ≤ off2 + i ∧ off2 + i < off1 + src.length) := by omega
  simp only [hcond, ↓reduceIte]

/-! ## 3. 5-Limb `FieldElement51` Modular Reduction & Arithmetic Identities -/

private theorem mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem lsr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem umaddl19_lsr51_toNat (d0 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat =
      d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
  have hd4 : d4.toNat < 2 ^ 64 := d4.isLt
  have hze : (BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51))).toNat = d4.toNat / 2 ^ 51 := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, lsr51_toNat]
    omega
  have hm := mask51_toNat d0
  rw [BitVec.toNat_add, BitVec.toNat_mul, hze, hm, show (19#64).toNat = 19 from rfl]
  omega

private theorem add_mask51_lsr51_toNat (di dprev : BitVec 64) :
    ((di &&& 2251799813685247#64) + (dprev >>> 51)).toNat =
      di.toNat % 2 ^ 51 + dprev.toNat / 2 ^ 51 := by
  have hprev : dprev.toNat < 2 ^ 64 := dprev.isLt
  rw [BitVec.toNat_add, mask51_toNat, lsr51_toNat]
  omega

/-- Unconditional limb bound (`< 2^52`) for the 5-limb `FieldElement51::reduce` output. -/
theorem fe51Reduce_bounded (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat < 2 ^ 52 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 52 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 52 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 52 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 52 := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt
  rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
    add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
  omega

theorem fe51Reduce_bounded54 (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat < 2 ^ 54 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 54 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 54 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 54 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 54 := by
  have ⟨h0, h1, h2, h3, h4⟩ := fe51Reduce_bounded d0 d1 d2 d3 d4
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Unconditional modular identity for `FieldElement51::reduce`: the reduced 5-limb value equals
    the unreduced 5-limb value modulo `p25519 = 2^255 - 19`. -/
theorem fe51Reduce_val_mod (d0 d1 d2 d3 d4 : BitVec 64) :
    fe51Val
      ((d0 &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
      ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
      ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
      ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
      ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) % p25519 =
    fe51Val d0 d1 d2 d3 d4 % p25519 := by
  have hid :
      fe51Val
        ((d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
        ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
        ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
        ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
        ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) +
      p25519 * (d4.toNat / 2 ^ 51) =
      fe51Val d0 d1 d2 d3 d4 := by
    unfold fe51Val p25519
    rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
      add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
    omega
  rw [← hid, Nat.add_mul_mod_self_left]

/-- Modulo `p25519` identity for biased 5-limb negation (`16*p - a`). -/
theorem fe51Neg_val_mod (l0 l1 l2 l3 l4 : BitVec 64)
    (h : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧
         l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54) :
    fe51Val
      (36028797018963664#64 - l0)
      (36028797018963952#64 - l1)
      (36028797018963952#64 - l2)
      (36028797018963952#64 - l3)
      (36028797018963952#64 - l4) % p25519 =
    fpNeg (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have hs0 : (36028797018963664#64 - l0).toNat = 36028797018963664 - l0.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l0.toNat ≤ 36028797018963664; omega)]; rfl
  have hs1 : (36028797018963952#64 - l1).toNat = 36028797018963952 - l1.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l1.toNat ≤ 36028797018963952; omega)]; rfl
  have hs2 : (36028797018963952#64 - l2).toNat = 36028797018963952 - l2.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l2.toNat ≤ 36028797018963952; omega)]; rfl
  have hs3 : (36028797018963952#64 - l3).toNat = 36028797018963952 - l3.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l3.toNat ≤ 36028797018963952; omega)]; rfl
  have hs4 : (36028797018963952#64 - l4).toNat = 36028797018963952 - l4.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l4.toNat ≤ 36028797018963952; omega)]; rfl
  have hval :
      fe51Val
        (36028797018963664#64 - l0)
        (36028797018963952#64 - l1)
        (36028797018963952#64 - l2)
        (36028797018963952#64 - l3)
        (36028797018963952#64 - l4) =
      16 * p25519 - fe51Val l0 l1 l2 l3 l4 := by
    unfold fe51Val p25519
    rw [hs0, hs1, hs2, hs3, hs4]
    omega
  rw [hval]
  unfold fpNeg
  have hlt : fe51Val l0 l1 l2 l3 l4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val l0 l1 l2 l3 l4 =
      p25519 * (fe51Val l0 l1 l2 l3 l4 / p25519) + fe51Val l0 l1 l2 l3 l4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val l0 l1 l2 l3 l4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmod_lt : fe51Val l0 l1 l2 l3 l4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmod2 : (fe51Val l0 l1 l2 l3 l4 % p25519) % p25519 = fe51Val l0 l1 l2 l3 l4 % p25519 :=
    Nat.mod_eq_of_lt hmod_lt
  rw [hmod2]
  have hrew : 16 * p25519 - fe51Val l0 l1 l2 l3 l4 =
      (p25519 - fe51Val l0 l1 l2 l3 l4 % p25519) + p25519 * (15 - fe51Val l0 l1 l2 l3 l4 / p25519) := by
    unfold p25519 at hdiv hq hmod_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left]

theorem bv64_add_bias0_sub (a b : BitVec 64) :
    (a + 36028797018963664#64) - b = (a - b) + 36028797018963664#64 := by
  bv_omega

theorem bv64_bias0_add_sub (a b : BitVec 64) :
    (36028797018963664#64 + a) - b = (a - b) + 36028797018963664#64 := by
  bv_omega

private theorem sub_bias0_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963664#64).toNat = a.toNat + 36028797018963664 - b.toNat := by
  bv_omega

private theorem sub_bias1_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963952#64).toNat = a.toNat + 36028797018963952 - b.toNat := by
  bv_omega

/-- Modulo `p25519` identity for biased 5-limb subtraction (`a + 16*p - b`). -/
theorem fe51Sub_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val
      ((a0 - b0) + 36028797018963664#64)
      ((a1 - b1) + 36028797018963952#64)
      ((a2 - b2) + 36028797018963952#64)
      ((a3 - b3) + 36028797018963952#64)
      ((a4 - b4) + 36028797018963952#64) % p25519 =
    fpSub (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have hval :
      fe51Val
        ((a0 - b0) + 36028797018963664#64)
        ((a1 - b1) + 36028797018963952#64)
        ((a2 - b2) + 36028797018963952#64)
        ((a3 - b3) + 36028797018963952#64)
        ((a4 - b4) + 36028797018963952#64) =
      fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val p25519
    rw [sub_bias0_toNat a0 b0 (by omega) (by omega), sub_bias1_toNat a1 b1 (by omega) (by omega),
        sub_bias1_toNat a2 b2 (by omega) (by omega), sub_bias1_toNat a3 b3 (by omega) (by omega),
        sub_bias1_toNat a4 b4 (by omega) (by omega)]
    omega
  rw [hval]
  unfold fpSub
  have hlt : fe51Val b0 b1 b2 b3 b4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val b0 b1 b2 b3 b4 =
      p25519 * (fe51Val b0 b1 b2 b3 b4 / p25519) + fe51Val b0 b1 b2 b3 b4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val b0 b1 b2 b3 b4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmodB_lt : fe51Val b0 b1 b2 b3 b4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmodB : (fe51Val b0 b1 b2 b3 b4 % p25519) % p25519 = fe51Val b0 b1 b2 b3 b4 % p25519 :=
    Nat.mod_eq_of_lt hmodB_lt
  rw [hmodB]
  have hrew : fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 =
      (fe51Val a0 a1 a2 a3 a4 + (p25519 - fe51Val b0 b1 b2 b3 b4 % p25519)) +
        p25519 * (15 - fe51Val b0 b1 b2 b3 b4 / p25519) := by
    unfold p25519 at hdiv hq hmodB_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left, Nat.add_sub_assoc (Nat.le_of_lt hmodB_lt),
      ← Nat.mod_add_mod]

/-- Limb bounds for 5-limb unreduced addition `a + b`. -/
theorem fe51Add_bounded (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) (B : Nat) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧ a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧ b3.toNat < B2 ∧ b4.toNat < B2)
    (hB : decide (B1 + B2 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide) :
    (a0 + b0).toNat < B ∧ (a1 + b1).toNat < B ∧ (a2 + b2).toNat < B ∧
    (a3 + b3).toNat < B ∧ (a4 + b4).toNat < B := by
  have ⟨h1, h2⟩ := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Modulo `p25519` identity for 5-limb unreduced addition `a + b`. -/
theorem fe51Add_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) % p25519 =
    fpAdd (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have h0 : (a0 + b0).toNat = a0.toNat + b0.toNat := by bv_omega
  have h1 : (a1 + b1).toNat = a1.toNat + b1.toNat := by bv_omega
  have h2 : (a2 + b2).toNat = a2.toNat + b2.toNat := by bv_omega
  have h3 : (a3 + b3).toNat = a3.toNat + b3.toNat := by bv_omega
  have h4 : (a4 + b4).toNat = a4.toNat + b4.toNat := by bv_omega
  have hval :
      fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) =
      fe51Val a0 a1 a2 a3 a4 + fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val
    rw [h0, h1, h2, h3, h4]
    omega
  rw [hval]
  unfold fpAdd
  exact Nat.add_mod _ _ _

/-- Limb bounds for 5-limb shift-left by 1 (`2 * a`). -/
theorem fe51Shl1_bounded (a0 a1 a2 a3 a4 : BitVec 64) (B : Nat) {B1 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hB : decide (2 * B1 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide) :
    (a0 <<< 1).toNat < B ∧ (a1 <<< 1).toNat < B ∧ (a2 <<< 1).toNat < B ∧
    (a3 <<< 1).toNat < B ∧ (a4 <<< 1).toNat < B := by
  have ⟨h1, h2⟩ := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Modulo `p25519` identity for 5-limb shift-left by 1 (`2 * a`). -/
theorem fe51Shl1_val_mod (a0 a1 a2 a3 a4 : BitVec 64) {B1 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hB : decide (B1 ≤ 2 ^ 53) = true := by decide) :
    fe51Val (a0 <<< 1) (a1 <<< 1) (a2 <<< 1) (a3 <<< 1) (a4 <<< 1) % p25519 =
    fpAdd (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val a0 a1 a2 a3 a4 % p25519) := by
  have hle : B1 ≤ 2 ^ 53 := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  have h0 : (a0 <<< 1).toNat = 2 * a0.toNat := by bv_omega
  have h1 : (a1 <<< 1).toNat = 2 * a1.toNat := by bv_omega
  have h2 : (a2 <<< 1).toNat = 2 * a2.toNat := by bv_omega
  have h3 : (a3 <<< 1).toNat = 2 * a3.toNat := by bv_omega
  have h4 : (a4 <<< 1).toNat = 2 * a4.toNat := by bv_omega
  have hval :
      fe51Val (a0 <<< 1) (a1 <<< 1) (a2 <<< 1) (a3 <<< 1) (a4 <<< 1) =
      fe51Val a0 a1 a2 a3 a4 + fe51Val a0 a1 a2 a3 a4 := by
    unfold fe51Val
    rw [h0, h1, h2, h3, h4]
    omega
  rw [hval]
  unfold fpAdd
  exact Nat.add_mod _ _ _

theorem fe51_canonical_mod2 (u0 u1 u2 u3 u4 : BitVec 64) :
    ((u0.toNat % 2 ^ 51) + (u1.toNat % 2 ^ 51) * 2 ^ 51 +
      (u2.toNat % 2 ^ 51) * 2 ^ 102 + (u3.toNat % 2 ^ 51) * 2 ^ 153 +
      (u4.toNat % 2 ^ 51) * 2 ^ 204) % 2 =
    u0.toNat % 2 := by omega

theorem mul_mod_eq_fpMul (a b : Nat) :
    (a * b) % p25519 = fpMul (a % p25519) (b % p25519) := by
  unfold fpMul
  rw [Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]

/-! ## 4. `SepWP` Byte-Window Focus/Unfocus & Stack Combinators -/

theorem sepWP_have_slice_prop {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {p : BitVec 64} {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (Q : List (BitVec 8) → Prop)
    (hQ : Q bs)
    (hwp : Q bs → SepWP prog target_pc s (P ∗ (p ↦ₛ bs)) post) :
    SepWP prog target_pc s (P ∗ (p ↦ₛ bs)) post :=
  hwp hQ

theorem sub_ofNat64_add (sp : BitVec 64) (a b : Nat) (h : b ≤ a := by decide) :
    sp - BitVec.ofNat 64 a + BitVec.ofNat 64 b = sp - BitVec.ofNat 64 (a - b) := by
  have : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [this, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem le_length_of_hasLenGe {bs : List (BitVec 8)} {k m : Nat}
    [h : HasLenGe bs m] (hd : decide (k ≤ m) = true := by decide) :
    k ≤ bs.length :=
  Nat.le_trans (of_decide_eq_true hd) h.le_length

@[expose] def pointsToBytesRest (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat) : SepProp :=
  (base ↦ₛ buf.take off) ∗ ((base + BitVec.ofNat 64 (off + n)) ↦ₛ buf.drop (off + n))

@[expose] def pointsToBytesRest2 (base : BitVec 64) (buf : List (BitVec 8))
    (off1 n1 off2 n2 : Nat) : SepProp :=
  if off2 + n2 ≤ off1 then
    pointsToBytesRest base (buf.take off1) off2 n2 ∗
      ((base + BitVec.ofNat 64 (off1 + n1)) ↦ₛ buf.drop (off1 + n1))
  else
    (base ↦ₛ buf.take off1) ∗
      pointsToBytesRest (base + BitVec.ofNat 64 (off1 + n1)) (buf.drop (off1 + n1))
        (off2 - (off1 + n1)) n2

theorem pointsToBytesRest_focus_ro (base ptr2 : BitVec 64) (buf : List (BitVec 8))
    (off1 n1 off2 n2 : Nat)
    (hptr2 : ptr2 = base + BitVec.ofNat 64 off2)
    (hlen1 : off1 + n1 ≤ buf.length)
    (hlen2 : off2 + n2 ≤ buf.length)
    (hdisj : off2 + n2 ≤ off1 ∨ off1 + n1 ≤ off2) :
    pointsToBytesRest base buf off1 n1 =
      (ptr2 ↦ₛ ProofLib.ByteSlice.slice buf off2 n2) ∗
      pointsToBytesRest2 base buf off1 n1 off2 n2 := by
  unfold pointsToBytesRest pointsToBytesRest2
  subst hptr2
  by_cases hle : off2 + n2 ≤ off1
  · simp only [hle, ↓reduceIte]
    have htake_len : off2 + n2 ≤ (buf.take off1).length := by simp [List.length_take]; omega
    have h1 : (base ↦ₛ buf.take off1) =
        ((base + BitVec.ofNat 64 off2) ↦ₛ ProofLib.ByteSlice.slice (buf.take off1) off2 n2) ∗
        pointsToBytesRest base (buf.take off1) off2 n2 :=
      pointsToBytes_focus base (buf.take off1) off2 n2 htake_len
    have hsl : ProofLib.ByteSlice.slice (buf.take off1) off2 n2 = ProofLib.ByteSlice.slice buf off2 n2 := by
      simp only [ProofLib.ByteSlice.slice, List.drop_take, List.take_take]
      rw [Nat.min_eq_left (by omega)]
    rw [h1, hsl, sepConj_assoc]
  · simp only [hle, ↓reduceIte]
    have hge : off1 + n1 ≤ off2 := by omega
    have hdrop_len : (off2 - (off1 + n1)) + n2 ≤ (buf.drop (off1 + n1)).length := by
      simp [List.length_drop]; omega
    have h1 : ((base + BitVec.ofNat 64 (off1 + n1)) ↦ₛ buf.drop (off1 + n1)) =
        ((base + BitVec.ofNat 64 (off1 + n1) + BitVec.ofNat 64 (off2 - (off1 + n1))) ↦ₛ
          ProofLib.ByteSlice.slice (buf.drop (off1 + n1)) (off2 - (off1 + n1)) n2) ∗
        pointsToBytesRest (base + BitVec.ofNat 64 (off1 + n1)) (buf.drop (off1 + n1))
          (off2 - (off1 + n1)) n2 :=
      pointsToBytes_focus (base + BitVec.ofNat 64 (off1 + n1)) (buf.drop (off1 + n1))
        (off2 - (off1 + n1)) n2 hdrop_len
    have haddr : base + BitVec.ofNat 64 (off1 + n1) + BitVec.ofNat 64 (off2 - (off1 + n1)) =
        base + BitVec.ofNat 64 off2 := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show off1 + n1 + (off2 - (off1 + n1)) = off2 by omega]
    have hsl : ProofLib.ByteSlice.slice (buf.drop (off1 + n1)) (off2 - (off1 + n1)) n2 =
        ProofLib.ByteSlice.slice buf off2 n2 := by
      simp only [ProofLib.ByteSlice.slice, List.drop_drop,
        show off1 + n1 + (off2 - (off1 + n1)) = off2 by omega]
    rw [h1, haddr, hsl, ← sepConj_assoc, sepConj_comm (base ↦ₛ buf.take off1), sepConj_assoc]

theorem sepWP_focus_bytes (base ptr : BitVec 64) (off n : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ buf) ∗ P := by sep_frame)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : (ProofLib.ByteSlice.slice buf off n).length = n →
      SepWP prog target_pc s
        (((ptr ↦ₛ ProofLib.ByteSlice.slice buf off n) ∗
          pointsToBytesRest base buf off n) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  have hfocus : (base ↦ₛ buf) =
      (ptr ↦ₛ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRest base buf off n := by
    subst hptr
    exact pointsToBytes_focus base buf off n hlen
  rw [hfocus]
  exact hnext (ByteSlice.slice_length buf off n hlen)

theorem sepWP_unfocus_bytes (base ptr : BitVec 64) (off n : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      ((ptr ↦ₛ ProofLib.ByteSlice.slice buf off n) ∗
       pointsToBytesRest base buf off n) ∗ P := by sep_frame)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : SepWP prog target_pc s ((base ↦ₛ buf) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  have hunfocus :
      ((ptr ↦ₛ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRest base buf off n) =
      (base ↦ₛ buf) := by
    subst hptr
    exact (pointsToBytes_focus base buf off n hlen).symm
  rw [hunfocus]
  exact hnext

theorem sepWP_write_bytes (base ptr : BitVec 64) (src : List (BitVec 8)) (off n m : Nat)
    (hn : src.length = n)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      ((ptr ↦ₛ src) ∗ pointsToBytesRest base buf off n) ∗ P := by sep_frame)
    (hbuf : m ≤ buf.length := by exact le_length_of_hasLenGe)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : m ≤ (ByteSlice.write buf off src).length →
      SepWP prog target_pc s ((base ↦ₛ ByteSlice.write buf off src) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  have hwrite :
      ((ptr ↦ₛ src) ∗ pointsToBytesRest base buf off n) =
      (base ↦ₛ ByteSlice.write buf off src) := by
    subst hptr
    exact pointsToBytes_write_len base buf src off n hn hlen
  rw [hwrite]
  exact hnext ((ByteSlice.write_length buf src off (hn ▸ hlen)).symm ▸ hbuf)

theorem sepWP_focus2_ro_bytes (base ptr2 : BitVec 64) (off1 n1 off2 n2 : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = pointsToBytesRest base buf off1 n1 ∗ P := by sep_frame)
    (hlen1 : off1 + n1 ≤ buf.length := by exact le_length_of_hasLenGe)
    (hlen2 : off2 + n2 ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr2 : ptr2 = base + BitVec.ofNat 64 off2 := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hdisj : off2 + n2 ≤ off1 ∨ off1 + n1 ≤ off2 := by decide)
    (hnext : (ProofLib.ByteSlice.slice buf off2 n2).length = n2 →
      SepWP prog target_pc s
        (((ptr2 ↦ₛ ProofLib.ByteSlice.slice buf off2 n2) ∗
          pointsToBytesRest2 base buf off1 n1 off2 n2) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsToBytesRest_focus_ro base ptr2 buf off1 n1 off2 n2 hptr2 hlen1 hlen2 hdisj]
  exact hnext (ByteSlice.slice_length buf off2 n2 hlen2)

theorem sepWP_unfocus2_ro_bytes (base ptr2 : BitVec 64) (off1 n1 off2 n2 : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      ((ptr2 ↦ₛ ProofLib.ByteSlice.slice buf off2 n2) ∗
       pointsToBytesRest2 base buf off1 n1 off2 n2) ∗ P := by sep_frame)
    (hlen1 : off1 + n1 ≤ buf.length := by exact le_length_of_hasLenGe)
    (hlen2 : off2 + n2 ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr2 : ptr2 = base + BitVec.ofNat 64 off2 := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hdisj : off2 + n2 ≤ off1 ∨ off1 + n1 ≤ off2 := by decide)
    (hnext : SepWP prog target_pc s (pointsToBytesRest base buf off1 n1 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, (pointsToBytesRest_focus_ro base ptr2 buf off1 n1 off2 n2 hptr2 hlen1 hlen2 hdisj).symm]
  exact hnext

theorem sepWP_norm_stackFrame {prog : Program} {target_pc : BitVec 64}
    {s : State} {spVal : BitVec 64} (n : Nat) {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp : s.sp = spVal)
    (hf : Full = stackFrame s n ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (spVal - BitVec.ofNat 64 n) n ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  change SepWP prog target_pc s (memRegion (s.sp - BitVec.ofNat 64 n) n ∗ P) post oom
  rw [hsp]
  exact hnext

theorem sepWP_abstract_bytes (ptr : BitVec 64) {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (Q : List (BitVec 8) → Prop)
    (hf : Full = (ptr ↦ₛ buf) ∗ P := by sep_frame)
    (hQ : Q buf)
    (hnext : ∀ (buf' : List (BitVec 8)), Q buf' →
      SepWP prog target_pc s ((ptr ↦ₛ buf') ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  exact hnext buf hQ

theorem slice_length' (bs : List (BitVec 8)) (off m : Nat) {n : Nat}
    [h : HasLenGe bs n]
    (h1 : decide (off + m ≤ n) = true := by decide) :
    (ProofLib.ByteSlice.slice bs off m).length = m :=
  ByteSlice.slice_length bs off m (Nat.le_trans (of_decide_eq_true h1) h.le_length)

theorem fe51LimbsBounded_slice_of_at {bs : List (BitVec 8)} {off b1 : Nat} (b2 : Nat) {n : Nat}
    [hlen : HasLenGe bs n]
    (h : fe51LimbsBoundedAt bs off b1)
    (hoff : decide (off + 40 ≤ n) = true := by decide)
    (hb : decide (b1 ≤ b2) = true := by decide) :
    fe51LimbsBounded (ProofLib.ByteSlice.slice bs off 40) b2 := by
  have hle : b1 ≤ b2 := of_decide_eq_true hb
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  refine ⟨slice_length' bs off 40 hoff, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readLE_slice_eq bs off 40 0 (by decide), Nat.add_zero]; omega
  · rw [readLE_slice_eq bs off 40 8 (by decide)]; omega
  · rw [readLE_slice_eq bs off 40 16 (by decide)]; omega
  · rw [readLE_slice_eq bs off 40 24 (by decide)]; omega
  · rw [readLE_slice_eq bs off 40 32 (by decide)]; omega

theorem fe51ValOfBytes_slice (bs : List (BitVec 8)) (off : Nat) :
    fe51ValOfBytes (ProofLib.ByteSlice.slice bs off 40) = fe51ValAt bs off := by
  unfold fe51ValOfBytes fe51ValAt
  simp (disch := decide) only [readLE_slice_eq, Nat.add_zero]

theorem fold_fe51ValOfBytes (bs : List (BitVec 8)) :
    fe51Val (ByteSlice.readLE bs 0 8) (ByteSlice.readLE bs 8 8)
      (ByteSlice.readLE bs 16 8) (ByteSlice.readLE bs 24 8) (ByteSlice.readLE bs 32 8) =
    fe51ValOfBytes bs := rfl

theorem fold_fe51ValAt (bs : List (BitVec 8)) (off : Nat) :
    fe51Val (ByteSlice.readLE bs off 8) (ByteSlice.readLE bs (off + 8) 8)
      (ByteSlice.readLE bs (off + 16) 8) (ByteSlice.readLE bs (off + 24) 8)
      (ByteSlice.readLE bs (off + 32) 8) =
    fe51ValAt bs off := rfl

theorem sepWP_split_stack_callee (calleeBytes frameBytes : Nat)
    {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = stackFrame s0 (calleeBytes + frameBytes) ∗ P := by sep_frame)
    (h : calleeBytes + frameBytes ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s0
      ((memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 frameBytes - BitVec.ofNat 64 calleeBytes) calleeBytes) ∗ P)
      post oom) :
    SepWP prog target_pc s0 Full post oom := by
  rw [hf]
  change SepWP prog target_pc s0 (stackAt s0.sp (calleeBytes + frameBytes) ∗ P) post oom
  rw [stackAt_region s0.sp calleeBytes frameBytes h, sepConj_comm (stackAt _ _) (memRegion _ _)]
  exact hnext

theorem sepWP_merge_stack_callee (calleeBytes frameBytes : Nat)
    {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes ∗
      memRegion (s0.sp - BitVec.ofNat 64 frameBytes - BitVec.ofNat 64 calleeBytes) calleeBytes) ∗ P := by sep_frame)
    (h : calleeBytes + frameBytes ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (stackFrame s0 (calleeBytes + frameBytes) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, sepConj_comm (memRegion _ frameBytes) _]
  change SepWP prog target_pc s
    ((stackAt (s0.sp - BitVec.ofNat 64 frameBytes) calleeBytes ∗ memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes) ∗ P) post oom
  rw [← stackAt_region s0.sp calleeBytes frameBytes h]
  exact hnext

theorem sepWP_have_bytes (ptr : BitVec 64) {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (Q : List (BitVec 8) → Prop)
    (_hf : Full = (ptr ↦ₛ buf) ∗ P := by sep_frame)
    (hQ : Q buf)
    (hnext : Q buf → SepWP prog target_pc s Full post oom) :
    SepWP prog target_pc s Full post oom :=
  hnext hQ

theorem sepWP_peel_stack_bytes (sp : BitVec 64) (off n rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - BitVec.ofNat 64 off) off ∗ P := by sep_frame)
    (hoff : off = n + rem := by decide)
    (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : ∀ bs : List (BitVec 8), bs.length = n →
      SepWP prog target_pc s
        ((((sp - BitVec.ofNat 64 off) ↦ₛ bs) ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by
    rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit : memRegion (sp - BitVec.ofNat 64 off) off =
      memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem := by
    have h1 := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb)
    rw [← hoff, haddr] at h1
    exact h1
  rw [hf, hsplit, sepConj_assoc]
  exact SepWP.memRegion_bytes (sp - BitVec.ofNat 64 off) n (by omega) rfl (fun bs hbs => by
    rw [← sepConj_assoc]; exact hnext bs hbs)

theorem sepWP_unpeel_stack_bytes (sp : BitVec 64) (off n rem : Nat)
    {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - BitVec.ofNat 64 off) ↦ₛ bs) ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P := by sep_frame)
    (hbs : bs.length = n := by assumption)
    (hoff : off = n + rem := by decide)
    (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - BitVec.ofNat 64 off) off ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by
    rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit : memRegion (sp - BitVec.ofNat 64 off) off =
      memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem := by
    have h1 := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb)
    rw [← hoff, haddr] at h1
    exact h1
  rw [hf]
  refine SepWP.weaken_pre (sepConj_mono_left ?_) hnext
  rw [hsplit]
  refine sepConj_mono_left ?_
  rw [← hbs]
  exact pointsToBytes_entails_memRegion _ _

theorem sepWP_callee_grow (base : BitVec 64) (big small diff : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (base - BitVec.ofNat 64 small) small ∗ stackAt (base - BitVec.ofNat 64 small) diff) ∗ P := by sep_frame)
    (hsum : diff + small = big := by decide)
    (hb : diff + small ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (base - BitVec.ofNat 64 big) big ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region base diff small hb]
  change SepWP prog target_pc s (memRegion (base - BitVec.ofNat 64 (diff + small)) (diff + small) ∗ P) post oom
  rw [hsum]
  exact hnext

theorem sepWP_callee_shrink (base : BitVec 64) (big small diff : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (base - BitVec.ofNat 64 big) big ∗ P := by sep_frame)
    (hsum : diff + small = big := by decide)
    (hb : diff + small ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s
      ((memRegion (base - BitVec.ofNat 64 small) small ∗ stackAt (base - BitVec.ofNat 64 small) diff) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, ← hsum]
  change SepWP prog target_pc s (stackAt base (diff + small) ∗ P) post oom
  rw [stackAt_region base diff small hb, sepConj_comm (stackAt _ _) (memRegion _ _)]
  exact hnext

theorem sepWP_callee_224_to_400 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 512#64 - 224#64) 224 ∗ stackAt (sp - 512#64 - 224#64) 176) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp - 512#64 - 400#64) 400 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp - 512#64) 176 224 (by decide)]
  exact hnext

theorem sepWP_callee_400_to_224 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 512#64 - 400#64) 400 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s
      ((memRegion (sp - 512#64 - 224#64) 224 ∗ stackAt (sp - 512#64 - 224#64) 176) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  change SepWP prog target_pc s (stackAt (sp - 512#64) (176 + 224) ∗ P) post oom
  rw [stackAt_region (sp - 512#64) 176 224 (by decide), sepConj_comm (stackAt _ _) (memRegion _ _)]
  exact hnext

/-! ## 5. Curve-Model Epilogue, 160-Byte Split/Merge, & Cell Decomposition Helpers -/

theorem fe51_write5_add_post (s a_bs : List (BitVec 8)) (hs : s.length = 40)
    (h0 : fe51LimbsBoundedAt a_bs 0 (2 ^ 53))
    (h40 : fe51LimbsBoundedAt a_bs 40 (2 ^ 53)) :
    let buf :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        (ByteSlice.write64 (ByteSlice.write64 s
          0 (ByteSlice.readLE a_bs 0 8 + ByteSlice.readLE a_bs 40 8))
          8 (ByteSlice.readLE a_bs 8 8 + ByteSlice.readLE a_bs 48 8))
          16 (ByteSlice.readLE a_bs 16 8 + ByteSlice.readLE a_bs 56 8))
          24 (ByteSlice.readLE a_bs 24 8 + ByteSlice.readLE a_bs 64 8))
          32 (ByteSlice.readLE a_bs 32 8 + ByteSlice.readLE a_bs 72 8)
    fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_bs 0 % p25519) (fe51ValAt a_bs 40 % p25519) := by
  haveI : HasLenGe s 40 := ⟨by omega⟩
  unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
  simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hs, Nat.min_eq_left]
  exact ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) h0 h40⟩,
    fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ h0 h40⟩

theorem fe51_write5_sub_reduce_post (s a_bs : List (BitVec 8)) (hs : s.length = 40)
    (h0 : fe51LimbsBoundedAt a_bs 0 (2 ^ 53))
    (h40 : fe51LimbsBoundedAt a_bs 40 (2 ^ 53)) :
    let d0 := (ByteSlice.readLE a_bs 40 8 + 36028797018963664#64) - ByteSlice.readLE a_bs 0 8
    let d1 := (ByteSlice.readLE a_bs 48 8 - ByteSlice.readLE a_bs 8 8) + 36028797018963952#64
    let d2 := (ByteSlice.readLE a_bs 56 8 - ByteSlice.readLE a_bs 16 8) + 36028797018963952#64
    let d3 := (ByteSlice.readLE a_bs 64 8 - ByteSlice.readLE a_bs 24 8) + 36028797018963952#64
    let d4 := (ByteSlice.readLE a_bs 72 8 - ByteSlice.readLE a_bs 32 8) + 36028797018963952#64
    let buf :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        (ByteSlice.write64 (ByteSlice.write64 s
          0 ((d0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64))
          8 ((d1 &&& 2251799813685247#64) + (d0 >>> 51)))
          32 ((d4 &&& 2251799813685247#64) + (d3 >>> 51)))
          16 ((d2 &&& 2251799813685247#64) + (d1 >>> 51)))
          24 ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
    fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_bs 40 % p25519) (fe51ValAt a_bs 0 % p25519) := by
  haveI : HasLenGe s 40 := ⟨by omega⟩
  unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
  simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hs, Nat.min_eq_left]
  refine ⟨⟨trivial, fe51Reduce_bounded54 _ _ _ _ _⟩, ?_⟩
  rw [fe51Reduce_val_mod, bv64_add_bias0_sub, fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ h40 h0]

theorem edAddNiels_epilogue_post (a_3 w w_1 w_2 : List (BitVec 8))
    (z0 z1 z2 z3 z4 : BitVec 64)
    (PP MM TT2d ZZ : Nat)
    (ha3 : a_3.length = 160)
    (hw : fe51LimbsBounded w (2 ^ 52))
    (hw1 : fe51LimbsBounded w_1 (2 ^ 52))
    (hw2 : fe51LimbsBounded w_2 (2 ^ 52))
    (hz : z0.toNat < 2 ^ 52 ∧ z1.toNat < 2 ^ 52 ∧ z2.toNat < 2 ^ 52 ∧
      z3.toNat < 2 ^ 52 ∧ z4.toNat < 2 ^ 52)
    (hPP : fe51ValOfBytes w % p25519 = PP)
    (hMM : fe51ValOfBytes w_1 % p25519 = MM)
    (hTT2d : fe51ValOfBytes w_2 % p25519 = TT2d)
    (hZZ : fe51Val z0 z1 z2 z3 z4 % p25519 = ZZ) :
    let dx0 := (ByteSlice.readLE w 0 8 + 36028797018963664#64) - ByteSlice.readLE w_1 0 8
    let dx1 := (ByteSlice.readLE w 8 8 - ByteSlice.readLE w_1 8 8) + 36028797018963952#64
    let dx2 := (ByteSlice.readLE w 16 8 - ByteSlice.readLE w_1 16 8) + 36028797018963952#64
    let dx3 := (ByteSlice.readLE w 24 8 - ByteSlice.readLE w_1 24 8) + 36028797018963952#64
    let dx4 := (ByteSlice.readLE w 32 8 - ByteSlice.readLE w_1 32 8) + 36028797018963952#64
    let rx0 := (dx0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (dx4 >>> 51)) * 19#64
    let rx1 := (dx1 &&& 2251799813685247#64) + (dx0 >>> 51)
    let rx2 := (dx2 &&& 2251799813685247#64) + (dx1 >>> 51)
    let rx3 := (dx3 &&& 2251799813685247#64) + (dx2 >>> 51)
    let rx4 := (dx4 &&& 2251799813685247#64) + (dx3 >>> 51)
    let ry0 := ByteSlice.readLE w_1 0 8 + ByteSlice.readLE w 0 8
    let ry1 := ByteSlice.readLE w_1 8 8 + ByteSlice.readLE w 8 8
    let ry2 := ByteSlice.readLE w_1 16 8 + ByteSlice.readLE w 16 8
    let ry3 := ByteSlice.readLE w_1 24 8 + ByteSlice.readLE w 24 8
    let ry4 := ByteSlice.readLE w_1 32 8 + ByteSlice.readLE w 32 8
    let zz0 := z0 <<< 1
    let zz1 := z1 <<< 1
    let zz2 := z2 <<< 1
    let zz3 := z3 <<< 1
    let zz4 := z4 <<< 1
    let rz0 := ByteSlice.readLE w_2 0 8 + zz0
    let rz1 := ByteSlice.readLE w_2 8 8 + zz1
    let rz2 := ByteSlice.readLE w_2 16 8 + zz2
    let rz3 := ByteSlice.readLE w_2 24 8 + zz3
    let rz4 := ByteSlice.readLE w_2 32 8 + zz4
    let dt0 := (zz0 + 36028797018963664#64) - ByteSlice.readLE w_2 0 8
    let dt1 := (zz1 - ByteSlice.readLE w_2 8 8) + 36028797018963952#64
    let dt2 := (zz2 - ByteSlice.readLE w_2 16 8) + 36028797018963952#64
    let dt3 := (zz3 - ByteSlice.readLE w_2 24 8) + 36028797018963952#64
    let dt4 := (zz4 - ByteSlice.readLE w_2 32 8) + 36028797018963952#64
    let rt0 := (dt0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (dt4 >>> 51)) * 19#64
    let rt1 := (dt1 &&& 2251799813685247#64) + (dt0 >>> 51)
    let rt2 := (dt2 &&& 2251799813685247#64) + (dt1 >>> 51)
    let rt3 := (dt3 &&& 2251799813685247#64) + (dt2 >>> 51)
    let rt4 := (dt4 &&& 2251799813685247#64) + (dt3 >>> 51)
    let res_bs :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        a_3 32 rx4) 40 ry0) 16 rx2) 24 rx3) 48 ry1) 56 ry2) 0 rx0) 8 rx1) 64 ry3) 72 ry4)
        96 rz2) 104 rz3) 80 rz0) 88 rz1) 112 rz4) 120 rt0) 128 rt1) 136 rt2) 144 rt3) 152 rt4
    res_bs.length = 160 ∧
    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
    fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
    fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
    edExtOfBytes res_bs =
      ⟨fpSub PP MM, fpAdd MM PP, fpAdd TT2d (fpAdd ZZ ZZ), fpSub (fpAdd ZZ ZZ) TT2d⟩ := by
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  have haddY_b := fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 53) hw1.2 hw.2
  have haddY_v := fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw1.2 hw.2
  have hshl_b := fe51Shl1_bounded _ _ _ _ _ (2 ^ 53) hz
  have hshl_v := fe51Shl1_val_mod _ _ _ _ _ hz
  have haddZ_b := fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hw2.2 hshl_b
  have haddZ_v := fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw2.2 hshl_b
  unfold fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
    write64_length_eq, ha3, Nat.min_eq_left]
  refine ⟨trivial, fe51Reduce_bounded _ _ _ _ _, haddY_b, haddZ_b,
    fe51Reduce_bounded _ _ _ _ _, ?_⟩
  rw [fe51Reduce_val_mod, fe51Reduce_val_mod,
      bv64_add_bias0_sub, bv64_add_bias0_sub,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw.2 hw1.2,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hshl_b hw2.2,
      haddY_v, haddZ_v, hshl_v,
      fold_fe51ValOfBytes w, fold_fe51ValOfBytes w_1, fold_fe51ValOfBytes w_2,
      hPP, hMM, hTT2d, hZZ]

theorem edSubNiels_epilogue_post (a_3 w w_1 w_2 : List (BitVec 8))
    (z0 z1 z2 z3 z4 : BitVec 64)
    (PP MM TT2d ZZ : Nat)
    (ha3 : a_3.length = 160)
    (hw : fe51LimbsBounded w (2 ^ 52))
    (hw1 : fe51LimbsBounded w_1 (2 ^ 52))
    (hw2 : fe51LimbsBounded w_2 (2 ^ 52))
    (hz : z0.toNat < 2 ^ 52 ∧ z1.toNat < 2 ^ 52 ∧ z2.toNat < 2 ^ 52 ∧
      z3.toNat < 2 ^ 52 ∧ z4.toNat < 2 ^ 52)
    (hPP : fe51ValOfBytes w % p25519 = PP)
    (hMM : fe51ValOfBytes w_1 % p25519 = MM)
    (hTT2d : fe51ValOfBytes w_2 % p25519 = TT2d)
    (hZZ : fe51Val z0 z1 z2 z3 z4 % p25519 = ZZ) :
    let dx0 := (ByteSlice.readLE w 0 8 + 36028797018963664#64) - ByteSlice.readLE w_1 0 8
    let dx1 := (ByteSlice.readLE w 8 8 - ByteSlice.readLE w_1 8 8) + 36028797018963952#64
    let dx2 := (ByteSlice.readLE w 16 8 - ByteSlice.readLE w_1 16 8) + 36028797018963952#64
    let dx3 := (ByteSlice.readLE w 24 8 - ByteSlice.readLE w_1 24 8) + 36028797018963952#64
    let dx4 := (ByteSlice.readLE w 32 8 - ByteSlice.readLE w_1 32 8) + 36028797018963952#64
    let rx0 := (dx0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (dx4 >>> 51)) * 19#64
    let rx1 := (dx1 &&& 2251799813685247#64) + (dx0 >>> 51)
    let rx2 := (dx2 &&& 2251799813685247#64) + (dx1 >>> 51)
    let rx3 := (dx3 &&& 2251799813685247#64) + (dx2 >>> 51)
    let rx4 := (dx4 &&& 2251799813685247#64) + (dx3 >>> 51)
    let ry0 := ByteSlice.readLE w_1 0 8 + ByteSlice.readLE w 0 8
    let ry1 := ByteSlice.readLE w_1 8 8 + ByteSlice.readLE w 8 8
    let ry2 := ByteSlice.readLE w_1 16 8 + ByteSlice.readLE w 16 8
    let ry3 := ByteSlice.readLE w_1 24 8 + ByteSlice.readLE w 24 8
    let ry4 := ByteSlice.readLE w_1 32 8 + ByteSlice.readLE w 32 8
    let zz0 := z0 <<< 1
    let zz1 := z1 <<< 1
    let zz2 := z2 <<< 1
    let zz3 := z3 <<< 1
    let zz4 := z4 <<< 1
    let dz0 := (zz0 + 36028797018963664#64) - ByteSlice.readLE w_2 0 8
    let dz1 := (zz1 - ByteSlice.readLE w_2 8 8) + 36028797018963952#64
    let dz2 := (zz2 - ByteSlice.readLE w_2 16 8) + 36028797018963952#64
    let dz3 := (zz3 - ByteSlice.readLE w_2 24 8) + 36028797018963952#64
    let dz4 := (zz4 - ByteSlice.readLE w_2 32 8) + 36028797018963952#64
    let rz0 := (dz0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (dz4 >>> 51)) * 19#64
    let rz1 := (dz1 &&& 2251799813685247#64) + (dz0 >>> 51)
    let rz2 := (dz2 &&& 2251799813685247#64) + (dz1 >>> 51)
    let rz3 := (dz3 &&& 2251799813685247#64) + (dz2 >>> 51)
    let rz4 := (dz4 &&& 2251799813685247#64) + (dz3 >>> 51)
    let rt0 := ByteSlice.readLE w_2 0 8 + zz0
    let rt1 := ByteSlice.readLE w_2 8 8 + zz1
    let rt2 := ByteSlice.readLE w_2 16 8 + zz2
    let rt3 := ByteSlice.readLE w_2 24 8 + zz3
    let rt4 := ByteSlice.readLE w_2 32 8 + zz4
    let res_bs :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        a_3 0 rx0) 8 rx1) 16 rx2) 24 rx3) 48 ry1) 56 ry2) 64 ry3) 72 ry4) 32 rx4) 40 ry0)
        80 rz0) 88 rz1) 128 rt1) 136 rt2) 96 rz2) 104 rz3) 112 rz4) 120 rt0) 144 rt3) 152 rt4
    res_bs.length = 160 ∧
    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
    fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
    fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
    edExtOfBytes res_bs =
      ⟨fpSub PP MM, fpAdd MM PP, fpSub (fpAdd ZZ ZZ) TT2d, fpAdd TT2d (fpAdd ZZ ZZ)⟩ := by
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  have haddY_b := fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 53) hw1.2 hw.2
  have haddY_v := fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw1.2 hw.2
  have hshl_b := fe51Shl1_bounded _ _ _ _ _ (2 ^ 53) hz
  have hshl_v := fe51Shl1_val_mod _ _ _ _ _ hz
  have haddT_b := fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hw2.2 hshl_b
  have haddT_v := fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw2.2 hshl_b
  unfold fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
    write64_length_eq, ha3, Nat.min_eq_left]
  refine ⟨trivial, fe51Reduce_bounded _ _ _ _ _, haddY_b,
    fe51Reduce_bounded _ _ _ _ _, haddT_b, ?_⟩
  rw [fe51Reduce_val_mod, fe51Reduce_val_mod,
      bv64_add_bias0_sub, bv64_add_bias0_sub,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw.2 hw1.2,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hshl_b hw2.2,
      haddY_v, haddT_v, hshl_v,
      fold_fe51ValOfBytes w, fold_fe51ValOfBytes w_1, fold_fe51ValOfBytes w_2,
      hPP, hMM, hTT2d, hZZ]

theorem readLE_append_left (xs ys : List (BitVec 8)) (off n : Nat) (h : off + n ≤ xs.length) :
    ByteSlice.readLE (xs ++ ys) off n = ByteSlice.readLE xs off n := by
  apply ByteSlice.readLE_congr; intro i hi
  have hlt : off + i < xs.length := by omega
  simp only [List.getD, List.getElem?_append_left hlt]

theorem readLE_append_right (xs ys : List (BitVec 8)) (off n : Nat) (h : xs.length ≤ off) :
    ByteSlice.readLE (xs ++ ys) off n = ByteSlice.readLE ys (off - xs.length) n := by
  apply readLE_congr_off; intro i _hi
  have hle : xs.length ≤ off + i := by omega
  simp only [List.getD, List.getElem?_append_right hle,
    show off + i - xs.length = off - xs.length + i by omega]

theorem edAsExtended_of_append4 (w0 w1 w2 w3 : List (BitVec 8)) (C : EdExtPoint)
    (hw0 : fe51LimbsBounded w0 (2 ^ 52))
    (hw1 : fe51LimbsBounded w1 (2 ^ 52))
    (hw2 : fe51LimbsBounded w2 (2 ^ 52))
    (hw3 : fe51LimbsBounded w3 (2 ^ 52))
    (hv0 : fe51ValOfBytes w0 % p25519 = fpMul C.X C.T)
    (hv1 : fe51ValOfBytes w1 % p25519 = fpMul C.Y C.Z)
    (hv2 : fe51ValOfBytes w2 % p25519 = fpMul C.Z C.T)
    (hv3 : fe51ValOfBytes w3 % p25519 = fpMul C.X C.Y) :
    let res := w0 ++ (w1 ++ (w2 ++ w3))
    res.length = 160 ∧
    fe51LimbsBoundedAt res 0 (2 ^ 52) ∧
    fe51LimbsBoundedAt res 40 (2 ^ 52) ∧
    fe51LimbsBoundedAt res 80 (2 ^ 52) ∧
    fe51LimbsBoundedAt res 120 (2 ^ 52) ∧
    edExtOfBytes res = edAsExtended C := by
  have hw0_l := hw0.1; have hw1_l := hw1.1; have hw2_l := hw2.1; have hw3_l := hw3.1
  have hlen : (w0 ++ (w1 ++ (w2 ++ w3))).length = 160 := by
    simp [List.length_append, hw0_l, hw1_l, hw2_l, hw3_l]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w0 off 8 :=
    readLE_append_left w0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w1 (off - 40) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_left w1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w2 (off - 80) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_right w1 _ (off - 40) 8 (by omega), hw1_l,
        show off - 40 - 40 = off - 80 by omega,
        readLE_append_left w2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w3 (off - 120) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_right w1 _ (off - 40) 8 (by omega), hw1_l,
        readLE_append_right w2 _ (off - 40 - 40) 8 (by omega), hw2_l,
        show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51LimbsBoundedAt edExtOfBytes fe51ValAt edAsExtended
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceSub,
    fold_fe51ValOfBytes w0, fold_fe51ValOfBytes w1, fold_fe51ValOfBytes w2, fold_fe51ValOfBytes w3]
  exact ⟨hlen, hw0.2, hw1.2, hw2.2, hw3.2, by rw [hv0, hv1, hv2, hv3]⟩

theorem edProjDouble_mod (X Y Z : Nat) :
    edProjDouble X Y Z = edProjDouble (X % p25519) (Y % p25519) (Z % p25519) := by
  unfold edProjDouble; simp only [Nat.mod_mod]

theorem fe51_mul_post_props (w : List (BitVec 8)) (V : Nat)
    {a b : List (BitVec 8)} {va vb : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes a * fe51ValOfBytes b) % p25519 := by assumption)
    (ha : fe51ValOfBytes a % p25519 = va := by assumption)
    (hbv : fe51ValOfBytes b % p25519 = vb := by assumption)
    (hV : fpMul va vb = V := by rfl) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = V := by
  refine ⟨hb.1, hb, ?_⟩
  unfold fpMul at hV
  rw [hv, Nat.mul_mod, ha, hbv, Nat.mul_mod]; exact hV

theorem proj_copy15_prologue_post (s src : List (BitVec 8))
    (hs : s.length = 120)
    (h0 : fe51LimbsBoundedAt src 0 (2 ^ 53))
    (h40 : fe51LimbsBoundedAt src 40 (2 ^ 53))
    (h80 : fe51LimbsBoundedAt src 80 (2 ^ 54)) :
    let buf :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        s 40 (ByteSlice.readLE src 40 8)) 48 (ByteSlice.readLE src 48 8))
        56 (ByteSlice.readLE src 56 8)) 64 (ByteSlice.readLE src 64 8))
        32 (ByteSlice.readLE src 32 8)) 80 (ByteSlice.readLE src 80 8))
        88 (ByteSlice.readLE src 88 8)) 96 (ByteSlice.readLE src 96 8))
        104 (ByteSlice.readLE src 104 8)) 112 (ByteSlice.readLE src 112 8))
        0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
        16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8))
        72 (ByteSlice.readLE src 72 8)
    buf.length = 120 ∧
    fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
    fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧
    fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
    edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) =
      edProjDouble (edExtOfBytes src).X (edExtOfBytes src).Y (edExtOfBytes src).Z := by
  haveI : HasLenGe s 120 := ⟨by omega⟩
  unfold fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
    write64_length_eq, hs, Nat.min_eq_left]
  exact ⟨trivial, h0, h40, h80, edProjDouble_mod _ _ _⟩

theorem proj_copy15_loop_post (s wX wY wZ : List (BitVec 8))
    (VX VY VZ : Nat)
    (hs : s.length = 120)
    (hwX : fe51LimbsBounded wX (2 ^ 52))
    (hwY : fe51LimbsBounded wY (2 ^ 52))
    (hwZ : fe51LimbsBounded wZ (2 ^ 52))
    (hVX : fe51ValOfBytes wX % p25519 = VX)
    (hVY : fe51ValOfBytes wY % p25519 = VY)
    (hVZ : fe51ValOfBytes wZ % p25519 = VZ) :
    let buf :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        s 64 (ByteSlice.readLE wY 24 8)) 72 (ByteSlice.readLE wY 32 8))
        80 (ByteSlice.readLE wZ 0 8)) 88 (ByteSlice.readLE wZ 8 8))
        96 (ByteSlice.readLE wZ 16 8)) 104 (ByteSlice.readLE wZ 24 8))
        112 (ByteSlice.readLE wZ 32 8)) 0 (ByteSlice.readLE wX 0 8))
        8 (ByteSlice.readLE wX 8 8)) 16 (ByteSlice.readLE wX 16 8))
        24 (ByteSlice.readLE wX 24 8)) 32 (ByteSlice.readLE wX 32 8))
        40 (ByteSlice.readLE wY 0 8)) 48 (ByteSlice.readLE wY 8 8))
        56 (ByteSlice.readLE wY 16 8)
    buf.length = 120 ∧
    fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
    fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧
    fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
    edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) =
      edProjDouble VX VY VZ := by
  haveI : HasLenGe s 120 := ⟨by omega⟩
  obtain ⟨_, hx0, hx1, hx2, hx3, hx4⟩ := hwX
  obtain ⟨_, hy0, hy1, hy2, hy3, hy4⟩ := hwY
  obtain ⟨_, hz0, hz1, hz2, hz3, hz4⟩ := hwZ
  unfold fe51LimbsBoundedAt
  simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
    write64_length_eq, hs, Nat.min_eq_left]
  refine ⟨trivial,
    ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
  rw [edProjDouble_mod, fold_fe51ValOfBytes wX, fold_fe51ValOfBytes wY, fold_fe51ValOfBytes wZ,
      hVX, hVY, hVZ]

theorem completed_split4_props (bs : List (BitVec 8)) (C : EdExtPoint)
    (hbs : bs.length = 160)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 52))
    (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 53))
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 52))
    (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 52))
    (hval : edExtOfBytes bs = C) :
    let b0 := bs.take 40
    let b1 := (bs.drop 40).take 40
    let b2 := ((bs.drop 40).drop 40).take 40
    let b3 := ((bs.drop 40).drop 40).drop 40
    fe51LimbsBounded b0 (2 ^ 54) ∧
    fe51LimbsBounded b1 (2 ^ 54) ∧
    fe51LimbsBounded b2 (2 ^ 54) ∧
    fe51LimbsBounded b3 (2 ^ 54) ∧
    fe51ValOfBytes b0 % p25519 = C.X ∧
    fe51ValOfBytes b1 % p25519 = C.Y ∧
    fe51ValOfBytes b2 % p25519 = C.Z ∧
    fe51ValOfBytes b3 % p25519 = C.T := by
  intro b0 b1 b2 b3
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hbs]
  have hb2_l : b2.length = 40 := by simp [b2, hbs]
  have hb3_l : b3.length = 40 := by simp [b3, hbs]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    have e0 : b0 ++ bs.drop 40 = bs := List.take_append_drop 40 bs
    have e1 : b1 ++ (bs.drop 40).drop 40 = bs.drop 40 := List.take_append_drop 40 (bs.drop 40)
    have e2 : b2 ++ b3 = (bs.drop 40).drop 40 := List.take_append_drop 40 ((bs.drop 40).drop 40)
    rw [e2, e1, e0]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_right b1 _ (off - 40) 8 (by omega), hb1_l,
        show off - 40 - 40 = off - 80 by omega,
        readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_right b1 _ (off - 40) 8 (by omega), hb1_l,
        readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l,
        show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51LimbsBoundedAt at h0 h40 h80 h120
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0 h40 h80 h120
  have hval' : edExtOfBytes bs =
      ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
       fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub,
      fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, fold_fe51ValOfBytes b3]
  rw [hval] at hval'
  obtain ⟨h0_0, h0_1, h0_2, h0_3, h0_4⟩ := h0
  obtain ⟨h1_0, h1_1, h1_2, h1_3, h1_4⟩ := h40
  obtain ⟨h2_0, h2_1, h2_2, h2_3, h2_4⟩ := h80
  obtain ⟨h3_0, h3_1, h3_2, h3_3, h3_4⟩ := h120
  refine ⟨⟨hb0_l, by omega, by omega, by omega, by omega, by omega⟩,
         ⟨hb1_l, by omega, by omega, by omega, by omega, by omega⟩,
         ⟨hb2_l, by omega, by omega, by omega, by omega, by omega⟩,
         ⟨hb3_l, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
  rw [hval']; exact ⟨rfl, rfl, rfl, rfl⟩

theorem completed_split4_props_54 (bs : List (BitVec 8)) (C : EdExtPoint)
    (hpt : fe51Point4Bounded bs (2 ^ 54)) (hval : edExtOfBytes bs = C) :
    let b0 := bs.take 40
    let b1 := (bs.drop 40).take 40
    let b2 := ((bs.drop 40).drop 40).take 40
    let b3 := ((bs.drop 40).drop 40).drop 40
    fe51LimbsBounded b0 (2 ^ 54) ∧
    fe51LimbsBounded b1 (2 ^ 54) ∧
    fe51LimbsBounded b2 (2 ^ 54) ∧
    fe51LimbsBounded b3 (2 ^ 54) ∧
    fe51ValOfBytes b0 % p25519 = C.X ∧
    fe51ValOfBytes b1 % p25519 = C.Y ∧
    fe51ValOfBytes b2 % p25519 = C.Z ∧
    fe51ValOfBytes b3 % p25519 = C.T := by
  obtain ⟨hbs, h0, h40, h80, h120⟩ := hpt
  intro b0 b1 b2 b3
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hbs]
  have hb2_l : b2.length = 40 := by simp [b2, hbs]
  have hb3_l : b3.length = 40 := by simp [b3, hbs]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    have e0 : b0 ++ bs.drop 40 = bs := List.take_append_drop 40 bs
    have e1 : b1 ++ (bs.drop 40).drop 40 = bs.drop 40 := List.take_append_drop 40 (bs.drop 40)
    have e2 : b2 ++ b3 = (bs.drop 40).drop 40 := List.take_append_drop 40 ((bs.drop 40).drop 40)
    rw [e2, e1, e0]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_right b1 _ (off - 40) 8 (by omega), hb1_l,
        show off - 40 - 40 = off - 80 by omega,
        readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l,
        readLE_append_right b1 _ (off - 40) 8 (by omega), hb1_l,
        readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l,
        show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51LimbsBoundedAt at h0 h40 h80 h120
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0 h40 h80 h120
  have hval' : edExtOfBytes bs =
      ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
       fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub,
      fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, fold_fe51ValOfBytes b3]
  rw [hval] at hval'
  exact ⟨⟨hb0_l, h0⟩, ⟨hb1_l, h40⟩, ⟨hb2_l, h80⟩, ⟨hb3_l, h120⟩, by rw [hval']; exact ⟨rfl, rfl, rfl, rfl⟩⟩

theorem sepWP_split4_160 (base : BitVec 64)
    {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = 160 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s
        (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) ∗
          ((base + 80#64) ↦ₛ b2) ∗ ((base + 120#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40
  have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40
  have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : (base ↦ₛ bs) = (base ↦ₛ bs.take 40) ∗ ((base + 40#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs]; rfl
  have hs1 : ((base + 40#64) ↦ₛ d1) = ((base + 40#64) ↦ₛ d1.take 40) ∗ ((base + 80#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1,
        show base + 40#64 + BitVec.ofNat 64 (min 40 120) = base + 80#64 by rw [BitVec.add_assoc]; rfl]
  have hs2 : ((base + 80#64) ↦ₛ d2) = ((base + 80#64) ↦ₛ d2.take 40) ∗ ((base + 120#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2,
        show base + 80#64 + BitVec.ofNat 64 (min 40 80) = base + 120#64 by rw [BitVec.add_assoc]; rfl]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

theorem sepWP_merge4_160 (base : BitVec 64)
    {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (Q : List (BitVec 8) → Prop)
    (hf : Full = (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) ∗
                   ((base + 80#64) ↦ₛ b2) ∗ ((base + 120#64) ↦ₛ b3)) ∗ P) := by sep_frame)
    (h0 : b0.length = 40 := by assumption)
    (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption)
    (hQ : Q (b0 ++ (b1 ++ (b2 ++ b3))))
    (hnext : ∀ res_bs : List (BitVec 8), Q res_bs →
      SepWP prog target_pc s (((base ↦ₛ res_bs) ∗ P)) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : (base ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      (base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) ∗
      ((base + 80#64) ↦ₛ b2) ∗ ((base + 120#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, h0, show BitVec.ofNat 64 40 = 40#64 by rfl,
        pointsToBytes_append, h1, show base + 40#64 + BitVec.ofNat 64 40 = base + 80#64 by
          rw [BitVec.add_assoc]; rfl,
        pointsToBytes_append, h2, show base + 80#64 + BitVec.ofNat 64 40 = base + 120#64 by
          rw [BitVec.add_assoc]; rfl]
  rw [hf, ← hm]
  exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) hQ

theorem sepWP_merge4_stack_bytes (sp : BitVec 64)
    {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗
                  ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption)
    (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption)
    (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 →
      SepWP prog target_pc s (((sp - 224#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 144#64 + BitVec.ofNat 64 b2.length = sp - 104#64 := by
    rw [h2]; exact sub_ofNat64_add sp 144 40
  have ha1 : sp - 184#64 + BitVec.ofNat 64 b1.length = sp - 144#64 := by
    rw [h1]; exact sub_ofNat64_add sp 184 40
  have ha0 : sp - 224#64 + BitVec.ofNat 64 b0.length = sp - 184#64 := by
    rw [h0]; exact sub_ofNat64_add sp 224 40
  have hm : ((sp - 224#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗
      ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]
  exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

theorem sepWP_merge4_stack_512 (sp : BitVec 64)
    {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 512#64) ↦ₛ b0) ∗ ((sp - 472#64) ↦ₛ b1) ∗
                  ((sp - 432#64) ↦ₛ b2) ∗ ((sp - 392#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption)
    (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption)
    (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 →
      SepWP prog target_pc s (((sp - 512#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 432#64 + BitVec.ofNat 64 b2.length = sp - 392#64 := by
    rw [h2]; exact sub_ofNat64_add sp 432 40
  have ha1 : sp - 472#64 + BitVec.ofNat 64 b1.length = sp - 432#64 := by
    rw [h1]; exact sub_ofNat64_add sp 472 40
  have ha0 : sp - 512#64 + BitVec.ofNat 64 b0.length = sp - 472#64 := by
    rw [h0]; exact sub_ofNat64_add sp 512 40
  have hm : ((sp - 512#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 512#64) ↦ₛ b0) ∗ ((sp - 472#64) ↦ₛ b1) ∗
      ((sp - 432#64) ↦ₛ b2) ∗ ((sp - 392#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]
  exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

theorem sepWP_split4_completed_224 (sp : BitVec 64) (C : EdExtPoint)
    {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 224#64) ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 52) := by assumption)
    (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 53) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 52) := by assumption)
    (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 52) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) →
      fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) →
      fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X →
      fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z →
      fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s
        ((((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗
          ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40
  have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40
  have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 224#64) ↦ₛ bs) = ((sp - 224#64) ↦ₛ bs.take 40) ∗ ((sp - 184#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 224 40]
  have hs1 : ((sp - 184#64) ↦ₛ d1) = ((sp - 184#64) ↦ₛ d1.take 40) ∗ ((sp - 144#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 184 40]
  have hs2 : ((sp - 144#64) ↦ₛ d2) = ((sp - 144#64) ↦ₛ d2.take 40) ∗ ((sp - 104#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 144 40]
  obtain ⟨hb0, hb1, hb2, hb3, hv0, hv1, hv2, hv3⟩ :=
    completed_split4_props bs C hbs h0 h40 h80 h120 hval
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    hb0.1 hb1.1 hb2.1 hb3.1 hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3

theorem sepWP_split4_completed_512 (sp : BitVec 64) (C : EdExtPoint)
    {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 512#64) ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 52) := by assumption)
    (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 53) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 52) := by assumption)
    (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 52) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) →
      fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) →
      fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X →
      fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z →
      fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s
        ((((sp - 512#64) ↦ₛ b0) ∗ ((sp - 472#64) ↦ₛ b1) ∗
          ((sp - 432#64) ↦ₛ b2) ∗ ((sp - 392#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40
  have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40
  have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 512#64) ↦ₛ bs) = ((sp - 512#64) ↦ₛ bs.take 40) ∗ ((sp - 472#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 512 40]
  have hs1 : ((sp - 472#64) ↦ₛ d1) = ((sp - 472#64) ↦ₛ d1.take 40) ∗ ((sp - 432#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 472 40]
  have hs2 : ((sp - 432#64) ↦ₛ d2) = ((sp - 432#64) ↦ₛ d2.take 40) ∗ ((sp - 392#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp 432 40]
  obtain ⟨hb0, hb1, hb2, hb3, hv0, hv1, hv2, hv3⟩ :=
    completed_split4_props bs C hbs h0 h40 h80 h120 hval
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    hb0.1 hb1.1 hb2.1 hb3.1 hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3

theorem pointsToBytes40_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40) :
    (a ↦ₛ bs) = (a ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((a + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
      ((a + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((a + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
      ((a + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8) := by
  rw [pointsToBytes_take_drop a 8 bs (by omega), pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by simp [h]),
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 ((bs.drop 8).drop 8) (by simp [h]),
      pointsToBytes_take_drop (a + 8#64 + 8#64 + 8#64) 8 (((bs.drop 8).drop 8).drop 8) (by simp [h])]
  simp only [List.drop_drop, BitVec.add_assoc]
  rw [show bs.take 8 = (bs.drop 0).take 8 from rfl,
      show bs.drop 32 = (bs.drop 32).take 8 from (List.take_of_length_le (by simp [h])).symm,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (by omega), pointsToBytes_take8_eq_pointsTo64 _ bs 8 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 16 (by omega), pointsToBytes_take8_eq_pointsTo64 _ bs 24 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 32 (by omega)]
  simp only [ByteSlice.pack64_eq_readLE_8]; rfl

theorem pointsToBytesRO40_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40) :
    (a ↦ᵣ bs) = (a ↦₆₄ᵣ ByteSlice.readLE bs 0 8) ∗ ((a + 8#64) ↦₆₄ᵣ ByteSlice.readLE bs 8 8) ∗
      ((a + 16#64) ↦₆₄ᵣ ByteSlice.readLE bs 16 8) ∗ ((a + 24#64) ↦₆₄ᵣ ByteSlice.readLE bs 24 8) ∗
      ((a + 32#64) ↦₆₄ᵣ ByteSlice.readLE bs 32 8) := by
  rw [pointsToBytesRO_take_drop a 8 bs (by omega), pointsToBytesRO_take_drop (a + 8#64) 8 (bs.drop 8) (by simp [h]),
      pointsToBytesRO_take_drop (a + 8#64 + 8#64) 8 ((bs.drop 8).drop 8) (by simp [h]),
      pointsToBytesRO_take_drop (a + 8#64 + 8#64 + 8#64) 8 (((bs.drop 8).drop 8).drop 8) (by simp [h])]
  simp only [List.drop_drop, BitVec.add_assoc]
  rw [show bs.take 8 = (bs.drop 0).take 8 from rfl,
      show bs.drop 32 = (bs.drop 32).take 8 from (List.take_of_length_le (by simp [h])).symm,
      pointsToBytesRO_take8_eq_pointsTo64RO _ bs 0 (by omega), pointsToBytesRO_take8_eq_pointsTo64RO _ bs 8 (by omega),
      pointsToBytesRO_take8_eq_pointsTo64RO _ bs 16 (by omega), pointsToBytesRO_take8_eq_pointsTo64RO _ bs 24 (by omega),
      pointsToBytesRO_take8_eq_pointsTo64RO _ bs 32 (by omega)]
  simp only [ByteSlice.pack64_eq_readLE_8]; rfl

theorem pointsToBytes32_eq_cells64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) = (a ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((a + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
      ((a + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((a + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8) := by
  rw [pointsToBytes_take_drop a 8 bs (by omega), pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by simp [h]),
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 ((bs.drop 8).drop 8) (by simp [h])]
  simp only [List.drop_drop, BitVec.add_assoc]
  rw [show bs.take 8 = (bs.drop 0).take 8 from rfl,
      show bs.drop 24 = (bs.drop 24).take 8 from (List.take_of_length_le (by simp [h])).symm,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (by omega), pointsToBytes_take8_eq_pointsTo64 _ bs 8 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 16 (by omega), pointsToBytes_take8_eq_pointsTo64 _ bs 24 (by omega)]
  simp only [ByteSlice.pack64_eq_readLE_8]; rfl

theorem pointsTo64_eq_cells8 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₈ v.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ v.extractLsb' 8 8) ∗ ((a + 2#64) ↦₈ v.extractLsb' 16 8) ∗
      ((a + 3#64) ↦₈ v.extractLsb' 24 8) ∗ ((a + 4#64) ↦₈ v.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ v.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ v.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ v.extractLsb' 56 8) := by
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc]; rfl

/-! ## 6. `modPowLoop` / `modPow` / `fpPow` Bridges -/

private theorem beq_false_of_ne' {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  beq_false_of_ne h

theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne' h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, show 2 * (exp / 2) = exp by omega, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', show (2 * (exp / 2)).succ = exp by omega]

theorem modPow_eq_pow_mod (base exp m : Nat) (he : exp < 2 ^ 256) :
    modPow base exp m = base ^ exp % m := by
  unfold modPow
  rw [modPowLoop_eq 256 (base % m) exp m 1 he, Nat.one_mul, ← Nat.pow_mod base exp m]

theorem modPow_mod_eq_pow_mod (base exp m : Nat) (he : exp < 2 ^ 256) :
    modPow (base % m) exp m = base ^ exp % m := by
  unfold modPow
  rw [Nat.mod_mod, modPowLoop_eq 256 (base % m) exp m 1 he, Nat.one_mul, ← Nat.pow_mod base exp m]

theorem fpPow_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) : fpPow a e = a ^ e % p25519 :=
  modPow_eq_pow_mod a e p25519 he

theorem fpPow_mod_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) :
    fpPow (a % p25519) e = a ^ e % p25519 :=
  modPow_mod_eq_pow_mod a e p25519 he

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
