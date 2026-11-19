/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Abi.Aapcs
import ProofLib.BV.Bits
import ProofLib.Invariant
import ProofLib.Lemmas
import ProofLib.SepLogic
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Solver
import ProofLib.SepLogic.WP

/-!
# Shared Layout Bridges, Register State & 128-Bit Step Rules for `decrypt_par::<15, U17>`

Auxiliary definitions and lemmas for `BlockDecPar17`:
1. Bidirectional byte-slice bridges between `blocks17At ptr blks`, `blocks17Bytes blks`, and
   `(ptr ↦ₛ bs)` (`bs.length = 272`).
2. Round-by-round unfolding of `armv8Decrypt15` and `armv8DecryptPar17` over the 17-block
   SIMD register assignment `Par17Regs`.
3. `Par17Anchor` (preserving all GPRs `x0..x30`, `sp`, `q8..q15`, and `PureStepPreserved`),
   fast state-normalization lemmas, and direct `↦₁₂₈` SIMD load/store step rules (`step_ldr128`,
   `step_ldp128`, `step_str128_perm`, `step_stp128_perm`).
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (u32OfBytesLE bytesToU32LE u128OfU32sLE bytesToU128LE u128ToBytesLE
   evalAesOp_aesd_comm evalAesOp_aesimc_vd_irrel
   armv8Decrypt15 armv8DecryptPar17 blocks17Bytes blocks17At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

public section

/-! ## 1. Little-Endian 128-Bit & 17-Block Byte Bridges -/

/-- Parse 272 bytes (`17 × 16` B) into 17 little-endian `u128` blocks. -/
@[expose] def bytesToBlocks17 (bs : List (BitVec 8)) : Vector (BitVec 128) 17 :=
  Vector.ofFn fun i : Fin 17 => bytesToU128LE ((bs.drop (16 * i.val)).take 16)

@[simp] theorem u128ToBytesLE_length (v : BitVec 128) : (u128ToBytesLE v).length = 16 := by
  simp [u128ToBytesLE]

theorem pointsTo128_eq_pointsToBytes_u128ToBytesLE (p : BitVec 64) (v : BitVec 128) :
    (p ↦₁₂₈ v) = (p ↦ₛ u128ToBytesLE v) := by
  rw [pointsTo128_split64 p v, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  have hlen : (unpack64 (v.extractLsb' 0 64)).length = 8 := by simp [unpack64]
  rw [show p + 8#64 = p + BitVec.ofNat 64 (unpack64 (v.extractLsb' 0 64)).length by rw [hlen],
      ← pointsToBytes_append]
  congr 1
  simp only [unpack64, u128ToBytesLE, List.ofFn_succ, Fin.val_zero, Fin.val_succ, List.ofFn_zero,
    List.cons_append, List.nil_append]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < 16 := by simpa using h1
  interval_cases i <;> (ext j hj; simp [← Nat.add_assoc]; omega)

private theorem bytesToU128LE_u128ToBytesLE_words (v : BitVec 128) :
    u32OfBytesLE (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8) (v.extractLsb' 24 8) = v.extractLsb' 0 32 ∧
    u32OfBytesLE (v.extractLsb' 32 8) (v.extractLsb' 40 8) (v.extractLsb' 48 8) (v.extractLsb' 56 8) = v.extractLsb' 32 32 ∧
    u32OfBytesLE (v.extractLsb' 64 8) (v.extractLsb' 72 8) (v.extractLsb' 80 8) (v.extractLsb' 88 8) = v.extractLsb' 64 32 ∧
    u32OfBytesLE (v.extractLsb' 96 8) (v.extractLsb' 104 8) (v.extractLsb' 112 8) (v.extractLsb' 120 8) = v.extractLsb' 96 32 ∧
    u128OfU32sLE (v.extractLsb' 0 32) (v.extractLsb' 32 32) (v.extractLsb' 64 32) (v.extractLsb' 96 32) = v := by
  dsimp only [u32OfBytesLE, u128OfU32sLE]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem bytesToU128LE_u128ToBytesLE (v : BitVec 128) :
    bytesToU128LE (u128ToBytesLE v) = v := by
  dsimp only [bytesToU128LE, bytesToU32LE, u128ToBytesLE]
  simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, List.ofFn_zero, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMul]
  obtain ⟨h0, h1, h2, h3, h4⟩ := bytesToU128LE_u128ToBytesLE_words v
  rw [h0, h1, h2, h3, h4]

private theorem u128OfU32sLE_extract32 (w0 w1 w2 w3 : BitVec 32) :
    (u128OfU32sLE w0 w1 w2 w3).extractLsb' 0 32 = w0 ∧
    (u128OfU32sLE w0 w1 w2 w3).extractLsb' 32 32 = w1 ∧
    (u128OfU32sLE w0 w1 w2 w3).extractLsb' 64 32 = w2 ∧
    (u128OfU32sLE w0 w1 w2 w3).extractLsb' 96 32 = w3 := by
  dsimp only [u128OfU32sLE]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem u32OfBytesLE_extract8 (b0 b1 b2 b3 : BitVec 8) :
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 0 8 = b0 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 8 8 = b1 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 16 8 = b2 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 24 8 = b3 := by
  dsimp only [u32OfBytesLE]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem extract8_of_extract32 (v : BitVec 128) (a b c : Nat)
    (hb : b + 8 ≤ 32) (hc : a + b = c) (w : BitVec 32) (hw : v.extractLsb' a 32 = w) :
    v.extractLsb' c 8 = w.extractLsb' b 8 := by
  subst hc hw
  ext j hj
  have hbj : b + j < 32 := by omega
  simp [hbj, ← Nat.add_assoc]

theorem u128ToBytesLE_bytesToU128LE {bs : List (BitVec 8)} (h : bs.length = 16) :
    u128ToBytesLE (bytesToU128LE bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at h
  simp only [bytesToU128LE, bytesToU32LE, Nat.zero_add, Nat.reduceAdd, List.getD_cons_zero,
    List.getD_cons_succ, u128ToBytesLE, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
    List.ofFn_zero, Nat.reduceMul]
  obtain ⟨hw0, hw1, hw2, hw3⟩ := u128OfU32sLE_extract32
    (u32OfBytesLE b0 b1 b2 b3) (u32OfBytesLE b4 b5 b6 b7)
    (u32OfBytesLE b8 b9 b10 b11) (u32OfBytesLE b12 b13 b14 b15)
  obtain ⟨e0, e1, e2, e3⟩ := u32OfBytesLE_extract8 b0 b1 b2 b3
  obtain ⟨e4, e5, e6, e7⟩ := u32OfBytesLE_extract8 b4 b5 b6 b7
  obtain ⟨e8, e9, e10, e11⟩ := u32OfBytesLE_extract8 b8 b9 b10 b11
  obtain ⟨e12, e13, e14, e15⟩ := u32OfBytesLE_extract8 b12 b13 b14 b15
  rw [extract8_of_extract32 _ 0 0 0 (by decide) rfl _ hw0, e0,
      extract8_of_extract32 _ 0 8 8 (by decide) rfl _ hw0, e1,
      extract8_of_extract32 _ 0 16 16 (by decide) rfl _ hw0, e2,
      extract8_of_extract32 _ 0 24 24 (by decide) rfl _ hw0, e3,
      extract8_of_extract32 _ 32 0 32 (by decide) rfl _ hw1, e4,
      extract8_of_extract32 _ 32 8 40 (by decide) rfl _ hw1, e5,
      extract8_of_extract32 _ 32 16 48 (by decide) rfl _ hw1, e6,
      extract8_of_extract32 _ 32 24 56 (by decide) rfl _ hw1, e7,
      extract8_of_extract32 _ 64 0 64 (by decide) rfl _ hw2, e8,
      extract8_of_extract32 _ 64 8 72 (by decide) rfl _ hw2, e9,
      extract8_of_extract32 _ 64 16 80 (by decide) rfl _ hw2, e10,
      extract8_of_extract32 _ 64 24 88 (by decide) rfl _ hw2, e11,
      extract8_of_extract32 _ 96 0 96 (by decide) rfl _ hw3, e12,
      extract8_of_extract32 _ 96 8 104 (by decide) rfl _ hw3, e13,
      extract8_of_extract32 _ 96 16 112 (by decide) rfl _ hw3, e14,
      extract8_of_extract32 _ 96 24 120 (by decide) rfl _ hw3, e15]

private theorem vector17_toList (v : Vector (BitVec 128) 17) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8],
                v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16]] := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < 17 := by simpa using h1
  interval_cases i <;> rfl

private theorem length_flatten16 {α β : Type _} (l : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = 16) : (l.map f).flatten.length = 16 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [hf x, ih]; omega

private theorem drop_take_flatten16 {α β : Type _} (l : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = 16) :
    ∀ (i : Nat) (hi : i < l.length),
      ((l.map f).flatten.drop (16 * i)).take 16 = f l[i] := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero =>
      rw [Nat.mul_zero, List.drop_zero, List.map_cons, List.flatten_cons, ← hf x, List.take_left]
      rfl
    | succ i' =>
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      rw [List.map_cons, List.flatten_cons,
          show 16 * (i' + 1) = (f x).length + 16 * i' by rw [hf x]; omega,
          ← List.drop_drop, List.drop_left]
      exact ih i' hi'

private theorem flatten_chunks16 :
    ∀ (n : Nat) (bs : List (BitVec 8)), bs.length = 16 * n →
      (List.ofFn fun i : Fin n => (bs.drop (16 * i.val)).take 16).flatten = bs := by
  intro n
  induction n with
  | zero => intro bs h; simp [List.eq_nil_of_length_eq_zero h]
  | succ n ih =>
    intro bs h
    rw [List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.mul_zero, List.drop_zero]
    have hdrop : (bs.drop 16).length = 16 * n := by simp [h]; omega
    have htail : (List.ofFn fun i : Fin n => (bs.drop (16 * i.succ.val)).take 16) =
        (List.ofFn fun i : Fin n => ((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1; funext i; rw [List.drop_drop, Fin.val_succ]; congr 2; omega
    rw [htail, ih (bs.drop 16) hdrop, List.take_append_drop]

private theorem toList_ofFn_map {α β : Type _} {n : Nat} (f : Fin n → α) (g : α → β) :
    (Vector.ofFn f).toList.map g = List.ofFn (fun i : Fin n => g (f i)) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem blocks17Bytes_length (blks : Vector (BitVec 128) 17) :
    (blocks17Bytes blks).length = 272 := by
  rw [blocks17Bytes, length_flatten16 blks.toList u128ToBytesLE u128ToBytesLE_length]
  simp

theorem blocks17At_eq_pointsToBytes (ptr : BitVec 64) (blks : Vector (BitVec 128) 17) :
    blocks17At ptr blks = (ptr ↦ₛ blocks17Bytes blks) := by
  rw [blocks17At, blocks17Bytes, vector17_toList blks]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    pointsTo128_eq_pointsToBytes_u128ToBytesLE, pointsToBytes_append, u128ToBytesLE_length,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem blocks17Bytes_bytesToBlocks17 {bs : List (BitVec 8)} (h : bs.length = 272) :
    blocks17Bytes (bytesToBlocks17 bs) = bs := by
  rw [blocks17Bytes, bytesToBlocks17, toList_ofFn_map]
  have hfn : (fun i : Fin 17 => u128ToBytesLE (bytesToU128LE ((bs.drop (16 * i.val)).take 16))) =
      (fun i : Fin 17 => (bs.drop (16 * i.val)).take 16) := by
    funext i
    exact u128ToBytesLE_bytesToU128LE (by simp [h]; omega)
  exact (congrArg (fun f => (List.ofFn f).flatten) hfn).trans (flatten_chunks16 17 bs (by omega))

theorem bytesToBlocks17_blocks17Bytes (blks : Vector (BitVec 128) 17) :
    bytesToBlocks17 (blocks17Bytes blks) = blks := by
  refine Vector.ext fun i hi => ?_
  simp only [bytesToBlocks17, blocks17Bytes, Vector.getElem_ofFn]
  rw [drop_take_flatten16 blks.toList u128ToBytesLE u128ToBytesLE_length i (by simpa using hi)]
  simp [bytesToU128LE_u128ToBytesLE]

theorem pointsToBytes_eq_blocks17At {bs : List (BitVec 8)} (ptr : BitVec 64) (h : bs.length = 272) :
    (ptr ↦ₛ bs) = blocks17At ptr (bytesToBlocks17 bs) := by
  rw [blocks17At_eq_pointsToBytes, blocks17Bytes_bytesToBlocks17 h]

/-! ## 2. Pure Round Unfolding & `Par17Regs` State -/

@[expose] def decRound (rk blk : BitVec 128) : BitVec 128 :=
  evalAesOp .AESIMC 0#128 (evalAesOp .AESD rk blk)

@[expose] def decFinish (rk13 rk14 blk : BitVec 128) : BitVec 128 :=
  rk14 ^^^ evalAesOp .AESD rk13 blk

theorem decRound_machine (rk blk : BitVec 128) :
    evalAesOp .AESIMC 0#128 (evalAesOp .AESD blk rk) = decRound rk blk := by
  rw [evalAesOp_aesd_comm]; rfl

theorem decFinish_machine (rk13 rk14 blk : BitVec 128) :
    rk14 ^^^ evalAesOp .AESD blk rk13 = decFinish rk13 rk14 blk := by
  rw [evalAesOp_aesd_comm]; rfl

theorem armv8Decrypt15_eq_rounds (dk : Vector (BitVec 128) 15) (blk : BitVec 128) :
    armv8Decrypt15 dk blk =
      decFinish dk[13] dk[14]
        (decRound dk[12] (decRound dk[11] (decRound dk[10] (decRound dk[9]
          (decRound dk[8] (decRound dk[7] (decRound dk[6] (decRound dk[5]
            (decRound dk[4] (decRound dk[3] (decRound dk[2] (decRound dk[1]
              (decRound dk[0] blk))))))))))))) := by
  rfl

/-- Explicit 17-block SIMD state corresponding to registers
    `(v2, v1, v0, v24, v23, v20, v21, v22, v19, v18, v17, v16, v7, v6, v3, v4, v5)`. -/
structure Par17Regs where
  b0  : BitVec 128
  b1  : BitVec 128
  b2  : BitVec 128
  b3  : BitVec 128
  b4  : BitVec 128
  b5  : BitVec 128
  b6  : BitVec 128
  b7  : BitVec 128
  b8  : BitVec 128
  b9  : BitVec 128
  b10 : BitVec 128
  b11 : BitVec 128
  b12 : BitVec 128
  b13 : BitVec 128
  b14 : BitVec 128
  b15 : BitVec 128
  b16 : BitVec 128

@[expose] def Par17Regs.ofVector (blks : Vector (BitVec 128) 17) : Par17Regs :=
  ⟨blks[0], blks[1], blks[2], blks[3], blks[4], blks[5], blks[6], blks[7], blks[8],
   blks[9], blks[10], blks[11], blks[12], blks[13], blks[14], blks[15], blks[16]⟩

@[expose] def Par17Regs.toVector (r : Par17Regs) : Vector (BitVec 128) 17 :=
  #v[r.b0, r.b1, r.b2, r.b3, r.b4, r.b5, r.b6, r.b7, r.b8,
     r.b9, r.b10, r.b11, r.b12, r.b13, r.b14, r.b15, r.b16]

@[expose] def Par17Regs.map (f : BitVec 128 → BitVec 128) (r : Par17Regs) : Par17Regs :=
  ⟨f r.b0, f r.b1, f r.b2, f r.b3, f r.b4, f r.b5, f r.b6, f r.b7, f r.b8,
   f r.b9, f r.b10, f r.b11, f r.b12, f r.b13, f r.b14, f r.b15, f r.b16⟩

@[expose] def Par17Regs.step (rk : BitVec 128) (r : Par17Regs) : Par17Regs :=
  r.map (decRound rk)

@[expose] def Par17Regs.rounds12 (dk : Vector (BitVec 128) 15) (r : Par17Regs) : Par17Regs :=
  (((((((((((r.step dk[0]).step dk[1]).step dk[2]).step dk[3]).step dk[4]).step dk[5]).step dk[6]).step dk[7]).step dk[8]).step dk[9]).step dk[10]).step dk[11]

theorem Par17Regs.toVector_ofVector (blks : Vector (BitVec 128) 17) :
    (Par17Regs.ofVector blks).toVector = blks := by
  refine Vector.ext fun i hi => ?_
  interval_cases i <;> rfl

theorem Par17Regs.toVector_map (f : BitVec 128 → BitVec 128) (r : Par17Regs) :
    (r.map f).toVector = r.toVector.map f := by
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_map]
  interval_cases i <;> rfl

theorem Par17Regs.toVector_finish_rounds12 (dk : Vector (BitVec 128) 15)
    (blks : Vector (BitVec 128) 17) :
    (((Par17Regs.ofVector blks).rounds12 dk).map
      (fun x => decFinish dk[13] dk[14] (decRound dk[12] x))).toVector =
      armv8DecryptPar17 dk blks := by
  ext i hi
  simp only [Par17Regs.rounds12, Par17Regs.step, Par17Regs.toVector_map,
    Par17Regs.toVector_ofVector, armv8DecryptPar17, Vector.getElem_map, armv8Decrypt15_eq_rounds]

/-- Register-file match for the 17 active block SIMD registers. -/
@[expose] def Par17Regs.holds (r : Par17Regs) (s : State) : Prop :=
  s.readVReg128 2#5  = r.b0  ∧ s.readVReg128 1#5  = r.b1  ∧ s.readVReg128 0#5  = r.b2  ∧
  s.readVReg128 24#5 = r.b3  ∧ s.readVReg128 23#5 = r.b4  ∧ s.readVReg128 20#5 = r.b5  ∧
  s.readVReg128 21#5 = r.b6  ∧ s.readVReg128 22#5 = r.b7  ∧ s.readVReg128 19#5 = r.b8  ∧
  s.readVReg128 18#5 = r.b9  ∧ s.readVReg128 17#5 = r.b10 ∧ s.readVReg128 16#5 = r.b11 ∧
  s.readVReg128 7#5  = r.b12 ∧ s.readVReg128 6#5  = r.b13 ∧ s.readVReg128 3#5  = r.b14 ∧
  s.readVReg128 4#5  = r.b15 ∧ s.readVReg128 5#5  = r.b16

/-! ## 3. Invariant Anchor (`Par17Anchor`), Fast State Simps & Direct `↦₁₂₈` Step Rules -/

@[expose] def simdCalleeProj (s : State) :=
  (s.readVReg128 8#5, s.readVReg128 9#5, s.readVReg128 10#5, s.readVReg128 11#5,
   s.readVReg128 12#5, s.readVReg128 13#5, s.readVReg128 14#5, s.readVReg128 15#5)

/-- Full frame of CPU and OS state preserved across `decrypt_par::<15, U17>`:
    every GPR `x0..x30`, `sp`, `q8..q15` (`d8..d15`), and `PureStepPreserved`. -/
structure Par17Anchor (s0 s : State) : Prop where
  regs : s.regs = s0.regs
  sp   : s.sp = s0.sp
  simd : simdCalleeProj s = simdCalleeProj s0
  pres : PureStepPreserved s0 s

theorem Par17Anchor.refl (s0 : State) : Par17Anchor s0 s0 :=
  ⟨rfl, rfl, rfl, PureStepPreserved.refl s0⟩

theorem Par17Anchor.readReg64 {s0 s : State} (ha : Par17Anchor s0 s) (r : Reg) :
    s.readReg64 r = s0.readReg64 r := by
  cases r <;> simp [State.readReg64, ha.regs, ha.sp]

theorem Par17Anchor.readVReg128_callee {s0 s : State} (ha : Par17Anchor s0 s) :
    s.readVReg128 8#5  = s0.readVReg128 8#5  ∧ s.readVReg128 9#5  = s0.readVReg128 9#5  ∧
    s.readVReg128 10#5 = s0.readVReg128 10#5 ∧ s.readVReg128 11#5 = s0.readVReg128 11#5 ∧
    s.readVReg128 12#5 = s0.readVReg128 12#5 ∧ s.readVReg128 13#5 = s0.readVReg128 13#5 ∧
    s.readVReg128 14#5 = s0.readVReg128 14#5 ∧ s.readVReg128 15#5 = s0.readVReg128 15#5 := by
  have h := ha.simd; dsimp only [simdCalleeProj] at h
  rcases Prod.mk.inj h with ⟨h8, h⟩; rcases Prod.mk.inj h with ⟨h9, h⟩
  rcases Prod.mk.inj h with ⟨h10, h⟩; rcases Prod.mk.inj h with ⟨h11, h⟩
  rcases Prod.mk.inj h with ⟨h12, h⟩; rcases Prod.mk.inj h with ⟨h13, h⟩
  rcases Prod.mk.inj h with ⟨h14, h15⟩
  exact ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem Par17Anchor.calleeSaved {s0 s : State} (ha : Par17Anchor s0 s) :
    CalleeSavedPreserved s0 s := by
  obtain ⟨q8, q9, q10, q11, q12, q13, q14, q15⟩ := ha.readVReg128_callee
  dsimp only [State.readVReg128] at q8 q9 q10 q11 q12 q13 q14 q15
  simp [Arm64.CalleeSavedPreserved, calleeSavedVRegs, VRegFile.calleeSaved,
    ha.readReg64, q8, q9, q10, q11, q12, q13, q14, q15]

theorem Par17Anchor.step {s0 s sf : State} (ha : Par17Anchor s0 s)
    (hregs : sf.regs = s.regs) (hsp : sf.sp = s.sp)
    (hsimd : simdCalleeProj sf = simdCalleeProj s)
    (hproj : pureStepProj sf = pureStepProj s)
    (hperm : sf.mem.perm = s.mem.perm) :
    Par17Anchor s0 sf :=
  ⟨hregs.trans ha.regs, hsp.trans ha.sp, hsimd.trans ha.simd,
   ha.pres.trans (PureStepPreserved.of_proj_perm hproj hperm)⟩

theorem regs_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).regs = s.regs := rfl
theorem regs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).regs = s.regs := rfl
theorem regs_advancePC (s : State) : s.advancePC.regs = s.regs := rfl
theorem regs_setMem (s : State) (m : Memory) : (s.setMem m).regs = s.regs := rfl
theorem sp_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl
theorem sp_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := rfl
theorem sp_advancePC (s : State) : s.advancePC.sp = s.sp := rfl
theorem sp_setMem (s : State) (m : Memory) : (s.setMem m).sp = s.sp := rfl
theorem status_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).status = s.status := rfl
theorem status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
theorem status_advancePC (s : State) : s.advancePC.status = s.status := rfl
theorem status_setMem (s : State) (m : Memory) : (s.setMem m).status = s.status := rfl
theorem vreg_setPC (s : State) (pc : BitVec 64) (r : BitVec 5) :
    (s.setPC pc).readVReg128 r = s.readVReg128 r := rfl
theorem vreg_advancePC (s : State) (r : BitVec 5) :
    s.advancePC.readVReg128 r = s.readVReg128 r := rfl
theorem vreg_setMem (s : State) (m : Memory) (r : BitVec 5) :
    (s.setMem m).readVReg128 r = s.readVReg128 r := rfl
theorem vreg_write_same (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).readVReg128 r = v := by simp [wp_norm, arm64_norm]
theorem vreg_write_ne (s : State) (r1 r2 : BitVec 5) (v : BitVec 128) (h : r2 ≠ r1) :
    (s.writeVReg128 r1 v).readVReg128 r2 = s.readVReg128 r2 := by simp [wp_norm, arm64_norm, h]
theorem readReg64_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) (r : Reg) :
    (s.writeVReg128 v val).readReg64 r = s.readReg64 r := by cases r <;> rfl
theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
theorem readReg64_advancePC (s : State) (r : Reg) :
    s.advancePC.readReg64 r = s.readReg64 r := by cases r <;> rfl
theorem readReg64_setMem (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

section SepWPSteps
set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP

/-- Direct 128-bit SIMD load (`LDR Qt, [Xn, #off]`) step rule over `(ea ↦₁₂₈ v) ∗ F`. -/
theorem step_ldr128 {prog : Program} {target_pc pc ea : BitVec 64} {v : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hP : P = (ea ↦₁₂₈ v) ∗ F)
    (hnext : SepWP prog target_pc ((s.writeVReg128 vt v).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hm0 : s.mem ⊨ (ea ↦₁₂₈ v) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hread : s.mem.read128 ea = v := (IsBlock.pointsTo128 ea v).read hm0
  have hcan : s.mem.canRead ea 16 = true := (IsBlock.pointsTo128 ea v).canRead (by decide) hm0
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldrSimd .Q128 vt (.Offset (.gpr rn) off)) s =
      (s.writeVReg128 vt v).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.readSimdSized, State.advancePC, State.setPC,
      State.writeVReg128, SimdMemSize.bytes, haddr, hread, hcan, hpc]
  rw [hstep]
  exact hnext R hm

/-- Direct 128-bit SIMD load-pair (`LDP Qt1, Qt2, [Xn, #off]`) step rule over `↦₁₂₈`. -/
theorem step_ldp128 {prog : Program} {target_pc pc ea : BitVec 64} {v1 v2 : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hP : P = ((ea ↦₁₂₈ v1) ∗ ((ea + 16#64) ↦₁₂₈ v2)) ∗ F)
    (hnext : SepWP prog target_pc (((s.writeVReg128 vt1 v1).writeVReg128 vt2 v2).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hm1 : s.mem ⊨ (ea ↦₁₂₈ v1) ∗ (((ea + 16#64) ↦₁₂₈ v2) ∗ (F ∗ R)) := by
    rwa [hP, sepConj_assoc, sepConj_assoc] at hm
  have hm2 : s.mem ⊨ ((ea + 16#64) ↦₁₂₈ v2) ∗ ((ea ↦₁₂₈ v1) ∗ (F ∗ R)) := by
    rwa [hP, sepConj_comm (ea ↦₁₂₈ v1) ((ea + 16#64) ↦₁₂₈ v2), sepConj_assoc, sepConj_assoc] at hm
  have hr1 : s.mem.read128 ea = v1 := (IsBlock.pointsTo128 ea v1).read hm1
  have hr2 : s.mem.read128 (ea + 16#64) = v2 := (IsBlock.pointsTo128 (ea + 16#64) v2).read hm2
  have hc1 : s.mem.canRead ea 16 = true := (IsBlock.pointsTo128 ea v1).canRead (by decide) hm1
  have hc2 : s.mem.canRead (ea + 16#64) 16 = true := (IsBlock.pointsTo128 (ea + 16#64) v2).canRead (by decide) hm2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr rn) off)) s =
      ((s.writeVReg128 vt1 v1).writeVReg128 vt2 v2).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.readSimdSized, State.advancePC, State.setPC,
      State.writeVReg128, SimdMemSize.bytes, haddr, hr1, hr2, hc1, hc2, hpc]
  rw [hstep]
  exact hnext R hm

/-- Permission-preserving 128-bit SIMD store (`STR Qt, [Xn, #off]`) step rule over `↦₁₂₈`. -/
theorem step_str128_perm {prog : Program} {target_pc pc ea : BitVec 64} {old val : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hval : s.readVReg128 vt = val)
    (hP : P = (ea ↦₁₂₈ old) ∗ F)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') ((ea ↦₁₂₈ val) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hm0 : s.mem ⊨ (ea ↦₁₂₈ old) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hcan : s.mem.canWrite ea 16 = true := (IsBlock.pointsTo128 ea old).canWrite (by decide) hm0
  let m1 := s.mem.write128 ea val
  have hm1 : m1 ⊨ ((ea ↦₁₂₈ val) ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact IsBlock.write128 (IsBlock.pointsTo128 ea old) hm0 val
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .Q128 vt (.Offset (.gpr rn) off)) s =
      (s.setPC (pc + 4#64)).setMem m1 := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.writeSimdSized, State.advancePC, State.setPC,
      State.setMem, SimdMemSize.bytes, haddr, hval, hcan, hpc, m1]
  rw [hstep]
  exact hnext m1 (Memory.perm_write128 _ _ _) R hm1

/-- Permission-preserving 128-bit SIMD store-pair (`STP Qt1, Qt2, [Xn, #off]`) step rule over `↦₁₂₈`. -/
theorem step_stp128_perm {prog : Program} {target_pc pc ea : BitVec 64}
    {old1 old2 val1 val2 : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hv1 : s.readVReg128 vt1 = val1) (hv2 : s.readVReg128 vt2 = val2)
    (hP : P = ((ea ↦₁₂₈ old1) ∗ ((ea + 16#64) ↦₁₂₈ old2)) ∗ F)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m')
        (((ea ↦₁₂₈ val1) ∗ ((ea + 16#64) ↦₁₂₈ val2)) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hm1_pre : s.mem ⊨ (ea ↦₁₂₈ old1) ∗ (((ea + 16#64) ↦₁₂₈ old2) ∗ (F ∗ R)) := by
    rwa [hP, sepConj_assoc, sepConj_assoc] at hm
  have hc1 : s.mem.canWrite ea 16 = true := (IsBlock.pointsTo128 ea old1).canWrite (by decide) hm1_pre
  let m1 := s.mem.write128 ea val1
  have hm1_raw : m1 ⊨ (ea ↦₁₂₈ val1) ∗ (((ea + 16#64) ↦₁₂₈ old2) ∗ (F ∗ R)) :=
    IsBlock.write128 (IsBlock.pointsTo128 ea old1) hm1_pre val1
  have hm1 : m1 ⊨ ((ea + 16#64) ↦₁₂₈ old2) ∗ ((ea ↦₁₂₈ val1) ∗ (F ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (ea ↦₁₂₈ val1) ((ea + 16#64) ↦₁₂₈ old2), sepConj_assoc] at hm1_raw
  have hc2_m1 : m1.canWrite (ea + 16#64) 16 = true :=
    (IsBlock.pointsTo128 (ea + 16#64) old2).canWrite (by decide) hm1
  have hc2 : s.mem.canWrite (ea + 16#64) 16 = true := by
    rwa [Memory.canWrite_congr (Memory.perm_write128 _ _ _)] at hc2_m1
  let m2 := m1.write128 (ea + 16#64) val2
  have hm2_raw : m2 ⊨ ((ea + 16#64) ↦₁₂₈ val2) ∗ ((ea ↦₁₂₈ val1) ∗ (F ∗ R)) :=
    IsBlock.write128 (IsBlock.pointsTo128 (ea + 16#64) old2) hm1 val2
  have hm2 : m2 ⊨ (((ea ↦₁₂₈ val1) ∗ ((ea + 16#64) ↦₁₂₈ val2)) ∗ F) ∗ R := by
    rwa [← sepConj_assoc, sepConj_comm ((ea + 16#64) ↦₁₂₈ val2) (ea ↦₁₂₈ val1), ← sepConj_assoc] at hm2_raw
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr rn) off)) s =
      (s.setPC (pc + 4#64)).setMem m2 := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.writeSimdSized, State.advancePC, State.setPC,
      State.setMem, SimdMemSize.bytes, haddr, hv1, hv2, hc1, hc2, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 (by simp [m2, m1]) R hm2

end SepWPSteps

end
end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
