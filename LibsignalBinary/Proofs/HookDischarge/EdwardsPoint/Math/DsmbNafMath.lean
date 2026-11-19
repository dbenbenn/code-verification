/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards -- proof-setup: allow-public-import

/-!
# Signed Width-5 & Width-8 NAF Recoding Proofs (`LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbNafMath`)

Pure `0-sorry` mathematical proofs for the Non-Adjacent Form (NAF) recoding and top-down scan
used by `vartime_double_scalar_mul_basepoint`:
1. Bit-level equivalence of `naf5BitBuf` and `naf8BitBuf` with `(leBytesToNat x_buf / 2 ^ pos) % 2^w`.
2. Digit validity and exact polynomial evaluation (`nafHorner`) of `naf5Loop` and `naf8Loop` on
   32-byte scalars `< 2 ^ 254` (hence all scalars `< edOrderL`).
3. Zero-skipping invariance of `findMaxNafIdx` on `nafHorner`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbNafMath

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  edOrderL leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  naf5BitBuf naf5Digit naf5NextCarry naf5Loop naf5ByteValid naf8BitBuf naf8NextCarry naf8Loop
  findMaxNafIdx)
/-! ## 1. Little-Endian Bit Extraction (`naf5BitBuf` & `naf8BitBuf`) -/

theorem leBytesToNat_append_replicate_zero (bs : List (BitVec 8)) (n : Nat) :
    leBytesToNat (bs ++ List.replicate n 0#8) = leBytesToNat bs := by
  have hrep : ∀ k : Nat, (List.replicate k 0#8).foldr (fun b acc => acc * 256 + b.toNat) 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  unfold leBytesToNat
  rw [List.foldr_append, hrep n]

private theorem testBit_leBytesToNat (bs : List (BitVec 8)) :
    ∀ k : Nat, (leBytesToNat bs).testBit k = (bs.getD (k / 8) 0#8).getLsbD (k % 8) := by
  induction bs with
  | nil =>
    intro k
    simp [leBytesToNat]
  | cons b rest ih =>
    intro k
    have hb : b.toNat < 256 := b.isLt
    have hcons : leBytesToNat (b :: rest) = leBytesToNat rest * 256 + b.toNat := rfl
    rw [hcons]
    by_cases hk : k < 8
    · have hdiv : k / 8 = 0 := by omega
      have hmod : k % 8 = k := by omega
      rw [hdiv, hmod, List.getD_cons_zero]
      have h256 : 256 = 2 ^ k * (2 * 2 ^ (7 - k)) := by
        have hsum : k + (7 - k + 1) = 8 := by omega
        calc 256 = 2 ^ 8 := rfl
          _ = 2 ^ (k + (7 - k + 1)) := by rw [hsum]
          _ = 2 ^ k * 2 ^ (7 - k + 1) := Nat.pow_add 2 k (7 - k + 1)
          _ = 2 ^ k * (2 * 2 ^ (7 - k)) := by rw [Nat.pow_succ']
      have heq :
          ((leBytesToNat rest * 256 + b.toNat) / 2 ^ k) % 2 = (b.toNat / 2 ^ k) % 2 := by
        have hrew :
            leBytesToNat rest * 256 + b.toNat =
              b.toNat + 2 ^ k * (2 * (leBytesToNat rest * 2 ^ (7 - k))) := by
          rw [h256]
          grind
        rw [hrew, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
        omega
      rw [Nat.testBit_eq_decide_div_mod_eq, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, heq]
    · have hk8 : k = 8 + (k - 8) := by omega
      have hdiv : k / 8 = (k - 8) / 8 + 1 := by omega
      have hmod : k % 8 = (k - 8) % 8 := by omega
      rw [hdiv, hmod, List.getD_cons_succ, ← ih (k - 8)]
      conv => lhs; rw [hk8]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
          Nat.pow_add, ← Nat.div_div_eq_div_mul,
          show (leBytesToNat rest * 256 + b.toNat) / 2 ^ 8 = leBytesToNat rest by
            have : (2 : Nat) ^ 8 = 256 := by decide
            omega]

private theorem getLsbD_readLE8 (bs : List (BitVec 8)) (off i : Nat) (hi : i < 64) :
    (ByteSlice.readLE bs off 8).getLsbD i = (leBytesToNat bs).testBit (8 * off + i) := by
  rw [BitVec.getLsbD_eq_getElem hi, ByteSlice.getElem_readLE bs off 8 i hi]
  have hi64 : i < 8 * 8 := by omega
  simp only [hi64, ↓reduceIte]
  rw [testBit_leBytesToNat bs (8 * off + i),
      show (8 * off + i) / 8 = off + i / 8 by omega,
      show (8 * off + i) % 8 = i % 8 by omega]
  exact (BitVec.getLsbD_eq_getElem (Nat.mod_lt _ (by omega))).symm

theorem naf5BitBuf_toNat (x_buf : List (BitVec 8)) (pos : Nat) :
    (naf5BitBuf x_buf pos).toNat = (leBytesToNat x_buf / 2 ^ pos) % 32 := by
  suffices hbv : naf5BitBuf x_buf pos = BitVec.ofNat 64 ((leBytesToNat x_buf / 2 ^ pos) % 32) by
    rw [hbv, BitVec.toNat_ofNat]
    have : (leBytesToNat x_buf / 2 ^ pos) % 32 < 2 ^ 64 := by omega
    exact Nat.mod_eq_of_lt this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hrhs :
      (BitVec.ofNat 64 ((leBytesToNat x_buf / 2 ^ pos) % 32)).getLsbD i =
        (decide (i < 5) && (leBytesToNat x_buf).testBit (pos + i)) := by
    rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and,
        show (32 : Nat) = 2 ^ 5 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i pos]
  rw [hrhs]
  unfold naf5BitBuf
  have hmask : (31#64).getLsbD i = decide (i < 5) := by
    exact (by decide : ∀ k : Fin 64, (31#64).getLsbD k.val = decide (k.val < 5)) ⟨i, hi⟩
  by_cases h59 : 59 ≤ pos % 64
  · simp only [h59, ↓reduceIte, BitVec.getLsbD_and, hmask]
    by_cases hi5 : i < 5
    · simp only [hi5, decide_true, Bool.and_true, Bool.true_and,
        BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
      by_cases hcross : pos % 64 + i < 64
      · have hlhs0 :
            (((ByteSlice.readLE x_buf (8 * (pos / 64) + 8) 8) <<< 1) <<< (63 - pos % 64)).getLsbD i = false := by
          rw [BitVec.getLsbD_shiftLeft]
          simp only [hi, decide_true, Bool.true_and]
          by_cases hlt : i < 63 - pos % 64
          · simp [hlt]
          · have heq0 : i - (63 - pos % 64) = 0 := by omega
            simp [hlt, heq0]
        rw [hlhs0, Bool.false_or, getLsbD_readLE8 x_buf (8 * (pos / 64)) (pos % 64 + i) hcross,
            show 8 * (8 * (pos / 64)) + (pos % 64 + i) = pos + i by omega]
      · have hrhs0 : (ByteSlice.readLE x_buf (8 * (pos / 64)) 8).getLsbD (pos % 64 + i) = false :=
          BitVec.getLsbD_of_ge _ _ (by omega)
        have hlt1 : ¬ (i < 63 - pos % 64) := by omega
        have hsub_lt : i - (63 - pos % 64) < 64 := by omega
        have hlt2 : ¬ (i - (63 - pos % 64) < 1) := by omega
        have hidx_lt : i - (63 - pos % 64) - 1 < 64 := by omega
        rw [hrhs0, Bool.or_false, BitVec.getLsbD_shiftLeft]
        simp only [hi, decide_true, Bool.true_and, hlt1, decide_false, Bool.not_false,
          BitVec.getLsbD_shiftLeft, hsub_lt, hlt2]
        rw [getLsbD_readLE8 x_buf (8 * (pos / 64) + 8) (i - (63 - pos % 64) - 1) hidx_lt,
            show 8 * (8 * (pos / 64) + 8) + (i - (63 - pos % 64) - 1) = pos + i by omega]
    · simp [hi5]
  · simp only [h59, ↓reduceIte, BitVec.getLsbD_and, hmask]
    by_cases hi5 : i < 5
    · have hcross : pos % 64 + i < 64 := by omega
      simp only [hi5, decide_true, Bool.and_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
      rw [getLsbD_readLE8 x_buf (8 * (pos / 64)) (pos % 64 + i) hcross,
          show 8 * (8 * (pos / 64)) + (pos % 64 + i) = pos + i by omega]
    · simp [hi5]

theorem naf8BitBuf_toNat (x_buf : List (BitVec 8)) (pos : Nat) :
    (naf8BitBuf x_buf pos).toNat = (leBytesToNat x_buf / 2 ^ pos) % 256 := by
  suffices hbv : naf8BitBuf x_buf pos = BitVec.ofNat 64 ((leBytesToNat x_buf / 2 ^ pos) % 256) by
    rw [hbv, BitVec.toNat_ofNat]
    have : (leBytesToNat x_buf / 2 ^ pos) % 256 < 2 ^ 64 := by omega
    exact Nat.mod_eq_of_lt this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hrhs :
      (BitVec.ofNat 64 ((leBytesToNat x_buf / 2 ^ pos) % 256)).getLsbD i =
        (decide (i < 8) && (leBytesToNat x_buf).testBit (pos + i)) := by
    rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and,
        show (256 : Nat) = 2 ^ 8 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i pos]
  rw [hrhs]
  unfold naf8BitBuf
  by_cases h56 : 56 ≤ pos % 64
  · simp only [h56, ↓reduceIte, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases hi8 : i < 8
    · simp only [hi8, decide_true, Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
      by_cases hcross : pos % 64 + i < 64
      · have hlhs0 :
            (((ByteSlice.readLE x_buf (8 * (pos / 64) + 8) 8) <<< 1) <<< (63 - pos % 64)).getLsbD i = false := by
          rw [BitVec.getLsbD_shiftLeft]
          simp only [hi, decide_true, Bool.true_and]
          by_cases hlt : i < 63 - pos % 64
          · simp [hlt]
          · have heq0 : i - (63 - pos % 64) = 0 := by omega
            simp [hlt, heq0]
        rw [hlhs0, Bool.false_or, getLsbD_readLE8 x_buf (8 * (pos / 64)) (pos % 64 + i) hcross,
            show 8 * (8 * (pos / 64)) + (pos % 64 + i) = pos + i by omega]
      · have hrhs0 : (ByteSlice.readLE x_buf (8 * (pos / 64)) 8).getLsbD (pos % 64 + i) = false :=
          BitVec.getLsbD_of_ge _ _ (by omega)
        have hlt1 : ¬ (i < 63 - pos % 64) := by omega
        have hsub_lt : i - (63 - pos % 64) < 64 := by omega
        have hlt2 : ¬ (i - (63 - pos % 64) < 1) := by omega
        have hidx_lt : i - (63 - pos % 64) - 1 < 64 := by omega
        rw [hrhs0, Bool.or_false, BitVec.getLsbD_shiftLeft]
        simp only [hi, decide_true, Bool.true_and, hlt1, decide_false, Bool.not_false,
          BitVec.getLsbD_shiftLeft, hsub_lt, hlt2]
        rw [getLsbD_readLE8 x_buf (8 * (pos / 64) + 8) (i - (63 - pos % 64) - 1) hidx_lt,
            show 8 * (8 * (pos / 64) + 8) + (i - (63 - pos % 64) - 1) = pos + i by omega]
    · simp [hi8]
  · simp only [h56, ↓reduceIte, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases hi8 : i < 8
    · have hcross : pos % 64 + i < 64 := by omega
      simp only [hi8, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
      rw [getLsbD_readLE8 x_buf (8 * (pos / 64)) (pos % 64 + i) hcross,
          show 8 * (8 * (pos / 64)) + (pos % 64 + i) = pos + i by omega]
    · simp [hi8]

/-! ## 2. Signed Digit Predicates & Horner Evaluation (`nafHorner`) -/

/-- Valid signed width-5 NAF digit: `0`, or odd in `[-15, 15]`. -/
@[expose] def naf5EntryOk (d : BitVec 8) : Bool :=
  (d == 0#8) || (d.getLsbD 0 && naf5ByteValid d)

/-- Valid signed width-8 NAF digit: `0`, or odd in `[-127, 127]`. -/
@[expose] def naf8EntryOk (d : BitVec 8) : Bool :=
  (d == 0#8) || d.getLsbD 0

/-- Downward Horner evaluation $\text{acc} \cdot 2^{k+1} + \sum_{j=0}^{k} \text{naf}[j].\text{toInt} \cdot 2^j$,
    mirroring `edStrausLoop`. -/
@[expose] def nafHorner (naf : List (BitVec 8)) : Nat → Int → Int
  | 0, acc => 2 * acc + (naf.getD 0 0#8).toInt
  | k + 1, acc => nafHorner naf k (2 * acc + (naf.getD (k + 1) 0#8).toInt)

theorem nafHorner_acc (naf : List (BitVec 8)) (k : Nat) (acc : Int) :
    nafHorner naf k acc = acc * ((2 ^ (k + 1) : Nat) : Int) + nafHorner naf k 0 := by
  induction k generalizing acc with
  | zero =>
    unfold nafHorner
    change 2 * acc + (naf.getD 0 0#8).toInt = acc * 2 + (2 * 0 + (naf.getD 0 0#8).toInt)
    omega
  | succ k ih =>
    unfold nafHorner
    rw [ih (2 * acc + (naf.getD (k + 1) 0#8).toInt),
        ih (2 * 0 + (naf.getD (k + 1) 0#8).toInt)]
    have hpow : ((2 ^ (k + 2) : Nat) : Int) = 2 * ((2 ^ (k + 1) : Nat) : Int) := by
      rw [show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ]
      omega
    rw [hpow]
    grind

theorem nafHorner_succ_zero (naf : List (BitVec 8)) (k : Nat) :
    nafHorner naf (k + 1) 0 =
      (naf.getD (k + 1) 0#8).toInt * ((2 ^ (k + 1) : Nat) : Int) + nafHorner naf k 0 := by
  conv => lhs; unfold nafHorner
  rw [nafHorner_acc]
  grind

private theorem getD_replicate_zero (n i : Nat) :
    (List.replicate n 0#8).getD i 0#8 = 0#8 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem nafHorner_replicate_zero (n : Nat) :
    ∀ k : Nat, nafHorner (List.replicate n 0#8) k 0 = 0
  | 0 => by
    unfold nafHorner
    rw [getD_replicate_zero]
    rfl
  | k + 1 => by
    rw [nafHorner_succ_zero, nafHorner_replicate_zero n k, getD_replicate_zero]
    simp

private theorem getD_write8_eq (bs : List (BitVec 8)) (pos i : Nat) (v d : BitVec 8)
    (hpos : pos < bs.length) :
    (ByteSlice.write8 bs pos v).getD i d = if pos = i then v else bs.getD i d := by
  rw [ByteSlice.write8, ← ByteSlice.set_eq_write bs pos v hpos,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases heq : pos = i
  · subst heq; simp [hpos]
  · simp [heq]

theorem nafHorner_write8 (naf : List (BitVec 8)) (pos : Nat) (v : BitVec 8)
    (hpos_len : pos < naf.length) (hz : naf.getD pos 0#8 = 0#8) :
    ∀ k : Nat,
      nafHorner (ByteSlice.write8 naf pos v) k 0 =
        nafHorner naf k 0 + (if pos ≤ k then v.toInt * ((2 ^ pos : Nat) : Int) else 0)
  | 0 => by
    unfold nafHorner
    rw [getD_write8_eq naf pos 0 v 0#8 hpos_len]
    by_cases hp0 : pos = 0
    · subst hp0
      rw [hz]
      simp
    · have hnle : ¬ (pos ≤ 0) := by omega
      simp [hp0, hnle]
  | k + 1 => by
    rw [nafHorner_succ_zero, nafHorner_succ_zero,
        nafHorner_write8 naf pos v hpos_len hz k,
        getD_write8_eq naf pos (k + 1) v 0#8 hpos_len]
    by_cases hp : pos = k + 1
    · subst hp
      have hnle : ¬ (k + 1 ≤ k) := by omega
      have hle : k + 1 ≤ k + 1 := Nat.le_refl _
      simp only [↓reduceIte, hnle, hle, hz, BitVec.toInt_zero, Int.zero_mul, Int.zero_add]
      omega
    · by_cases hle : pos ≤ k
      · have hle' : pos ≤ k + 1 := by omega
        simp only [hp, ↓reduceIte, hle, hle']
        omega
      · have hle' : ¬ (pos ≤ k + 1) := by omega
        simp only [hp, ↓reduceIte, hle, hle']
        omega

/-! ## 3. Finite-Domain Step Lemmas & Loop Correctness (`naf5Loop` & `naf8Loop`) -/

private theorem naf5_step_props :
    ∀ (r : Fin 32) (c : Fin 2),
      let w := BitVec.ofNat 64 r.val + BitVec.ofNat 64 c.val
      (w.getLsbD 0 = decide ((r.val + c.val) % 2 = 1)) ∧
      ((r.val + c.val) % 2 = 1 →
        let d := naf5Digit w
        let c' := naf5NextCarry w
        naf5EntryOk d = true ∧
        (c' = 0#64 ∨ c' = 1#64) ∧
        (((r.val + c.val : Nat) : Int) = d.toInt + 32 * (c'.toNat : Int)) ∧
        (r.val + c.val ≤ 15 → c'.toNat = 0)) := by
  decide +kernel

private theorem naf8_step_props :
    ∀ (r : Fin 256) (c : Fin 2),
      let w := BitVec.ofNat 64 c.val + BitVec.ofNat 64 r.val
      (w.getLsbD 0 = decide ((r.val + c.val) % 2 = 1)) ∧
      ((r.val + c.val) % 2 = 1 →
        let d := BitVec.setWidth 8 w
        let c' := naf8NextCarry w
        naf8EntryOk d = true ∧
        (c' = 0#64 ∨ c' = 1#64) ∧
        (((r.val + c.val : Nat) : Int) = d.toInt + 256 * (c'.toNat : Int)) ∧
        (r.val + c.val ≤ 127 → c'.toNat = 0)) := by
  decide +kernel

private theorem naf5Loop_invariant (x_buf : List (BitVec 8))
    (hN : leBytesToNat x_buf < 2 ^ 254) :
    ∀ (fuel pos : Nat) (_hpos : pos < 256) (_hfuel : fuel + pos = 256)
      (carry : BitVec 64) (_hc : carry = 0#64 ∨ carry = 1#64)
      (naf : List (BitVec 8)) (_hlen : naf.length = 256)
      (_hok : ∀ i < 256, naf5EntryOk (naf.getD i 0#8) = true)
      (_hzero : ∀ j, pos ≤ j → j < 256 → naf.getD j 0#8 = 0#8)
      (_hsum : nafHorner naf 255 0 +
          ((leBytesToNat x_buf / 2 ^ pos + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
        (leBytesToNat x_buf : Int)),
      let res := naf5Loop x_buf fuel pos carry naf
      res.length = 256 ∧
      (∀ i < 256, naf5EntryOk (res.getD i 0#8) = true) ∧
      nafHorner res 255 0 = (leBytesToNat x_buf : Int) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hpos hfuel carry hc naf hlen hok hzero hsum
    cases fuel with
    | zero => omega
    | succ f =>
      dsimp only
      rw [naf5Loop]
      let N := leBytesToNat x_buf
      let M := N / 2 ^ pos
      have hc_lt : carry.toNat < 2 := by rcases hc with rfl | rfl <;> decide
      have hc_eq : carry = BitVec.ofNat 64 carry.toNat := by simp
      have hbuf_eq : naf5BitBuf x_buf pos = BitVec.ofNat 64 (M % 32) := by
        apply BitVec.eq_of_toNat_eq
        rw [naf5BitBuf_toNat, BitVec.toNat_ofNat]
        change M % 32 = (M % 32) % 2 ^ 64
        omega
      have hstep := naf5_step_props ⟨M % 32, by omega⟩ ⟨carry.toNat, hc_lt⟩
      dsimp only at hstep
      rw [← hbuf_eq, ← hc_eq] at hstep
      rcases hstep with ⟨hparity, hodd_step⟩
      by_cases hodd : (M % 32 + carry.toNat) % 2 = 1
      · have hlsb : (naf5BitBuf x_buf pos + carry).getLsbD 0 = true := by
          rw [hparity]; exact decide_eq_true hodd
        obtain ⟨hd_ok, hc'_or, hd_val, hc'_small⟩ := hodd_step hodd
        let d := naf5Digit (naf5BitBuf x_buf pos + carry)
        let c' := naf5NextCarry (naf5BitBuf x_buf pos + carry)
        let naf' := ByteSlice.write8 naf pos d
        have hlen' : naf'.length = 256 := by
          dsimp only [naf']
          rw [ByteSlice.write8_length _ _ _ (by omega), hlen]
        have hok' : ∀ i < 256, naf5EntryOk (naf'.getD i 0#8) = true := by
          intro i hi
          dsimp only [naf']
          rw [getD_write8_eq naf pos i d 0#8 (by omega)]
          by_cases heq : pos = i
          · simp only [heq, ↓reduceIte]; exact hd_ok
          · simp only [heq, ↓reduceIte]; exact hok i hi
        have hhorner' :
            nafHorner naf' 255 0 = nafHorner naf 255 0 + d.toInt * ((2 ^ pos : Nat) : Int) := by
          dsimp only [naf']
          rw [nafHorner_write8 naf pos d (by omega) (hzero pos (Nat.le_refl _) hpos) 255]
          have : pos ≤ 255 := by omega
          simp [this]
        have hM_div : N / 2 ^ (pos + 5) = M / 32 := by
          dsimp only [M]
          rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
        have hsum_step :
            ((M + carry.toNat : Nat) : Int) =
              d.toInt + 32 * ((N / 2 ^ (pos + 5) + c'.toNat : Nat) : Int) := by
          have hM_split : M + carry.toNat = 32 * (M / 32) + (M % 32 + carry.toNat) := by omega
          rw [hM_div, hM_split]
          change ((32 * (M / 32) + (M % 32 + carry.toNat) : Nat) : Int) =
            d.toInt + 32 * ((M / 32 + c'.toNat : Nat) : Int)
          change ((M % 32 + carry.toNat : Nat) : Int) = d.toInt + 32 * (c'.toNat : Int) at hd_val
          omega
        by_cases hlt5 : pos + 5 < 256
        · simp only [hlsb, ↓reduceIte, hlt5]
          have hzero' : ∀ j, pos + 5 ≤ j → j < 256 → naf'.getD j 0#8 = 0#8 := by
            intro j hj1 hj2
            dsimp only [naf']
            have hne : pos ≠ j := by omega
            rw [getD_write8_eq naf pos j d 0#8 (by omega)]
            simp only [hne, ↓reduceIte]
            exact hzero j (by omega) hj2
          have hsum' :
              nafHorner naf' 255 0 +
                  ((N / 2 ^ (pos + 5) + c'.toNat : Nat) : Int) * ((2 ^ (pos + 5) : Nat) : Int) =
                (N : Int) := by
            have hpow5 : ((2 ^ (pos + 5) : Nat) : Int) = 32 * ((2 ^ pos : Nat) : Int) := by
              rw [Nat.pow_add, Int.natCast_mul]
              change ((2 ^ pos : Nat) : Int) * 32 = 32 * ((2 ^ pos : Nat) : Int)
              omega
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hhorner', hpow5]
            rw [hsum_step] at hsum
            grind
          exact ih (f - 4) (by omega) (pos + 5) hlt5 (by omega) c' hc'_or naf' hlen' hok' hzero' hsum'
        · simp only [hlsb, ↓reduceIte, hlt5]
          have hpos_ge : 251 ≤ pos := by omega
          have hM_le : M ≤ 7 := by
            dsimp only [M, N]
            have hpow_ge : 2 ^ 251 ≤ 2 ^ pos := Nat.pow_le_pow_right (by omega) hpos_ge
            have hN_div : leBytesToNat x_buf / 2 ^ pos ≤ leBytesToNat x_buf / 2 ^ 251 :=
              Nat.div_le_div_left hpow_ge (Nat.two_pow_pos 251)
            have htop : leBytesToNat x_buf / 2 ^ 251 < 8 := by
              have : (2 : Nat) ^ 254 = 2 ^ 251 * 8 := by decide
              omega
            omega
          have hQ0 : N / 2 ^ (pos + 5) = 0 := hM_div.trans (Nat.div_eq_of_lt (by omega))
          have hM_mod_le : M % 32 ≤ M := Nat.mod_le M 32
          have hc'0 : c'.toNat = 0 := hc'_small (by omega)
          have hfin : nafHorner naf' 255 0 = (N : Int) := by
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hQ0, hc'0] at hsum_step
            rw [hsum_step] at hsum
            rw [hhorner']
            grind
          exact ⟨hlen', hok', hfin⟩
      · have hlsb : (naf5BitBuf x_buf pos + carry).getLsbD 0 = false := by
          rw [hparity]; exact decide_eq_false hodd
        have hM_div1 : N / 2 ^ (pos + 1) = M / 2 := by
          dsimp only [M]
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        have hhalf : M + carry.toNat = 2 * (M / 2 + carry.toNat) := by omega
        by_cases hlt1 : pos + 1 < 256
        · simp only [hlsb, Bool.false_eq_true, ↓reduceIte, hlt1]
          have hzero' : ∀ j, pos + 1 ≤ j → j < 256 → naf.getD j 0#8 = 0#8 :=
            fun j hj1 hj2 => hzero j (by omega) hj2
          have hsum' :
              nafHorner naf 255 0 +
                  ((N / 2 ^ (pos + 1) + carry.toNat : Nat) : Int) * ((2 ^ (pos + 1) : Nat) : Int) =
                (N : Int) := by
            have hpow1 : ((2 ^ (pos + 1) : Nat) : Int) = 2 * ((2 ^ pos : Nat) : Int) := by
              rw [Nat.pow_succ]
              omega
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hM_div1, hpow1, hhalf] at *
            grind
          exact ih f (by omega) (pos + 1) hlt1 (by omega) carry hc naf hlen hok hzero' hsum'
        · simp only [hlsb, Bool.false_eq_true, ↓reduceIte, hlt1]
          have hp255 : pos = 255 := by omega
          have hM0 : M = 0 := by
            dsimp only [M, N]
            rw [hp255]
            have : leBytesToNat x_buf < 2 ^ 255 :=
              Nat.lt_trans hN (by decide : 2 ^ 254 < 2 ^ 255)
            omega
          have hc0 : carry.toNat = 0 := by omega
          have hfin : nafHorner naf 255 0 = (N : Int) := by
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hM0, hc0] at hsum
            simpa using hsum
          exact ⟨hlen, hok, hfin⟩

private theorem naf8Loop_invariant (x_buf : List (BitVec 8))
    (hN : leBytesToNat x_buf < 2 ^ 254) :
    ∀ (fuel pos : Nat) (_hpos : pos < 256) (_hfuel : fuel + pos = 256)
      (carry : BitVec 64) (_hc : carry = 0#64 ∨ carry = 1#64)
      (naf : List (BitVec 8)) (_hlen : naf.length = 256)
      (_hok : ∀ i < 256, naf8EntryOk (naf.getD i 0#8) = true)
      (_hzero : ∀ j, pos ≤ j → j < 256 → naf.getD j 0#8 = 0#8)
      (_hsum : nafHorner naf 255 0 +
          ((leBytesToNat x_buf / 2 ^ pos + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
        (leBytesToNat x_buf : Int)),
      let res := naf8Loop x_buf fuel pos carry naf
      res.length = 256 ∧
      (∀ i < 256, naf8EntryOk (res.getD i 0#8) = true) ∧
      nafHorner res 255 0 = (leBytesToNat x_buf : Int) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hpos hfuel carry hc naf hlen hok hzero hsum
    cases fuel with
    | zero => omega
    | succ f =>
      dsimp only
      rw [naf8Loop]
      let N := leBytesToNat x_buf
      let M := N / 2 ^ pos
      have hc_lt : carry.toNat < 2 := by rcases hc with rfl | rfl <;> decide
      have hc_eq : carry = BitVec.ofNat 64 carry.toNat := by simp
      have hbuf_eq : naf8BitBuf x_buf pos = BitVec.ofNat 64 (M % 256) := by
        apply BitVec.eq_of_toNat_eq
        rw [naf8BitBuf_toNat, BitVec.toNat_ofNat]
        change M % 256 = (M % 256) % 2 ^ 64
        omega
      have hstep := naf8_step_props ⟨M % 256, by omega⟩ ⟨carry.toNat, hc_lt⟩
      dsimp only at hstep
      rw [← hbuf_eq, ← hc_eq] at hstep
      rcases hstep with ⟨hparity, hodd_step⟩
      by_cases hodd : (M % 256 + carry.toNat) % 2 = 1
      · have hlsb : (carry + naf8BitBuf x_buf pos).getLsbD 0 = true := by
          rw [hparity]; exact decide_eq_true hodd
        obtain ⟨hd_ok, hc'_or, hd_val, hc'_small⟩ := hodd_step hodd
        let d := BitVec.setWidth 8 (carry + naf8BitBuf x_buf pos)
        let c' := naf8NextCarry (carry + naf8BitBuf x_buf pos)
        let naf' := ByteSlice.write8 naf pos d
        have hlen' : naf'.length = 256 := by
          dsimp only [naf']
          rw [ByteSlice.write8_length _ _ _ (by omega), hlen]
        have hok' : ∀ i < 256, naf8EntryOk (naf'.getD i 0#8) = true := by
          intro i hi
          dsimp only [naf']
          rw [getD_write8_eq naf pos i d 0#8 (by omega)]
          by_cases heq : pos = i
          · simp only [heq, ↓reduceIte]; exact hd_ok
          · simp only [heq, ↓reduceIte]; exact hok i hi
        have hhorner' :
            nafHorner naf' 255 0 = nafHorner naf 255 0 + d.toInt * ((2 ^ pos : Nat) : Int) := by
          dsimp only [naf']
          rw [nafHorner_write8 naf pos d (by omega) (hzero pos (Nat.le_refl _) hpos) 255]
          have : pos ≤ 255 := by omega
          simp [this]
        have hM_div : N / 2 ^ (pos + 8) = M / 256 := by
          dsimp only [M]
          rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
        have hsum_step :
            ((M + carry.toNat : Nat) : Int) =
              d.toInt + 256 * ((N / 2 ^ (pos + 8) + c'.toNat : Nat) : Int) := by
          have hM_split : M + carry.toNat = 256 * (M / 256) + (M % 256 + carry.toNat) := by omega
          rw [hM_div, hM_split]
          change ((256 * (M / 256) + (M % 256 + carry.toNat) : Nat) : Int) =
            d.toInt + 256 * ((M / 256 + c'.toNat : Nat) : Int)
          change ((M % 256 + carry.toNat : Nat) : Int) = d.toInt + 256 * (c'.toNat : Int) at hd_val
          omega
        by_cases hlt8 : pos + 8 < 256
        · simp only [hlsb, ↓reduceIte, hlt8]
          have hzero' : ∀ j, pos + 8 ≤ j → j < 256 → naf'.getD j 0#8 = 0#8 := by
            intro j hj1 hj2
            dsimp only [naf']
            have hne : pos ≠ j := by omega
            rw [getD_write8_eq naf pos j d 0#8 (by omega)]
            simp only [hne, ↓reduceIte]
            exact hzero j (by omega) hj2
          have hsum' :
              nafHorner naf' 255 0 +
                  ((N / 2 ^ (pos + 8) + c'.toNat : Nat) : Int) * ((2 ^ (pos + 8) : Nat) : Int) =
                (N : Int) := by
            have hpow8 : ((2 ^ (pos + 8) : Nat) : Int) = 256 * ((2 ^ pos : Nat) : Int) := by
              rw [Nat.pow_add, Int.natCast_mul]
              change ((2 ^ pos : Nat) : Int) * 256 = 256 * ((2 ^ pos : Nat) : Int)
              omega
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hhorner', hpow8]
            rw [hsum_step] at hsum
            grind
          exact ih (f - 7) (by omega) (pos + 8) hlt8 (by omega) c' hc'_or naf' hlen' hok' hzero' hsum'
        · simp only [hlsb, ↓reduceIte, hlt8]
          have hpos_ge : 248 ≤ pos := by omega
          have hM_le : M ≤ 63 := by
            dsimp only [M, N]
            have hpow_ge : 2 ^ 248 ≤ 2 ^ pos := Nat.pow_le_pow_right (by omega) hpos_ge
            have hN_div : leBytesToNat x_buf / 2 ^ pos ≤ leBytesToNat x_buf / 2 ^ 248 :=
              Nat.div_le_div_left hpow_ge (Nat.two_pow_pos 248)
            have htop : leBytesToNat x_buf / 2 ^ 248 < 64 := by
              have : (2 : Nat) ^ 254 = 2 ^ 248 * 64 := by decide
              omega
            omega
          have hQ0 : N / 2 ^ (pos + 8) = 0 := hM_div.trans (Nat.div_eq_of_lt (by omega))
          have hM_mod_le : M % 256 ≤ M := Nat.mod_le M 256
          have hc'0 : c'.toNat = 0 := hc'_small (by omega)
          have hfin : nafHorner naf' 255 0 = (N : Int) := by
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hQ0, hc'0] at hsum_step
            rw [hsum_step] at hsum
            rw [hhorner']
            grind
          exact ⟨hlen', hok', hfin⟩
      · have hlsb : (carry + naf8BitBuf x_buf pos).getLsbD 0 = false := by
          rw [hparity]; exact decide_eq_false hodd
        have hM_div1 : N / 2 ^ (pos + 1) = M / 2 := by
          dsimp only [M]
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        have hhalf : M + carry.toNat = 2 * (M / 2 + carry.toNat) := by omega
        by_cases hlt1 : pos + 1 < 256
        · simp only [hlsb, Bool.false_eq_true, ↓reduceIte, hlt1]
          have hzero' : ∀ j, pos + 1 ≤ j → j < 256 → naf.getD j 0#8 = 0#8 :=
            fun j hj1 hj2 => hzero j (by omega) hj2
          have hsum' :
              nafHorner naf 255 0 +
                  ((N / 2 ^ (pos + 1) + carry.toNat : Nat) : Int) * ((2 ^ (pos + 1) : Nat) : Int) =
                (N : Int) := by
            have hpow1 : ((2 ^ (pos + 1) : Nat) : Int) = 2 * ((2 ^ pos : Nat) : Int) := by
              rw [Nat.pow_succ]
              omega
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hM_div1, hpow1, hhalf] at *
            grind
          exact ih f (by omega) (pos + 1) hlt1 (by omega) carry hc naf hlen hok hzero' hsum'
        · simp only [hlsb, Bool.false_eq_true, ↓reduceIte, hlt1]
          have hp255 : pos = 255 := by omega
          have hM0 : M = 0 := by
            dsimp only [M, N]
            rw [hp255]
            have : leBytesToNat x_buf < 2 ^ 255 :=
              Nat.lt_trans hN (by decide : 2 ^ 254 < 2 ^ 255)
            omega
          have hc0 : carry.toNat = 0 := by omega
          have hfin : nafHorner naf 255 0 = (N : Int) := by
            change nafHorner naf 255 0 + ((M + carry.toNat : Nat) : Int) * ((2 ^ pos : Nat) : Int) =
              (N : Int) at hsum
            rw [hM0, hc0] at hsum
            simpa using hsum
          exact ⟨hlen, hok, hfin⟩

theorem edOrderL_lt_two_pow_254 : edOrderL < 2 ^ 254 := by
  unfold edOrderL; decide

theorem naf5Loop_spec {a_bs : List (BitVec 8)} (ha : leBytesToNat a_bs < edOrderL) :
    let naf := naf5Loop (a_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
    naf.length = 256 ∧
    (∀ i < 256, naf5EntryOk (naf.getD i 0#8) = true) ∧
    nafHorner naf 255 0 = (leBytesToNat a_bs : Int) := by
  have hx : leBytesToNat (a_bs ++ List.replicate 8 0#8) = leBytesToNat a_bs :=
    leBytesToNat_append_replicate_zero a_bs 8
  have hlt : leBytesToNat (a_bs ++ List.replicate 8 0#8) < 2 ^ 254 := by
    rw [hx]; exact Nat.lt_trans ha edOrderL_lt_two_pow_254
  have hinv := naf5Loop_invariant (a_bs ++ List.replicate 8 0#8) hlt
    256 0 (by decide) rfl 0#64 (Or.inl rfl) (List.replicate 256 0#8) (List.length_replicate)
    (fun i _ => by rw [getD_replicate_zero]; rfl)
    (fun j _ _ => getD_replicate_zero 256 j)
    (by
      rw [nafHorner_replicate_zero]
      change 0 + ((leBytesToNat (a_bs ++ List.replicate 8 0#8) / 1 + 0 : Nat) : Int) * 1 =
        (leBytesToNat (a_bs ++ List.replicate 8 0#8) : Int)
      omega)
  simpa only [hx] using hinv

theorem naf8Loop_spec {b_bs : List (BitVec 8)} (hb : leBytesToNat b_bs < edOrderL) :
    let naf := naf8Loop (b_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
    naf.length = 256 ∧
    (∀ i < 256, naf8EntryOk (naf.getD i 0#8) = true) ∧
    nafHorner naf 255 0 = (leBytesToNat b_bs : Int) := by
  have hx : leBytesToNat (b_bs ++ List.replicate 8 0#8) = leBytesToNat b_bs :=
    leBytesToNat_append_replicate_zero b_bs 8
  have hlt : leBytesToNat (b_bs ++ List.replicate 8 0#8) < 2 ^ 254 := by
    rw [hx]; exact Nat.lt_trans hb edOrderL_lt_two_pow_254
  have hinv := naf8Loop_invariant (b_bs ++ List.replicate 8 0#8) hlt
    256 0 (by decide) rfl 0#64 (Or.inl rfl) (List.replicate 256 0#8) (List.length_replicate)
    (fun i _ => by rw [getD_replicate_zero]; rfl)
    (fun j _ _ => getD_replicate_zero 256 j)
    (by
      rw [nafHorner_replicate_zero]
      change 0 + ((leBytesToNat (b_bs ++ List.replicate 8 0#8) / 1 + 0 : Nat) : Int) * 1 =
        (leBytesToNat (b_bs ++ List.replicate 8 0#8) : Int)
      omega)
  simpa only [hx] using hinv

/-! ## 4. Top-Down Zero-Skipping Scan (`findMaxNafIdx`) -/

theorem findMaxNafIdx_le_self (naf_a naf_b : List (BitVec 8)) :
    ∀ i : Nat, findMaxNafIdx naf_a naf_b i ≤ i
  | 0 => Nat.le_refl 0
  | k + 1 => by
    unfold findMaxNafIdx
    split
    · split
      · exact Nat.le_trans (findMaxNafIdx_le_self naf_a naf_b k) (Nat.le_succ k)
      · exact Nat.le_refl (k + 1)
    · exact Nat.le_refl (k + 1)

theorem nafHorner_findMaxNafIdx (naf_a naf_b : List (BitVec 8)) :
    ∀ i : Nat,
      nafHorner naf_a (findMaxNafIdx naf_a naf_b i) 0 = nafHorner naf_a i 0 ∧
      nafHorner naf_b (findMaxNafIdx naf_a naf_b i) 0 = nafHorner naf_b i 0
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    unfold findMaxNafIdx
    by_cases ha : (naf_a.getD (k + 1) 0#8 == 0#8) = true
    · simp only [ha, ↓reduceIte]
      have ha0 : naf_a.getD (k + 1) 0#8 = 0#8 := beq_iff_eq.mp ha
      by_cases hb : (naf_b.getD (k + 1) 0#8 == 0#8) = true
      · simp only [hb, ↓reduceIte]
        have hb0 : naf_b.getD (k + 1) 0#8 = 0#8 := beq_iff_eq.mp hb
        obtain ⟨iha, ihb⟩ := nafHorner_findMaxNafIdx naf_a naf_b k
        rw [iha, ihb, nafHorner_succ_zero, nafHorner_succ_zero, ha0, hb0]
        simp
      · simp only [hb]
        exact ⟨rfl, rfl⟩
    · simp only [ha]
      exact ⟨rfl, rfl⟩

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbNafMath
