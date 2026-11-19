/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem

/-!
# Bit-Level Reduction Helpers for `PortableVector::deserialize_{4,5,11}`

Helper lemmas for `PortableVector::deserialize_{4,5,11}`:
- `getElem_deserializeChunkCoeff`: closed-form bit `i < 16` of `deserializeChunkCoeff d bs j`
- `HalfwordTable` and `eq_deserializeChunkBytes_of_halfwordTable`: close a 16-store
  `ByteSlice.write16` buffer equality against `deserializeChunkBytes d bs` from the 16 halfword
  equalities
- Bit-level `evalBitfield` rules for 32-bit `UBFM` and `BFM`
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (bytesToBits byteDecodeRaw)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkBytes
  deserializeChunkCoeff
  eq_packPoly16ChunkBytes_of_getD
)

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h
    change (Array.ofFn f)[i]'h = f ⟨i, hi⟩
    exact Array.getElem_ofFn h
  · rename_i h
    exact False.elim (h (by simp [hi]))

private theorem toArray_getD_eq {α : Type _} (xs : List α) (i : Nat) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have hi : i < xs.length := by simpa using h
    change xs.toArray[i]'h = xs[i]?.getD d
    rw [List.getElem_toArray, List.getElem?_eq_getElem hi]
    rfl
  · rename_i h
    have hi : xs.length ≤ i := by simpa using h
    rw [List.getElem?_eq_none hi]
    rfl

private theorem testBit_and_one (x r : Nat) :
    Nat.testBit (x &&& 1) r = (decide (r = 0) && Nat.testBit x 0) := by
  rw [Nat.testBit_and]
  cases r with
  | zero => simp
  | succ r' =>
    have h1 : Nat.testBit 1 (r' + 1) = false := by
      rw [Nat.testBit_succ]
      simp
    rw [h1, Bool.and_false]
    rfl

private theorem testBit_foldl_bits (m : Nat) (bitFn : Nat → Nat) (i : Nat) :
    Nat.testBit ((List.range m).foldl (fun acc k => acc ||| ((bitFn k &&& 1) <<< k)) 0) i =
      if i < m then Nat.testBit (bitFn i) 0 else false := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.testBit_shiftLeft, testBit_and_one]
    by_cases him : i < m
    · have hge : ¬(m ≤ i) := by omega
      have hlt : i < m + 1 := by omega
      simp [him, hge, hlt]
    · by_cases heq : i = m
      · subst heq
        simp
      · have hlt : ¬(i < m + 1) := by omega
        have hsub : ¬(i - m = 0) := by omega
        simp [him, hlt, hsub]

/-- Exact bit `i < 16` of `deserializeChunkCoeff d bs j` (`j < 16`, `bs.length = 2 * d`). -/
theorem getElem_deserializeChunkCoeff (d : Nat) (bs : List (BitVec 8))
    (hlen : bs.length = 2 * d) (j i : Nat) (hj : j < 16) (hi : i < 16) :
    (deserializeChunkCoeff d bs j)[i] =
      if i < d then
        (bs.getD ((j * d + i) / 8) 0#8).getLsbD ((j * d + i) % 8)
      else
        false := by
  have hj256 : j < 256 := by omega
  rw [← BitVec.getLsbD_eq_getElem hi]
  unfold deserializeChunkCoeff byteDecodeRaw
  rw [BitVec.getLsbD_ofNat, array_getD_ofFn _ _ _ hj256]
  simp only [hi, decide_true, Bool.true_and]
  have hbits_eq :
      (List.range d).foldl
        (fun acc k => acc ||| ((bytesToBits bs).getD (j * d + k) 0 <<< k)) 0 =
      (List.range d).foldl
        (fun acc k =>
          acc ||| ((((bs.getD ((j * d + k) / 8) 0#8).toNat >>> ((j * d + k) % 8)) &&& 1) <<< k))
        0 := by
    have hcongr : ∀ (xs : List Nat) (init : Nat),
        (∀ k ∈ xs, k < d) →
        xs.foldl (fun acc k => acc ||| ((bytesToBits bs).getD (j * d + k) 0 <<< k)) init =
        xs.foldl (fun acc k =>
          acc ||| ((((bs.getD ((j * d + k) / 8) 0#8).toNat >>> ((j * d + k) % 8)) &&& 1) <<< k))
          init := by
      intro xs
      induction xs with
      | nil => intros; rfl
      | cons x xs ih =>
        intro init hmem
        have hx : x < d := hmem x List.mem_cons_self
        have hidx : j * d + x < 8 * bs.length := by
          rw [hlen]
          have h1 : j * d + x < (j + 1) * d := by rw [Nat.succ_mul]; omega
          have h2 : (j + 1) * d ≤ 16 * d := Nat.mul_le_mul_right d (by omega)
          have h3 : 16 * d = 8 * (2 * d) := by rw [← Nat.mul_assoc]
          omega
        have hb : (bytesToBits bs).getD (j * d + x) 0 =
            ((bs.getD ((j * d + x) / 8) 0#8).toNat >>> ((j * d + x) % 8)) &&& 1 := by
          unfold bytesToBits
          rw [array_getD_ofFn _ _ _ hidx]
          dsimp only
          rw [toArray_getD_eq]
        simp only [List.foldl_cons, hb]
        exact ih _ fun k hk => hmem k (List.mem_cons_of_mem x hk)
    exact hcongr (List.range d) 0 fun k hk => List.mem_range.mp hk
  rw [hbits_eq,
    testBit_foldl_bits d
      (fun k => (bs.getD ((j * d + k) / 8) 0#8).toNat >>> ((j * d + k) % 8)) i]
  by_cases hid : i < d
  · simp only [hid, ↓reduceIte, Nat.testBit_shiftRight, Nat.add_zero]
    exact BitVec.testBit_toNat _
  · simp [hid]

/-- Bitwise criterion for proving `v = deserializeChunkCoeff d bs j` across `Fin 16`. -/
theorem eq_deserializeChunkCoeff_of_bits (d : Nat) (bs : List (BitVec 8))
    (hlen : bs.length = 2 * d) (j : Nat) (hj : j < 16) (v : BitVec 16)
    (hbits : ∀ i : Nat, i < 16 →
      v.getLsbD i =
        if i < d then (bs.getD ((j * d + i) / 8) 0#8).getLsbD ((j * d + i) % 8)
        else false) :
    v = deserializeChunkCoeff d bs j := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem hi, hbits i hi,
    ← getElem_deserializeChunkCoeff d bs hlen j i hj hi]

/-- Reassemble a 16-bit word from its high and low 8-bit slices. -/
theorem rejoin16_8_8 (w : BitVec 16) :
    w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  ext i hi
  rw [BitVec.getElem_append]
  by_cases hi8 : i < 8
  · simp [hi8, BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem hi]
  · have hsub : 8 + (i - 8) = i := by omega
    simp [hi8, BitVec.getElem_extractLsb', hsub, BitVec.getLsbD_eq_getElem hi]

/-- Prove `out = deserializeChunkBytes d bs` by checking the 16 16-bit halfwords
`out.getD (2 * j + 1) 0#8 ++ out.getD (2 * j) 0#8` (`j < 16`). -/
theorem eq_deserializeChunkBytes_of_extract16 {out : List (BitVec 8)} {d : Nat}
    {bs : List (BitVec 8)} (hout : out.length = 32)
    (hlanes : ∀ j, j < 16 →
      (out.getD (2 * j + 1) 0#8 ++ out.getD (2 * j) 0#8) = deserializeChunkCoeff d bs j) :
    out = deserializeChunkBytes d bs := by
  apply eq_packPoly16ChunkBytes_of_getD hout
  · intro j hj
    have h := congrArg (fun w : BitVec 16 => w.truncate 8) (hlanes j hj)
    have hlo : (out.getD (2 * j + 1) 0#8 ++ out.getD (2 * j) 0#8).truncate 8 =
        out.getD (2 * j) 0#8 := by
      ext i hi
      rw [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_append]
      simp [hi]
    rwa [hlo] at h
  · intro j hj
    have h := congrArg (fun w : BitVec 16 => (w >>> 8).truncate 8) (hlanes j hj)
    have hhi : ((out.getD (2 * j + 1) 0#8 ++ out.getD (2 * j) 0#8) >>> 8).truncate 8 =
        out.getD (2 * j + 1) 0#8 := by
      ext i hi
      have hnlt : ¬(8 + i < 8) := by omega
      have hsub : 8 + i - 8 = i := by omega
      rw [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_append]
      simp [hnlt, hsub, BitVec.getLsbD_eq_getElem hi]
    rwa [hhi] at h

/-- Unpack `stackAt sp 16` into its two 64-bit saved-register slots. -/
theorem satisfies_stackAt16_two {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 16 ∗ R) :
    ∃ (w0 w1 : BitVec 64),
      m ⊨ (((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1)) ∗ R := by
  have h0 : stackAt (sp - BitVec.ofNat 64 (8 * 2)) (16 - 8 * 2) = emp := memRegion_zero _
  rw [stackAt_frame sp 16 2 (by decide), h0, emp_sepConj,
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero] at hm
  simp only [sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨w0, w1, hm⟩
  exact ⟨w0, w1, Satisfies.mono (by sep_frame) hm⟩

/-- Repack two 64-bit saved-register slots into `stackAt sp 16`. -/
theorem stackAt16_two_entails (sp : BitVec 64) (w0 w1 : BitVec 64) :
    (((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1)) ⊢ stackAt sp 16 := by
  have h0 : stackAt (sp - BitVec.ofNat 64 (8 * 2)) (16 - 8 * 2) = emp := memRegion_zero _
  rw [stackAt_frame sp 16 2 (by decide), h0, emp_sepConj,
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right w0 (sepConj_mono_right (Entails.sepExists_right w1 (Entails.refl _)))

/-- Extract the low byte (`extractLsb' 0 8`) as `.truncate 8`. -/
theorem extractLsb'_0_8_eq_truncate (w : BitVec 16) :
    w.extractLsb' 0 8 = w.truncate 8 := by
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.truncate_eq_setWidth, BitVec.getLsbD_eq_getElem,
    show i < 16 by omega]

/-- Extract the high byte (`extractLsb' 8 8`) as `(w >>> 8).truncate 8`. -/
theorem extractLsb'_8_8_eq_shift_truncate (w : BitVec 16) :
    w.extractLsb' 8 8 = (w >>> 8).truncate 8 := by
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.truncate_eq_setWidth, BitVec.getLsbD_ushiftRight]

/-- `State.writeReg64` preserves `vregs`. -/
theorem vregs_writeReg64 (s : State) (r : Reg) (val : BitVec 64) :
    (s.writeReg64 r val).vregs = s.vregs := rfl

/-- `State.setPState` preserves `vregs`. -/
theorem vregs_setPState (s : State) (ps : PState) :
    (s.setPState ps).vregs = s.vregs := rfl

/-- `State.setPC` preserves `vregs`. -/
theorem vregs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).vregs = s.vregs := rfl

/-- `State.setMem` preserves `vregs`. -/
theorem vregs_setMem (s : State) (m : Memory) :
    (s.setMem m).vregs = s.vregs := rfl

/-- Linear-cost 16-lane halfword view of a 32-byte output slice `bs`, avoiding recursive
`byte_region_len` / `ByteSlice.getD_write16` blowups across 16 nested `strh` writes. -/
def HalfwordTable (bs : List (BitVec 8)) (f : Nat → BitVec 16) : Prop :=
  bs.length = 32 ∧
  ∀ j, j < 16 →
    bs.getD (2 * j) 0#8 = (f j).truncate 8 ∧
    bs.getD (2 * j + 1) 0#8 = ((f j) >>> 8).truncate 8

/-- Initial `HalfwordTable` for any 32-byte slice `out₀`. -/
theorem halfwordTable_init {out₀ : List (BitVec 8)} (hout₀ : out₀.length = 32) :
    HalfwordTable out₀ (fun j => out₀.getD (2 * j + 1) 0#8 ++ out₀.getD (2 * j) 0#8) := by
  refine ⟨hout₀, fun j _hj => ⟨?_, ?_⟩⟩
  · symm
    ext i hi
    rw [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_append]
    simp [hi]
  · symm
    ext i hi
    have hnlt : ¬(8 + i < 8) := by omega
    have hsub : 8 + i - 8 = i := by omega
    rw [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append]
    simp [hnlt, hsub, BitVec.getLsbD_eq_getElem hi]

/-- Step a `HalfwordTable` across one even-aligned in-bounds `ByteSlice.write16` in `O(1)`. -/
theorem halfwordTable_write16 {bs : List (BitVec 8)} {f : Nat → BitVec 16}
    {off : Nat} {v : BitVec 16} (h : HalfwordTable bs f)
    (hoff : decide (off % 2 = 0 ∧ off + 2 ≤ 32) = true := by decide) :
    HalfwordTable (ByteSlice.write16 bs off v)
      (fun j => if j = off / 2 then v else f j) := by
  have ⟨heven, hle⟩ := of_decide_eq_true hoff
  have hbs : bs.length = 32 := h.1
  have hlen : (ByteSlice.write16 bs off v).length = 32 := by
    rw [ByteSlice.write16_length bs off v (by omega), hbs]
  refine ⟨hlen, fun j hj => ⟨?_, ?_⟩⟩
  · dsimp only
    rw [ByteSlice.getD_write16 bs off v (2 * j) 0#8 (by omega)]
    by_cases heq : j = off / 2
    · subst heq
      have hin : off ≤ 2 * (off / 2) ∧ 2 * (off / 2) < off + 2 := by omega
      have hsub : 8 * (2 * (off / 2) - off) = 0 := by omega
      simp only [hin, and_self, ↓reduceIte, hsub, extractLsb'_0_8_eq_truncate]
    · have hout : ¬(off ≤ 2 * j ∧ 2 * j < off + 2) := by omega
      simp only [hout, heq, ↓reduceIte, (h.2 j hj).1]
  · dsimp only
    rw [ByteSlice.getD_write16 bs off v (2 * j + 1) 0#8 (by omega)]
    by_cases heq : j = off / 2
    · subst heq
      have hin : off ≤ 2 * (off / 2) + 1 ∧ 2 * (off / 2) + 1 < off + 2 := by omega
      have hsub : 8 * (2 * (off / 2) + 1 - off) = 8 := by omega
      simp only [hin, and_self, ↓reduceIte, hsub, extractLsb'_8_8_eq_shift_truncate]
    · have hout : ¬(off ≤ 2 * j + 1 ∧ 2 * j + 1 < off + 2) := by omega
      simp only [hout, heq, ↓reduceIte, (h.2 j hj).2]

/-- Close `bs = deserializeChunkBytes d inBytes` from a `HalfwordTable` and 16 lane equalities. -/
theorem eq_deserializeChunkBytes_of_halfwordTable {bs : List (BitVec 8)}
    {f : Nat → BitVec 16} (d : Nat) (inBytes : List (BitVec 8))
    (htab : HalfwordTable bs f)
    (hlanes : ∀ j, j < 16 → f j = deserializeChunkCoeff d inBytes j) :
    bs = deserializeChunkBytes d inBytes :=
  eq_packPoly16ChunkBytes_of_getD htab.1
    (fun j hj => by rw [(htab.2 j hj).1, hlanes j hj])
    (fun j hj => by rw [(htab.2 j hj).2, hlanes j hj])

/-- Out-of-range bit read (`8 ≤ k`) on a `BitVec 8` is `false`. -/
theorem getLsbD_8_of_ge (b : BitVec 8) (k : Nat) (hk : decide (8 ≤ k) = true := by decide) :
    b.getLsbD k = false :=
  BitVec.getLsbD_of_ge b k (of_decide_eq_true hk)

/-- Ground bit read on `0xf0000000f#64` (`and w, w, #0xf` mask) for `k < 16`. -/
theorem getLsbD_mask4_64 (k : Nat) (hk : decide (k < 16) = true := by decide) :
    (64424509455#64).getLsbD k = decide (k < 4) := by
  have hk16 : k < 16 := of_decide_eq_true hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

/-- Ground bit read on `0x1f0000001f#64` (`and w, w, #0x1f` mask) for `k < 16`. -/
theorem getLsbD_mask5_64 (k : Nat) (hk : decide (k < 16) = true := by decide) :
    (133143986207#64).getLsbD k = decide (k < 5) := by
  have hk16 : k < 16 := of_decide_eq_true hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

private theorem getLsbD_mask_pow2_64 (len k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 (Nat.shiftLeft 1 len - 1)).getLsbD k = decide (k < len) := by
  have hsh : Nat.shiftLeft 1 len = 2 ^ len := Nat.one_shiftLeft len
  rw [BitVec.getLsbD_ofNat, hsh, Nat.testBit_two_pow_sub_one]
  simp [hk]

private theorem bfm_ubfm_self : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl
private theorem bfm_ubfm_sbfm : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := rfl
private theorem bfm_bfm_ubfm : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
private theorem bfm_bfm_sbfm : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := rfl

/-- Closed-form bit `k` of `evalBitfield .W32 .UBFM dst src immr imms` (`immr, imms < 32`),
covering `lsr`, `lsl`, `ubfx`, and `ubfiz`. -/
theorem getLsbD_evalBitfield_w32_ubfm (dst src : BitVec 64) (immr imms k : Nat)
    (h : decide (immr < 32 ∧ imms < 32) = true := by decide) :
    (evalBitfield .W32 .UBFM dst src immr imms).getLsbD k =
      if k < 32 then
        if immr ≤ imms then
          if k ≤ imms - immr then src.getLsbD (immr + k) else false
        else
          if 32 - immr ≤ k ∧ k < (32 - immr) + (imms + 1) then
            src.getLsbD (k - (32 - immr))
          else false
      else false := by
  have ⟨hr, hs⟩ := of_decide_eq_true h
  have hrmod : immr % 32 = immr := Nat.mod_eq_of_lt hr
  have hsmod : imms % 32 = imms := Nat.mod_eq_of_lt hs
  unfold evalBitfield
  dsimp only
  simp only [hrmod, hsmod, bfm_ubfm_self, bfm_ubfm_sbfm, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, BitVec.truncate_eq_setWidth]
  by_cases hk32 : k < 32
  · have hk64 : k < 64 := by omega
    by_cases hle : immr ≤ imms
    · have hgt : decide (immr > imms) = false := by
        rw [decide_eq_false_iff_not]
        omega
      by_cases hs31 : imms + 1 == 32
      · have himms31 : imms = 31 := by
          have := beq_iff_eq.mp hs31
          omega
        subst himms31
        have h31 : (31 + 1 == 32) = true := rfl
        simp only [h31, ↓reduceIte, hk32, hle,
          BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
        by_cases hksub : k ≤ 31 - immr
        · have hsum : immr + k < 32 := by omega
          have hsum64 : immr + k < 64 := by omega
          simp [hksub, hsum, hk64, hsum64]
        · have hsum : ¬(immr + k < 32) := by omega
          simp [hksub, hsum]
      · have hs31f : (imms + 1 == 32) = false := Bool.eq_false_iff.mpr hs31
        simp only [hs31f, hgt, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hle, hk32,
          BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
          BitVec.getLsbD_ushiftRight, getLsbD_mask_pow2_64 _ k hk64, decide_true, Bool.true_and]
        by_cases hksub : k ≤ imms - immr
        · have hsum : immr + k < 32 := by omega
          have hsum64 : immr + k < 64 := by omega
          have hklen : k < imms - immr + 1 := by omega
          simp [hksub, hsum, hk64, hsum64, hklen]
        · have hklen : ¬(k < imms - immr + 1) := by omega
          simp [hksub, hklen]
    · have hs31f : (imms + 1 == 32) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      have hgt : decide (immr > imms) = true := by
        rw [decide_eq_true_iff]
        omega
      simp only [hs31f, Bool.false_eq_true, ↓reduceIte, hgt, Bool.true_and, hle, hk32]
      by_cases hfast : (imms + 1 == immr) = true
      · have hfast' : imms + 1 = immr := beq_iff_eq.mp hfast
        simp only [hfast, ↓reduceIte, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_shiftLeft, hk32, hk64, decide_true, Bool.true_and]
        by_cases hpos : 32 - immr ≤ k
        · have hnlt : ¬(k < 32 - immr) := by omega
          have htop : k < 32 - immr + (imms + 1) := by omega
          have hsub32 : k - (32 - immr) < 32 := by omega
          have hsub64 : k - (32 - immr) < 64 := by omega
          simp [hpos, hnlt, htop, hsub32, hsub64]
        · have hlt : k < 32 - immr := by omega
          simp [hpos, hlt]
      · have hfastf : (imms + 1 == immr) = false := Bool.eq_false_iff.mpr hfast
        have hge_false : ¬(imms ≥ immr) := by omega
        simp only [hfastf, Bool.false_eq_true, ↓reduceIte]
        simp only [BitVec.getLsbD_setWidth,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hk32, hk64, decide_true, Bool.true_and]
        by_cases hpos : 32 - immr ≤ k
        · have hnlt : ¬(k < 32 - immr) := by omega
          have hsub64 : k - (32 - immr) < 64 := by omega
          have hsub32 : k - (32 - immr) < 32 := by omega
          rw [getLsbD_mask_pow2_64 _ _ hsub64]
          by_cases htop : k < 32 - immr + (imms + 1)
          · have hsublen : k - (32 - immr) < imms + 1 := by omega
            simp [hpos, hnlt, htop, hsub32, hsub64, hsublen]
          · have hsublen : ¬(k - (32 - immr) < imms + 1) := by omega
            simp [hpos, hnlt, htop, hsublen]
        · have hlt : k < 32 - immr := by omega
          simp [hpos, hlt]
  · split <;> (try split) <;> (try split) <;>
      simp [BitVec.getLsbD_setWidth, hk32]

/-- Closed-form bit `k` of `evalBitfield .W32 .BFM dst src immr imms` for `bfi` (`imms < immr < 32`). -/
theorem getLsbD_evalBitfield_w32_bfm_lt (dst src : BitVec 64) (immr imms k : Nat)
    (h : decide (imms < immr ∧ immr < 32) = true := by decide) :
    (evalBitfield .W32 .BFM dst src immr imms).getLsbD k =
      if k < 32 then
        if 32 - immr ≤ k ∧ k < (32 - immr) + (imms + 1) then
          src.getLsbD (k - (32 - immr))
        else
          dst.getLsbD k
      else false := by
  have ⟨hlt, hr⟩ := of_decide_eq_true h
  have hs : imms < 32 := by omega
  have hrmod : immr % 32 = immr := Nat.mod_eq_of_lt hr
  have hsmod : imms % 32 = imms := Nat.mod_eq_of_lt hs
  have hnge : ¬(imms ≥ immr) := by omega
  unfold evalBitfield
  dsimp only
  simp only [hrmod, hsmod, bfm_bfm_ubfm, bfm_bfm_sbfm, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, hnge, BitVec.truncate_eq_setWidth]
  by_cases hk32 : k < 32
  · have hk64 : k < 64 := by omega
    simp only [hk32, hk64, ↓reduceIte, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      decide_true, Bool.true_and]
    by_cases hpos : 32 - immr ≤ k
    · have hnlt : ¬(k < 32 - immr) := by omega
      have hsub64 : k - (32 - immr) < 64 := by omega
      have hsub32 : k - (32 - immr) < 32 := by omega
      rw [getLsbD_mask_pow2_64 _ _ hsub64]
      by_cases htop : k < 32 - immr + (imms + 1)
      · have hsublen : k - (32 - immr) < imms + 1 := by omega
        simp [hpos, hnlt, htop, hsub32, hsub64, hsublen]
      · have hsublen : ¬(k - (32 - immr) < imms + 1) := by omega
        simp [hpos, hnlt, htop, hsublen]
    · have hltpos : k < 32 - immr := by omega
      simp [hpos, hltpos]
  · simp [BitVec.getLsbD_setWidth, hk32]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers
