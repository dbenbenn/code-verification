/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import

/-!
# `rej_sample` halfword-slot memory, bitfield, and clamp bridges

Memory, bitfield, and condition-code equivalences for `B03`–`B07` `rej_sample` and post-loop clamping:
1. `write16_packHalfwordsLE` (`ByteSlice.write16` on `packHalfwordsLE hws` ↔ `hws.set`) and
   `rejWriteCandidates_append` / `rejChunksFromPure_zero_eq_fold`;
2. `SepStore16` and `SepLoad8` framing helpers for `272`-halfword (`544`-byte) scratch slots and
   `24`-byte squeeze chunks (relative to `rBuf = sqBase + (24 * chunkIdx + 11)`);
3. `Arm64` `evalBitfield`, `evalLogical`, `ConditionHolds`, and `CSEL` `clampSampled` lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkemQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  clampSampled
  getD_packHalfwordsLE_even
  getD_packHalfwordsLE_odd
  packHalfwordsLE
  packHalfwordsLE_length
  rej12D1
  rej12D1W32
  rej12D1W32_ule_3328
  rej12D1W32_ult_3329
  rej12D2
  rej12D2W32
  rej12D2W32_ule_3328
  rej12D2W32_ult_3329
  rejChunkStepPure
  rejChunksFoldPure
  rejWriteCandidates
)

/-! ## 1. `ByteSlice.write16` ↔ `packHalfwordsLE (hws.set ...)` & Chunk Fold Countdown -/

private theorem extractLsb'_0_8_eq_truncate (v : BitVec 16) :
    v.extractLsb' 0 8 = v.truncate 8 := by bv_bits

private theorem extractLsb'_8_8_eq_shr_truncate (v : BitVec 16) :
    v.extractLsb' 8 8 = (v >>> 8).truncate 8 := by bv_bits

/-- Storing a 16-bit halfword `v` at byte offset `2 * pos` into `packHalfwordsLE hws` (`pos < hws.length`)
    updates halfword `pos` in place. -/
theorem write16_packHalfwordsLE (hws : List (BitVec 16)) (pos : Nat) (v : BitVec 16)
    (hpos : pos < hws.length) :
    ByteSlice.write16 (packHalfwordsLE hws) (2 * pos) v =
      packHalfwordsLE (hws.set pos v) := by
  have hlenL : (ByteSlice.write16 (packHalfwordsLE hws) (2 * pos) v).length = 2 * hws.length := by
    rw [ByteSlice.write16_length (packHalfwordsLE hws) (2 * pos) v
      (by rw [packHalfwordsLE_length]; omega), packHalfwordsLE_length]
  have hlenR : (packHalfwordsLE (hws.set pos v)).length = 2 * hws.length := by
    rw [packHalfwordsLE_length, List.length_set]
  apply ByteSlice.ext_getD (hlenL.trans hlenR.symm)
  intro i hi
  rw [hlenL] at hi
  rw [ByteSlice.getD_write16 (packHalfwordsLE hws) (2 * pos) v i 0#8
    (by rw [packHalfwordsLE_length]; omega)]
  have hk_lt : i / 2 < hws.length := by omega
  by_cases heven : i % 2 = 0
  · have hi_eq : i = 2 * (i / 2) := by omega
    rw [hi_eq, getD_packHalfwordsLE_even, getD_packHalfwordsLE_even]
    by_cases hkp : i / 2 = pos
    · subst hkp
      have hcond : 2 * (i / 2) ≤ 2 * (i / 2) ∧ 2 * (i / 2) < 2 * (i / 2) + 2 := by omega
      simp only [hcond, and_self, ↓reduceIte, Nat.sub_self, Nat.mul_zero,
        extractLsb'_0_8_eq_truncate, List.getD_eq_getElem?_getD,
        List.getElem?_set_self hk_lt, Option.getD_some]
    · have hcond : ¬(2 * pos ≤ 2 * (i / 2) ∧ 2 * (i / 2) < 2 * pos + 2) := by omega
      simp only [hcond, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hkp)]
  · have hi_eq : i = 2 * (i / 2) + 1 := by omega
    rw [hi_eq, getD_packHalfwordsLE_odd, getD_packHalfwordsLE_odd]
    by_cases hkp : i / 2 = pos
    · subst hkp
      have hcond : 2 * (i / 2) ≤ 2 * (i / 2) + 1 ∧ 2 * (i / 2) + 1 < 2 * (i / 2) + 2 := by omega
      have hsub : 2 * (i / 2) + 1 - 2 * (i / 2) = 1 := by omega
      simp only [hcond, and_self, ↓reduceIte, hsub, Nat.mul_one,
        extractLsb'_8_8_eq_shr_truncate, List.getD_eq_getElem?_getD,
        List.getElem?_set_self hk_lt, Option.getD_some]
    · have hcond : ¬(2 * pos ≤ 2 * (i / 2) + 1 ∧ 2 * (i / 2) + 1 < 2 * pos + 2) := by omega
      simp only [hcond, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hkp)]

@[simp] theorem rejWriteCandidates_nil (hws : List (BitVec 16)) (pos : Nat) :
    rejWriteCandidates hws pos [] = hws := rfl

@[simp] theorem rejWriteCandidates_cons (hws : List (BitVec 16)) (pos c : Nat) (cs : List Nat) :
    rejWriteCandidates hws pos (c :: cs) =
      rejWriteCandidates (hws.set pos (BitVec.ofNat 16 c)) (pos + 1) cs := rfl

theorem rejWriteCandidates_append (hws : List (BitVec 16)) (pos : Nat) (cs1 cs2 : List Nat) :
    rejWriteCandidates hws pos (cs1 ++ cs2) =
      rejWriteCandidates (rejWriteCandidates hws pos cs1) (pos + cs1.length) cs2 := by
  induction cs1 generalizing hws pos with
  | nil => simp [rejWriteCandidates]
  | cons c cs1 ih =>
    simp only [List.cons_append, rejWriteCandidates, List.length_cons, ih]
    congr 1
    omega

/-- Tail-recursive `rem`-countdown form of `rejChunksFoldPure`, matching the hardware `subs xRem, 1`
    inner chunk loop starting at chunk `idx` with `rem` chunks remaining. -/
@[expose] def rejChunksFromPure (buf : List (BitVec 8)) :
    Nat → Nat → Nat → List (BitVec 16) → Nat × List (BitVec 16)
  | _, 0, sampled, hws => (sampled, hws)
  | idx, rem + 1, sampled, hws =>
    let res := rejChunkStepPure sampled hws ((buf.drop (24 * idx)).take 24)
    rejChunksFromPure buf (idx + 1) rem res.1 res.2

private theorem foldl_range_shift (buf : List (BitVec 8)) (idx : Nat) :
    ∀ (rem sampled : Nat) (hws : List (BitVec 16)),
      ((List.range rem).map (idx + ·)).foldl
        (fun (s, h) i => rejChunkStepPure s h ((buf.drop (24 * i)).take 24))
        (sampled, hws) =
      rejChunksFromPure buf idx rem sampled hws
  | 0, sampled, hws => by simp [rejChunksFromPure]
  | rem + 1, sampled, hws => by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map, List.foldl_cons, rejChunksFromPure]
    have hcomp : ((fun x => idx + x) ∘ (· + 1)) = fun x => (idx + 1) + x := by
      funext x; dsimp; omega
    rw [hcomp]
    exact foldl_range_shift buf (idx + 1) rem _ _

/-- `rejChunksFromPure buf 0 n` equals `rejChunksFoldPure buf n`. -/
theorem rejChunksFromPure_zero_eq_fold (buf : List (BitVec 8)) (n sampled : Nat)
    (hws : List (BitVec 16)) :
    rejChunksFromPure buf 0 n sampled hws = rejChunksFoldPure buf n sampled hws := by
  have h := (foldl_range_shift buf 0 n sampled hws).symm
  simpa [rejChunksFoldPure] using h

/-! ## 2. `SepStore16` & `SepLoad8` Helpers for `rej_sample` Addressing -/

/-- `SepStore16` for `STRH w, [xOut, xCnt, lsl #1]` (and `STRH w, [xOut]` when `count = 0`) into
    `slotBase ↦ₛ packHalfwordsLE hws` (`hws.length = 272`, `sampled < 256`, `count < 16`). -/
theorem sepStore16_rejSlot {ea slotBase : BitVec 64} {hws : List (BitVec 16)}
    {sampled count : Nat} {v : BitVec 16} {F : SepProp}
    (hlen : hws.length = 272) (hs : sampled < 256) (hc : count < 16)
    (hea : slotBase + BitVec.ofNat 64 (2 * (sampled + count)) = ea) :
    SepStore16 ea v ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)
      ((slotBase ↦ₛ packHalfwordsLE (hws.set (sampled + count) v)) ∗ F) := by
  have hoff : 2 * (sampled + count) + 2 ≤ (packHalfwordsLE hws).length := by
    rw [packHalfwordsLE_length, hlen]; omega
  have hst := SepStore16.left (R := F)
    (SepStore16.of_pointsToBytes_here ea slotBase (packHalfwordsLE hws)
      (2 * (sampled + count)) v hoff hea)
  rwa [write16_packHalfwordsLE hws (sampled + count) v (by omega)] at hst

/-- Address identity for `STRH w, [xOut]` (`count = 0`) where `xOut = slotBase + (sampled <<< 1)`. -/
theorem addr_rejSlot_zero (slotBase : BitVec 64) (sampled : Nat) :
    slotBase + BitVec.ofNat 64 (2 * (sampled + 0)) =
      slotBase + (BitVec.ofNat 64 sampled <<< 1) := by
  congr 1
  bv_omega

/-- Address identity for `STRH w, [xOut, xCnt, lsl #1]` where `xOut = slotBase + (sampled <<< 1)`. -/
theorem addr_rejSlot_regOff (slotBase : BitVec 64) (sampled count : Nat) :
    slotBase + BitVec.ofNat 64 (2 * (sampled + count)) =
      (slotBase + (BitVec.ofNat 64 sampled <<< 1)) + (BitVec.ofNat 64 count <<< 1) := by
  bv_omega

/-- Abstract byte-load capability over `buf` at `sqBase` (`24 * nChunks` readable bytes), satisfied
    by both `(sqBase ↦ₛ buf)` and `(sqBase ↦ᵣ buf)`. -/
@[expose] def RejBufReadable (sqBase : BitVec 64) (buf : List (BitVec 8))
    (nChunks : Nat) (Pbuf : SepProp) : Prop :=
  ∀ off : Nat, off < 24 * nChunks → SepLoad8 (sqBase + BitVec.ofNat 64 off) Pbuf (buf.getD off 0#8)

theorem rejBufReadable_of_pointsToBytes (sqBase : BitVec 64) (buf : List (BitVec 8))
    (nChunks : Nat) (hlen : 24 * nChunks ≤ buf.length) :
    RejBufReadable sqBase buf nChunks (sqBase ↦ₛ buf) := fun _ hoff =>
  SepLoad8.of_pointsToBytes (sepConj_emp _).symm (by omega) rfl

theorem rejBufReadable_of_pointsToBytesRO (sqBase : BitVec 64) (buf : List (BitVec 8))
    (nChunks : Nat) (hlen : 24 * nChunks ≤ buf.length) :
    RejBufReadable sqBase buf nChunks (sqBase ↦ᵣ buf) := fun _ hoff =>
  SepLoad8.of_pointsToBytesRO (sepConj_emp _).symm (by omega) rfl

/-- Byte load `j < 24` of chunk `chunkIdx < nChunks` at `ea = rBuf + disp` (where
    `rBuf = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11)` and `11#64 + disp = BitVec.ofNat 64 j`). -/
theorem sepLoad8_rejChunk_byte {sqBase ea disp : BitVec 64} {buf : List (BitVec 8)}
    {nChunks chunkIdx j : Nat} {Pbuf F : SepProp}
    (hread : RejBufReadable sqBase buf nChunks Pbuf)
    (hchunk : chunkIdx < nChunks) (hj : j < 24)
    (hdisp : 11#64 + disp = BitVec.ofNat 64 j)
    (hea : (sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11)) + disp = ea) :
    SepLoad8 ea (Pbuf ∗ F) (((buf.drop (24 * chunkIdx)).take 24).getD j 0#8) := by
  have hoff_lt : 24 * chunkIdx + j < 24 * nChunks := by omega
  have hadj : sqBase + BitVec.ofNat 64 (24 * chunkIdx + j) = ea := by bv_omega
  have hget : buf.getD (24 * chunkIdx + j) 0#8 =
      ((buf.drop (24 * chunkIdx)).take 24).getD j 0#8 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]
  rw [← hadj, ← hget]
  exact SepLoad8.left (hread (24 * chunkIdx + j) hoff_lt)

/-! ## 3. Bitfield, Branch Condition (`subsPState32`/`subsPState64`), & `CSEL` Clamp -/

/-- `BFI Wd, Wn, #8, #4` (`BFM Wd, Wn, #24, #3`) on zero-extended bytes `b0, b1` produces
    `(rej12D1W32 b0 b1).zeroExtend 64`. -/
theorem evalBitfield_bfi_d1 (b0 b1 : BitVec 8) :
    evalBitfield .W32 .BFM (b0.zeroExtend 64) (b1.zeroExtend 64) 24 3 =
      (rej12D1W32 b0 b1).zeroExtend 64 := by
  dsimp [evalBitfield, rej12D1W32]
  bv_bits

/-- `LSR Wb1, Wb1, #4` (`UBFM Wb1, Wb1, #4, #31`) followed by `ORR Wb1, Wb1, Wb2, LSL #4`
    on zero-extended bytes `b1, b2` produces `(rej12D2W32 b1 b2).zeroExtend 64`. -/
theorem evalBitfield_lsr4_orr_d2 (b1 b2 : BitVec 8) (ps : PState) :
    let lsrVal := evalBitfield .W32 .UBFM (b1.zeroExtend 64) (b1.zeroExtend 64) 4 31
    (evalLogical .W32 .ORR lsrVal (shiftVal .W32 (b2.zeroExtend 64) .LSL 4) ps).1 =
      (rej12D2W32 b1 b2).zeroExtend 64 := by
  have hlsr : evalBitfield .W32 .UBFM (b1.zeroExtend 64) (b1.zeroExtend 64) 4 31 =
      ((((b1.zeroExtend 64).truncate 32).zeroExtend 64 >>> 4).truncate 32).zeroExtend 64 := rfl
  dsimp only
  rw [hlsr]
  dsimp [evalLogical, shiftVal, shift32, rej12D2W32]
  bv_bits

theorem condHolds_cmp32_3329_cs_d1 (b0 b1 : BitVec 8) :
    ConditionHolds .CS (subsPState32 (rej12D1W32 b0 b1) 3329#32) =
      decide (¬(rej12D1 b0 b1 < mlkemQ)) := by
  rw [conditionHolds_cs_subsPState32, BitVec.ule_eq_decide_le]
  have h := rej12D1W32_ult_3329 b0 b1
  by_cases hlt : rej12D1 b0 b1 < mlkemQ
  · have hnle : ¬(3329#32 ≤ rej12D1W32 b0 b1) := by have := h.mpr hlt; bv_omega
    simp [hlt, hnle]
  · have hle : 3329#32 ≤ rej12D1W32 b0 b1 := by have : ¬(rej12D1W32 b0 b1 < 3329#32) := mt h.mp hlt; bv_omega
    simp [hlt, hle]

theorem condHolds_cmp32_3329_cs_d2 (b1 b2 : BitVec 8) :
    ConditionHolds .CS (subsPState32 (rej12D2W32 b1 b2) 3329#32) =
      decide (¬(rej12D2 b1 b2 < mlkemQ)) := by
  rw [conditionHolds_cs_subsPState32, BitVec.ule_eq_decide_le]
  have h := rej12D2W32_ult_3329 b1 b2
  by_cases hlt : rej12D2 b1 b2 < mlkemQ
  · have hnle : ¬(3329#32 ≤ rej12D2W32 b1 b2) := by have := h.mpr hlt; bv_omega
    simp [hlt, hnle]
  · have hle : 3329#32 ≤ rej12D2W32 b1 b2 := by have : ¬(rej12D2W32 b1 b2 < 3329#32) := mt h.mp hlt; bv_omega
    simp [hlt, hle]

theorem condHolds_cmp32_3329_cc_d2 (b1 b2 : BitVec 8) :
    ConditionHolds .CC (subsPState32 (rej12D2W32 b1 b2) 3329#32) =
      decide (rej12D2 b1 b2 < mlkemQ) := by
  rw [conditionHolds_cc_subsPState32, BitVec.ult_eq_decide_lt]
  simp [rej12D2W32_ult_3329]

theorem condHolds_cmp32_3328_ls_d1 (b0 b1 : BitVec 8) :
    ConditionHolds .LS (subsPState32 (rej12D1W32 b0 b1) 3328#32) =
      decide (rej12D1 b0 b1 < mlkemQ) := by
  rw [conditionHolds_ls_subsPState32, BitVec.ule_eq_decide_le]
  simp [rej12D1W32_ule_3328]

theorem condHolds_cmp32_3328_hi_d1 (b0 b1 : BitVec 8) :
    ConditionHolds .HI (subsPState32 (rej12D1W32 b0 b1) 3328#32) =
      decide (¬(rej12D1 b0 b1 < mlkemQ)) := by
  rw [conditionHolds_hi_subsPState32, BitVec.ult_eq_decide_lt]
  have h := rej12D1W32_ule_3328 b0 b1
  by_cases hlt : rej12D1 b0 b1 < mlkemQ
  · have hn : ¬(3328#32 < rej12D1W32 b0 b1) := by have := h.mpr hlt; bv_omega
    simp [hlt, hn]
  · have hp : 3328#32 < rej12D1W32 b0 b1 := by have : ¬(rej12D1W32 b0 b1 ≤ 3328#32) := mt h.mp hlt; bv_omega
    simp [hlt, hp]

theorem condHolds_cmp32_3328_ls_d2 (b1 b2 : BitVec 8) :
    ConditionHolds .LS (subsPState32 (rej12D2W32 b1 b2) 3328#32) =
      decide (rej12D2 b1 b2 < mlkemQ) := by
  rw [conditionHolds_ls_subsPState32, BitVec.ule_eq_decide_le]
  simp [rej12D2W32_ule_3328]

theorem condHolds_cmp32_3328_hi_d2 (b1 b2 : BitVec 8) :
    ConditionHolds .HI (subsPState32 (rej12D2W32 b1 b2) 3328#32) =
      decide (¬(rej12D2 b1 b2 < mlkemQ)) := by
  rw [conditionHolds_hi_subsPState32, BitVec.ult_eq_decide_lt]
  have h := rej12D2W32_ule_3328 b1 b2
  by_cases hlt : rej12D2 b1 b2 < mlkemQ
  · have hn : ¬(3328#32 < rej12D2W32 b1 b2) := by have := h.mpr hlt; bv_omega
    simp [hlt, hn]
  · have hp : 3328#32 < rej12D2W32 b1 b2 := by have : ¬(rej12D2W32 b1 b2 ≤ 3328#32) := mt h.mp hlt; bv_omega
    simp [hlt, hp]

theorem condHolds_cmp64_256_cs {sampled : Nat} (hbnd : sampled < 2 ^ 64) :
    ConditionHolds .CS (subsPState64 (BitVec.ofNat 64 sampled) 256#64) =
      decide (¬(sampled < 256)) := by
  rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide_le]
  by_cases hlt : sampled < 256
  · have hn : ¬(256#64 ≤ BitVec.ofNat 64 sampled) := by
      simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hlt, hn]
  · have hp : 256#64 ≤ BitVec.ofNat 64 sampled := by
      simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hlt, hp]

theorem condHolds_cmp64_256_cc {sampled : Nat} (hbnd : sampled < 2 ^ 64) :
    ConditionHolds .CC (subsPState64 (BitVec.ofNat 64 sampled) 256#64) =
      decide (sampled < 256) := by
  rw [conditionHolds_cc_subsPState64, BitVec.ult_eq_decide_lt]
  by_cases hlt : sampled < 256
  · have hp : BitVec.ofNat 64 sampled < 256#64 := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hlt, hp]
  · have hn : ¬(BitVec.ofNat 64 sampled < 256#64) := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hlt, hn]

theorem subs64_one_eq (rem : Nat) :
    BitVec.ofNat 64 (rem + 1) - 1#64 = BitVec.ofNat 64 rem := by
  bv_omega

theorem condHolds_cmp64_1_eq {rem : Nat} (hbnd : rem + 1 < 2 ^ 64) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 (rem + 1)) 1#64) =
      decide (rem = 0) := by
  rw [conditionHolds_eq_subsPState64]
  by_cases h0 : rem = 0
  · subst h0; simp
  · have hne : (BitVec.ofNat 64 (rem + 1) == 1#64) = false := by
      apply beq_false_of_ne
      intro heq
      have hnat := congrArg BitVec.toNat heq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd] at hnat
      omega
    simp [h0, hne]

/-- Hardware clamp equivalence (`CMP Xn, #255; CSEL Xd, X_256, Xn, HI` on `subsPState64`):
    produces `BitVec.ofNat 64 (clampSampled sampled)` whenever `sampled < 2 ^ 64`. -/
theorem condHolds_cmp64_255_hi {sampled : Nat} (hbnd : sampled < 2 ^ 64) :
    ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 sampled) 255#64) =
      decide (255 < sampled) := by
  rw [conditionHolds_hi_subsPState64, BitVec.ult_eq_decide_lt]
  by_cases hgt : 255 < sampled
  · have hp : 255#64 < BitVec.ofNat 64 sampled := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hgt, hp]
  · have hn : ¬(255#64 < BitVec.ofNat 64 sampled) := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hgt, hn]

theorem condHolds_cmp64_255_ls {sampled : Nat} (hbnd : sampled < 2 ^ 64) :
    ConditionHolds .LS (subsPState64 (BitVec.ofNat 64 sampled) 255#64) =
      decide (sampled ≤ 255) := by
  rw [conditionHolds_ls_subsPState64, BitVec.ule_eq_decide_le]
  by_cases hle : sampled ≤ 255
  · have hp : BitVec.ofNat 64 sampled ≤ 255#64 := by
      simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hle, hp]
  · have hn : ¬(BitVec.ofNat 64 sampled ≤ 255#64) := by
      simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd]; omega
    simp [hle, hn]

theorem csel_clampSampled_eq {sampled : Nat} (hbnd : sampled < 2 ^ 64) :
    (if ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 sampled) 255#64) then
      256#64
    else
      BitVec.ofNat 64 sampled) = BitVec.ofNat 64 (clampSampled sampled) := by
  rw [condHolds_cmp64_255_hi hbnd]
  unfold clampSampled
  by_cases h : 255 < sampled <;> simp [h]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem
