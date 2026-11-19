/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec

/-!
# ARMv8 AES Instruction Equivalence & Equivalent Inverse Cipher Algebra (`Armv8.Pure.OpsEquiv`)

Bridges `Arm64.evalAesOp` (`.AESE`, `.AESD`, `.AESMC`, `.AESIMC`) and the little-endian `u32`/`u128`
packing helpers in `Armv8.Defs` to the FIPS 197 operations in `CryptoGames.AES256`, and proves the
FIPS 197 §5.3.5 Equivalent Inverse Cipher commutation identities.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.OpsEquiv

open Arm64 (AesOp evalAesOp aesSBoxTable aesInvSBoxTable)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconWords aesRconBytes u32OfBytesLE bytesToU32LE u32ToBytesLE
   u128OfU32sLE bytesToU128LE u128ToBytesLE armv8InvExpandedKeys)
open CryptoGames.AES256
  (State sboxTable invSboxTable sbox invSbox gfMul subBytes invSubBytes shiftRows invShiftRows
   mixColumn mixColumns invMixColumn invMixColumns addRoundKey xorWord)
open CryptoGames.CBC
  (Block blockToBytesLE bytesToBlock bytesToBlock_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
  (length_addRoundKey)

/-! ## 1. Little-Endian `u32` and `u128` Byte Packing & Round-Trip Lemmas -/

private theorem extractLsb'_u32OfBytesLE (b0 b1 b2 b3 : BitVec 8) :
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 0 8 = b0 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 8 8 = b1 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 16 8 = b2 ∧
    (u32OfBytesLE b0 b1 b2 b3).extractLsb' 24 8 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [u32OfBytesLE, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
      BitVec.getLsbD_append]
    split_ifs <;> try (first | omega | (congr 1; omega))
  }

@[simp] theorem length_u32ToBytesLE (w : BitVec 32) : (u32ToBytesLE w).length = 4 := rfl

@[simp] theorem u32ToBytesLE_u32OfBytesLE (b0 b1 b2 b3 : BitVec 8) :
    u32ToBytesLE (u32OfBytesLE b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  obtain ⟨h0, h1, h2, h3⟩ := extractLsb'_u32OfBytesLE b0 b1 b2 b3
  simp [u32ToBytesLE, h0, h1, h2, h3]

theorem u32_eq_of_extractBytes {a b : BitVec 32}
    (h : ∀ j : Fin 4, a.extractLsb' (8 * j.val) 8 = b.extractLsb' (8 * j.val) 8) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hbyte := congrArg (fun x => x.getLsbD (k % 8)) (h ⟨k / 8, by omega⟩)
  simpa [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega, Nat.div_add_mod k 8] using hbyte

@[simp] theorem u32OfBytesLE_extractLsb' (w : BitVec 32) :
    u32OfBytesLE (w.extractLsb' 0 8) (w.extractLsb' 8 8)
      (w.extractLsb' 16 8) (w.extractLsb' 24 8) = w := by
  obtain ⟨h0, h1, h2, h3⟩ := extractLsb'_u32OfBytesLE
    (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
  apply u32_eq_of_extractBytes; intro ⟨j, hj⟩
  interval_cases j <;> simp [h0, h1, h2, h3]

@[simp] theorem bytesToU32LE_u32ToBytesLE (w : BitVec 32) :
    bytesToU32LE (u32ToBytesLE w) 0 = w := by simp [bytesToU32LE, u32ToBytesLE]

theorem u32ToBytesLE_bytesToU32LE (bs : List (BitVec 8)) (off : Nat) :
    u32ToBytesLE (bytesToU32LE bs off) =
      [bs.getD off 0#8, bs.getD (off + 1) 0#8, bs.getD (off + 2) 0#8, bs.getD (off + 3) 0#8] := by
  simp [bytesToU32LE]

@[simp] theorem u32ToBytesLE_bytesToU32LE_zero {bs : List (BitVec 8)} (h : bs.length = 4) :
    u32ToBytesLE (bytesToU32LE bs 0) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp_all [u32ToBytesLE_bytesToU32LE]

theorem u32ToBytesLE_xor (a b : BitVec 32) :
    u32ToBytesLE (a ^^^ b) = xorWord (u32ToBytesLE a) (u32ToBytesLE b) := by
  have hxor : ∀ s : Nat, (a ^^^ b).extractLsb' s 8 = a.extractLsb' s 8 ^^^ b.extractLsb' s 8 := by
    intro s; apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  simp [u32ToBytesLE, xorWord, List.ofFn_succ, hxor]

theorem rotateRight8_u32OfBytesLE (b0 b1 b2 b3 : BitVec 8) :
    (u32OfBytesLE b0 b1 b2 b3).rotateRight 8 = u32OfBytesLE b1 b2 b3 b0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [u32OfBytesLE, BitVec.getLsbD_rotateRight, hk, decide_true, Bool.true_and,
    BitVec.getLsbD_append, Nat.reduceMod, Nat.reduceSub]
  split_ifs <;> try (first | omega | exact congrArg _ (by omega))

theorem bytesToU32LE_aesRconBytes (i : Fin 10) :
    bytesToU32LE aesRconBytes (4 * i.val) = aesRconWords[i] := by
  revert i; decide

theorem u128ToBytesLE_eq_blockToBytesLE (v : BitVec 128) :
    u128ToBytesLE v = blockToBytesLE v := rfl

@[simp] theorem length_u128ToBytesLE (v : BitVec 128) :
    (u128ToBytesLE v).length = 16 := by simp only [u128ToBytesLE, List.length_ofFn]

@[simp] theorem getElem_u128ToBytesLE (v : BitVec 128) (j : Nat) (hj : j < 16) :
    (u128ToBytesLE v)[j]'(by simp only [length_u128ToBytesLE]; exact hj) =
      v.extractLsb' (8 * j) 8 := by simp only [u128ToBytesLE, List.getElem_ofFn]

theorem getD_u128ToBytesLE (v : BitVec 128) (j : Nat) (hj : j < 16) (d : BitVec 8) :
    (u128ToBytesLE v).getD j d = v.extractLsb' (8 * j) 8 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hj])]; simp [hj]

theorem u128_eq_of_extractBytes {a b : BitVec 128}
    (h : ∀ j : Fin 16, a.extractLsb' (8 * j.val) 8 = b.extractLsb' (8 * j.val) 8) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hbyte := congrArg (fun x => x.getLsbD (k % 8)) (h ⟨k / 8, by omega⟩)
  simpa [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega, Nat.div_add_mod k 8] using hbyte

private theorem extractLsb'_u128OfU32sLE (w0 w1 w2 w3 : BitVec 32) (c : Fin 4) (r : Fin 4) :
    (u128OfU32sLE w0 w1 w2 w3).extractLsb' (8 * (4 * c.val + r.val)) 8 =
      (#[w0, w1, w2, w3][c.val]'(by simp [c.isLt])).extractLsb' (8 * r.val) 8 := by
  rcases c with ⟨c, hc⟩; rcases r with ⟨r, hr⟩
  interval_cases c <;> interval_cases r <;> {
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [u128OfU32sLE, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
      BitVec.getLsbD_append, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    split_ifs <;> try (first | omega | exact congrArg _ (by omega))
  }

theorem u128ToBytesLE_u128OfU32sLE (w0 w1 w2 w3 : BitVec 32) :
    u128ToBytesLE (u128OfU32sLE w0 w1 w2 w3) =
      u32ToBytesLE w0 ++ u32ToBytesLE w1 ++ u32ToBytesLE w2 ++ u32ToBytesLE w3 := by
  apply List.ext_getElem
  · simp [u32ToBytesLE]
  · intro j hj1 _
    have hj : j < 16 := by simpa using hj1
    have hex := extractLsb'_u128OfU32sLE w0 w1 w2 w3 ⟨j / 4, by omega⟩ ⟨j % 4, by omega⟩
    rw [Nat.div_add_mod j 4] at hex
    simp only [getElem_u128ToBytesLE _ j hj, hex]; interval_cases j <;> rfl

theorem u128ToBytesLE_bytesToU128LE_eq_ofFn (bs : List (BitVec 8)) :
    u128ToBytesLE (bytesToU128LE bs) = List.ofFn (fun i : Fin 16 => bs.getD i.val 0#8) := by
  rw [bytesToU128LE, u128ToBytesLE_u128OfU32sLE,
    u32ToBytesLE_bytesToU32LE, u32ToBytesLE_bytesToU32LE,
    u32ToBytesLE_bytesToU32LE, u32ToBytesLE_bytesToU32LE]
  rfl

theorem extractLsb'_bytesToU128LE (bs : List (BitVec 8)) (j : Fin 16) :
    (bytesToU128LE bs).extractLsb' (8 * j.val) 8 = bs.getD j.val 0#8 := by
  have h := congrArg (fun xs => xs[j.val]?) (u128ToBytesLE_bytesToU128LE_eq_ofFn bs)
  rw [List.getElem?_eq_getElem (by simp [j.isLt]),
    List.getElem?_eq_getElem (by simp [j.isLt])] at h
  have hinj := Option.some.inj h
  simp only [getElem_u128ToBytesLE _ j.val j.isLt, List.getElem_ofFn] at hinj
  exact hinj

@[simp] theorem u128ToBytesLE_bytesToU128LE {bs : List (BitVec 8)} (h : bs.length = 16) :
    u128ToBytesLE (bytesToU128LE bs) = bs := by
  apply List.ext_getElem
  · simp [h]
  · intro j hj1 hj2
    have hj : j < 16 := by omega
    rw [getElem_u128ToBytesLE _ j hj]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2] using
      extractLsb'_bytesToU128LE bs ⟨j, hj⟩

@[simp] theorem bytesToU128LE_u128ToBytesLE (v : BitVec 128) :
    bytesToU128LE (u128ToBytesLE v) = v := by
  apply u128_eq_of_extractBytes; intro j
  rw [extractLsb'_bytesToU128LE, getD_u128ToBytesLE v j.val j.isLt]

@[simp] theorem bytesToU128LE_blockToBytesLE (b : Block) :
    bytesToU128LE (blockToBytesLE b) = b := bytesToU128LE_u128ToBytesLE b

theorem bytesToU128LE_eq_bytesToBlock {bs : List (BitVec 8)} (h : bs.length = 16) :
    bytesToU128LE bs = bytesToBlock bs := by
  calc bytesToU128LE bs = bytesToBlock (blockToBytesLE (bytesToU128LE bs)) :=
         (bytesToBlock_blockToBytesLE _).symm
    _ = bytesToBlock (u128ToBytesLE (bytesToU128LE bs)) := rfl
    _ = bytesToBlock bs := by rw [u128ToBytesLE_bytesToU128LE h]

theorem u128ToBytesLE_xor (a b : BitVec 128) :
    u128ToBytesLE (a ^^^ b) = addRoundKey (u128ToBytesLE a) (u128ToBytesLE b) := by
  apply List.ext_getElem
  · simp [length_addRoundKey]
  · intro j hj1 _
    have hj : j < 16 := by simpa using hj1
    have hxor : (a ^^^ b).extractLsb' (8 * j) 8 =
        a.extractLsb' (8 * j) 8 ^^^ b.extractLsb' (8 * j) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
    simp only [getElem_u128ToBytesLE _ j hj, addRoundKey, List.getElem_ofFn,
      getD_u128ToBytesLE _ j hj, hxor]

theorem bytesToU128LE_addRoundKey (s rk : State) :
    bytesToU128LE (addRoundKey s rk) = bytesToU128LE s ^^^ bytesToU128LE rk := by
  apply u128_eq_of_extractBytes; intro j
  have hxor : (bytesToU128LE s ^^^ bytesToU128LE rk).extractLsb' (8 * j.val) 8 =
      (bytesToU128LE s).extractLsb' (8 * j.val) 8 ^^^
        (bytesToU128LE rk).extractLsb' (8 * j.val) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  have hlen : j.val < (addRoundKey s rk).length := by simp [length_addRoundKey, j.isLt]
  rw [hxor, extractLsb'_bytesToU128LE, extractLsb'_bytesToU128LE, extractLsb'_bytesToU128LE,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp only [addRoundKey, List.getElem_ofFn, Option.getD_some]

/-! ## 2. Byte-Table & $\mathrm{GF}(2^8)$ Agreement Between `Arm64` and `CryptoGames.AES256` -/

private theorem aesSBoxTable_row (hi : Fin 16) :
    (aesSBoxTable.toList.drop (16 * hi.val)).take 16 =
      List.ofFn (fun lo : Fin 16 => UInt8.ofBitVec sboxTable[hi][lo]) := by
  rcases hi with ⟨q, hq⟩; interval_cases q <;> rfl

private theorem aesInvSBoxTable_row (hi : Fin 16) :
    (aesInvSBoxTable.toList.drop (16 * hi.val)).take 16 =
      List.ofFn (fun lo : Fin 16 => UInt8.ofBitVec invSboxTable[hi][lo]) := by
  rcases hi with ⟨q, hq⟩; interval_cases q <;> rfl

private theorem getElem!_by_row16 {arr : Array UInt8}
    (tbl : Vector (Vector (BitVec 8) 16) 16)
    (hrow : ∀ hi : Fin 16, (arr.toList.drop (16 * hi.val)).take 16 =
      List.ofFn (fun lo : Fin 16 => UInt8.ofBitVec tbl[hi][lo]))
    (n : Nat) (hn : n < 256) :
    arr[n]! = UInt8.ofBitVec tbl[n / 16][n % 16] := by
  have h15 := congrArg List.length (hrow ⟨15, by omega⟩)
  simp only [List.length_take, List.length_drop, List.length_ofFn] at h15
  have hsz : 256 ≤ arr.size := by rw [Array.size_eq_length_toList]; omega
  rw [getElem!_pos arr n (by omega), ← Array.getElem_toList]
  have hget := congrArg (fun xs => xs[n % 16]?) (hrow ⟨n / 16, by omega⟩)
  rw [List.getElem?_eq_getElem (by rw [List.length_take, List.length_drop,
      ← Array.size_eq_length_toList]; omega),
    List.getElem?_eq_getElem (by simp; omega)] at hget
  have hinj := Option.some.inj hget
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
    Nat.div_add_mod n 16, Fin.getElem_fin] at hinj
  exact hinj

theorem arm64_aesSBox_eq_sbox (b : BitVec 8) :
    (aesSBoxTable[(UInt8.ofBitVec b).toNat]!).toBitVec = sbox b := by
  rw [getElem!_by_row16 sboxTable aesSBoxTable_row _ (UInt8.toNat_lt _)]
  simp [sbox, show (UInt8.ofBitVec b).toNat = b.toNat from rfl]

theorem arm64_aesInvSBox_eq_invSbox (b : BitVec 8) :
    (aesInvSBoxTable[(UInt8.ofBitVec b).toNat]!).toBitVec = invSbox b := by
  rw [getElem!_by_row16 invSboxTable aesInvSBoxTable_row _ (UInt8.toNat_lt _)]
  simp [invSbox, show (UInt8.ofBitVec b).toNat = b.toNat from rfl]

theorem arm64_gfMul_02_eq (b : BitVec 8) :
    (Arm64.gfMul 2 (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x02#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

theorem arm64_gfMul_03_eq (b : BitVec 8) :
    (Arm64.gfMul 3 (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x03#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

theorem arm64_gfMul_09_eq (b : BitVec 8) :
    (Arm64.gfMul 0x09 (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x09#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

theorem arm64_gfMul_0b_eq (b : BitVec 8) :
    (Arm64.gfMul 0x0b (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x0b#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

theorem arm64_gfMul_0d_eq (b : BitVec 8) :
    (Arm64.gfMul 0x0d (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x0d#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

theorem arm64_gfMul_0e_eq (b : BitVec 8) :
    (Arm64.gfMul 0x0e (UInt8.ofBitVec b)).toBitVec = CryptoGames.AES256.gfMul 0x0e#8 b := by
  simp only [Arm64.gfMul, Std.Legacy.Range.forIn_eq_forIn_range']; revert b; decide

/-! ## 3. Correspondence of `Arm64.evalAesOp` with FIPS 197 Round Transformations -/

private def getByte128 (v : BitVec 128) (i : Nat) : UInt8 :=
  UInt8.ofNat ((v >>> (i * 8)).truncate 8).toNat

private def packUInt8s16
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : UInt8) : BitVec 128 :=
  0#128 ||| (BitVec.ofNat 128 u0.toNat <<< 0) ||| (BitVec.ofNat 128 u1.toNat <<< 8)
        ||| (BitVec.ofNat 128 u2.toNat <<< 16) ||| (BitVec.ofNat 128 u3.toNat <<< 24)
        ||| (BitVec.ofNat 128 u4.toNat <<< 32) ||| (BitVec.ofNat 128 u5.toNat <<< 40)
        ||| (BitVec.ofNat 128 u6.toNat <<< 48) ||| (BitVec.ofNat 128 u7.toNat <<< 56)
        ||| (BitVec.ofNat 128 u8.toNat <<< 64) ||| (BitVec.ofNat 128 u9.toNat <<< 72)
        ||| (BitVec.ofNat 128 u10.toNat <<< 80) ||| (BitVec.ofNat 128 u11.toNat <<< 88)
        ||| (BitVec.ofNat 128 u12.toNat <<< 96) ||| (BitVec.ofNat 128 u13.toNat <<< 104)
        ||| (BitVec.ofNat 128 u14.toNat <<< 112) ||| (BitVec.ofNat 128 u15.toNat <<< 120)

private theorem uInt8_ofNat_toNat (b : BitVec 8) : UInt8.ofNat b.toNat = UInt8.ofBitVec b :=
  congrArg UInt8.ofBitVec (by simp : BitVec.ofNat 8 b.toNat = b)

private theorem getByte128_eq_ofBitVec (v : BitVec 128) (i : Nat) :
    getByte128 v i = UInt8.ofBitVec (v.extractLsb' (8 * i) 8) := by
  have htr : (v >>> (i * 8)).truncate 8 = v.extractLsb' (8 * i) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, Nat.mul_comm]
  rw [getByte128, htr, uInt8_ofNat_toNat]

private theorem getLsbD_ofNat128_uInt8_shift (u : UInt8) (s k : Nat) (hk128 : k < 128) :
    (BitVec.ofNat 128 u.toNat <<< s).getLsbD k =
      (decide (s ≤ k) && decide (k < s + 8) && u.toBitVec.getLsbD (k - s)) := by
  have hof : BitVec.ofNat 128 u.toNat = u.toBitVec.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
  rw [hof]
  simp only [BitVec.getLsbD_shiftLeft, hk128, decide_true, Bool.true_and, BitVec.getLsbD_setWidth]
  by_cases hs : s ≤ k
  · by_cases hlt : k < s + 8
    · simp [hs, hlt, show k - s < 128 by omega]
    · simp [hs, hlt, BitVec.getLsbD_of_ge u.toBitVec (k - s) (by omega)]
  · simp [hs, show k < s by omega]

private theorem u128ToBytesLE_packUInt8s16
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : UInt8) :
    u128ToBytesLE (packUInt8s16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15) =
      [u0.toBitVec, u1.toBitVec, u2.toBitVec, u3.toBitVec,
       u4.toBitVec, u5.toBitVec, u6.toBitVec, u7.toBitVec,
       u8.toBitVec, u9.toBitVec, u10.toBitVec, u11.toBitVec,
       u12.toBitVec, u13.toBitVec, u14.toBitVec, u15.toBitVec] := by
  have hex : ∀ j : Fin 16,
      (packUInt8s16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15).extractLsb'
        (8 * j.val) 8 =
      (#[u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15][j.val]'(by
        simp [j.isLt])).toBitVec := by
    intro ⟨j, hj⟩; interval_cases j <;> {
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp only [packUInt8s16, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
        BitVec.getLsbD_or, BitVec.getLsbD_zero]
      repeat rw [getLsbD_ofNat128_uInt8_shift _ _ _ (by omega)]
      interval_cases k <;> simp
    }
  simp [u128ToBytesLE, List.ofFn_succ, hex]

private theorem evalAesOp_aese_unfold (vd vn : BitVec 128) :
    evalAesOp .AESE vd vn =
      let x := vd ^^^ vn
      packUInt8s16
        aesSBoxTable[(getByte128 x 0).toNat]! aesSBoxTable[(getByte128 x 5).toNat]!
        aesSBoxTable[(getByte128 x 10).toNat]! aesSBoxTable[(getByte128 x 15).toNat]!
        aesSBoxTable[(getByte128 x 4).toNat]! aesSBoxTable[(getByte128 x 9).toNat]!
        aesSBoxTable[(getByte128 x 14).toNat]! aesSBoxTable[(getByte128 x 3).toNat]!
        aesSBoxTable[(getByte128 x 8).toNat]! aesSBoxTable[(getByte128 x 13).toNat]!
        aesSBoxTable[(getByte128 x 2).toNat]! aesSBoxTable[(getByte128 x 7).toNat]!
        aesSBoxTable[(getByte128 x 12).toNat]! aesSBoxTable[(getByte128 x 1).toNat]!
        aesSBoxTable[(getByte128 x 6).toNat]! aesSBoxTable[(getByte128 x 11).toNat]! := by
  rw [evalAesOp]; dsimp only; generalize vd ^^^ vn = x
  simp [getByte128, packUInt8s16, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range']

private theorem evalAesOp_aesd_unfold (vd vn : BitVec 128) :
    evalAesOp .AESD vd vn =
      let x := vd ^^^ vn
      packUInt8s16
        aesInvSBoxTable[(getByte128 x 0).toNat]! aesInvSBoxTable[(getByte128 x 13).toNat]!
        aesInvSBoxTable[(getByte128 x 10).toNat]! aesInvSBoxTable[(getByte128 x 7).toNat]!
        aesInvSBoxTable[(getByte128 x 4).toNat]! aesInvSBoxTable[(getByte128 x 1).toNat]!
        aesInvSBoxTable[(getByte128 x 14).toNat]! aesInvSBoxTable[(getByte128 x 11).toNat]!
        aesInvSBoxTable[(getByte128 x 8).toNat]! aesInvSBoxTable[(getByte128 x 5).toNat]!
        aesInvSBoxTable[(getByte128 x 2).toNat]! aesInvSBoxTable[(getByte128 x 15).toNat]!
        aesInvSBoxTable[(getByte128 x 12).toNat]! aesInvSBoxTable[(getByte128 x 9).toNat]!
        aesInvSBoxTable[(getByte128 x 6).toNat]! aesInvSBoxTable[(getByte128 x 3).toNat]! := by
  rw [evalAesOp]; dsimp only; generalize vd ^^^ vn = x
  simp [getByte128, packUInt8s16, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range']

private theorem evalAesOp_aesmc_unfold (vd vn : BitVec 128) :
    evalAesOp .AESMC vd vn =
      let g := getByte128 vn
      packUInt8s16
        (Arm64.gfMul 2 (g 0) ^^^ Arm64.gfMul 3 (g 1) ^^^ g 2 ^^^ g 3)
        (g 0 ^^^ Arm64.gfMul 2 (g 1) ^^^ Arm64.gfMul 3 (g 2) ^^^ g 3)
        (g 0 ^^^ g 1 ^^^ Arm64.gfMul 2 (g 2) ^^^ Arm64.gfMul 3 (g 3))
        (Arm64.gfMul 3 (g 0) ^^^ g 1 ^^^ g 2 ^^^ Arm64.gfMul 2 (g 3))
        (Arm64.gfMul 2 (g 4) ^^^ Arm64.gfMul 3 (g 5) ^^^ g 6 ^^^ g 7)
        (g 4 ^^^ Arm64.gfMul 2 (g 5) ^^^ Arm64.gfMul 3 (g 6) ^^^ g 7)
        (g 4 ^^^ g 5 ^^^ Arm64.gfMul 2 (g 6) ^^^ Arm64.gfMul 3 (g 7))
        (Arm64.gfMul 3 (g 4) ^^^ g 5 ^^^ g 6 ^^^ Arm64.gfMul 2 (g 7))
        (Arm64.gfMul 2 (g 8) ^^^ Arm64.gfMul 3 (g 9) ^^^ g 10 ^^^ g 11)
        (g 8 ^^^ Arm64.gfMul 2 (g 9) ^^^ Arm64.gfMul 3 (g 10) ^^^ g 11)
        (g 8 ^^^ g 9 ^^^ Arm64.gfMul 2 (g 10) ^^^ Arm64.gfMul 3 (g 11))
        (Arm64.gfMul 3 (g 8) ^^^ g 9 ^^^ g 10 ^^^ Arm64.gfMul 2 (g 11))
        (Arm64.gfMul 2 (g 12) ^^^ Arm64.gfMul 3 (g 13) ^^^ g 14 ^^^ g 15)
        (g 12 ^^^ Arm64.gfMul 2 (g 13) ^^^ Arm64.gfMul 3 (g 14) ^^^ g 15)
        (g 12 ^^^ g 13 ^^^ Arm64.gfMul 2 (g 14) ^^^ Arm64.gfMul 3 (g 15))
        (Arm64.gfMul 3 (g 12) ^^^ g 13 ^^^ g 14 ^^^ Arm64.gfMul 2 (g 15)) := by
  simp [evalAesOp, getByte128, packUInt8s16, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range']

private theorem evalAesOp_aesimc_unfold (vd vn : BitVec 128) :
    evalAesOp .AESIMC vd vn =
      let g := getByte128 vn
      packUInt8s16
        (Arm64.gfMul 0x0e (g 0) ^^^ Arm64.gfMul 0x0b (g 1) ^^^ Arm64.gfMul 0x0d (g 2) ^^^ Arm64.gfMul 0x09 (g 3))
        (Arm64.gfMul 0x09 (g 0) ^^^ Arm64.gfMul 0x0e (g 1) ^^^ Arm64.gfMul 0x0b (g 2) ^^^ Arm64.gfMul 0x0d (g 3))
        (Arm64.gfMul 0x0d (g 0) ^^^ Arm64.gfMul 0x09 (g 1) ^^^ Arm64.gfMul 0x0e (g 2) ^^^ Arm64.gfMul 0x0b (g 3))
        (Arm64.gfMul 0x0b (g 0) ^^^ Arm64.gfMul 0x0d (g 1) ^^^ Arm64.gfMul 0x09 (g 2) ^^^ Arm64.gfMul 0x0e (g 3))
        (Arm64.gfMul 0x0e (g 4) ^^^ Arm64.gfMul 0x0b (g 5) ^^^ Arm64.gfMul 0x0d (g 6) ^^^ Arm64.gfMul 0x09 (g 7))
        (Arm64.gfMul 0x09 (g 4) ^^^ Arm64.gfMul 0x0e (g 5) ^^^ Arm64.gfMul 0x0b (g 6) ^^^ Arm64.gfMul 0x0d (g 7))
        (Arm64.gfMul 0x0d (g 4) ^^^ Arm64.gfMul 0x09 (g 5) ^^^ Arm64.gfMul 0x0e (g 6) ^^^ Arm64.gfMul 0x0b (g 7))
        (Arm64.gfMul 0x0b (g 4) ^^^ Arm64.gfMul 0x0d (g 5) ^^^ Arm64.gfMul 0x09 (g 6) ^^^ Arm64.gfMul 0x0e (g 7))
        (Arm64.gfMul 0x0e (g 8) ^^^ Arm64.gfMul 0x0b (g 9) ^^^ Arm64.gfMul 0x0d (g 10) ^^^ Arm64.gfMul 0x09 (g 11))
        (Arm64.gfMul 0x09 (g 8) ^^^ Arm64.gfMul 0x0e (g 9) ^^^ Arm64.gfMul 0x0b (g 10) ^^^ Arm64.gfMul 0x0d (g 11))
        (Arm64.gfMul 0x0d (g 8) ^^^ Arm64.gfMul 0x09 (g 9) ^^^ Arm64.gfMul 0x0e (g 10) ^^^ Arm64.gfMul 0x0b (g 11))
        (Arm64.gfMul 0x0b (g 8) ^^^ Arm64.gfMul 0x0d (g 9) ^^^ Arm64.gfMul 0x09 (g 10) ^^^ Arm64.gfMul 0x0e (g 11))
        (Arm64.gfMul 0x0e (g 12) ^^^ Arm64.gfMul 0x0b (g 13) ^^^ Arm64.gfMul 0x0d (g 14) ^^^ Arm64.gfMul 0x09 (g 15))
        (Arm64.gfMul 0x09 (g 12) ^^^ Arm64.gfMul 0x0e (g 13) ^^^ Arm64.gfMul 0x0b (g 14) ^^^ Arm64.gfMul 0x0d (g 15))
        (Arm64.gfMul 0x0d (g 12) ^^^ Arm64.gfMul 0x09 (g 13) ^^^ Arm64.gfMul 0x0e (g 14) ^^^ Arm64.gfMul 0x0b (g 15))
        (Arm64.gfMul 0x0b (g 12) ^^^ Arm64.gfMul 0x0d (g 13) ^^^ Arm64.gfMul 0x09 (g 14) ^^^ Arm64.gfMul 0x0e (g 15)) := by
  simp [evalAesOp, getByte128, packUInt8s16, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range']

theorem addRoundKey_comm (s rk : State) : addRoundKey s rk = addRoundKey rk s := by
  simp only [addRoundKey]; congr 1; funext i; exact BitVec.xor_comm _ _

theorem u128ToBytesLE_evalAesOp_aese (rk st : BitVec 128) :
    u128ToBytesLE (evalAesOp .AESE rk st) =
      subBytes (shiftRows (addRoundKey (u128ToBytesLE st) (u128ToBytesLE rk))) := by
  rw [Defs.evalAesOp_aese_comm, evalAesOp_aese_unfold]; dsimp only
  rw [u128ToBytesLE_packUInt8s16]
  simp only [getByte128_eq_ofBitVec, arm64_aesSBox_eq_sbox, ← u128ToBytesLE_xor]
  generalize st ^^^ rk = x
  simp [u128ToBytesLE, shiftRows, subBytes, List.ofFn_succ]

theorem evalAesOp_aese_eq_bytesToU128LE (rk st : BitVec 128) :
    evalAesOp .AESE rk st =
      bytesToU128LE (subBytes (shiftRows (addRoundKey (u128ToBytesLE st) (u128ToBytesLE rk)))) := by
  rw [← u128ToBytesLE_evalAesOp_aese, bytesToU128LE_u128ToBytesLE]

theorem u128ToBytesLE_evalAesOp_aesd (rk st : BitVec 128) :
    u128ToBytesLE (evalAesOp .AESD rk st) =
      invSubBytes (invShiftRows (addRoundKey (u128ToBytesLE st) (u128ToBytesLE rk))) := by
  rw [Defs.evalAesOp_aesd_comm, evalAesOp_aesd_unfold]; dsimp only
  rw [u128ToBytesLE_packUInt8s16]
  simp only [getByte128_eq_ofBitVec, arm64_aesInvSBox_eq_invSbox, ← u128ToBytesLE_xor]
  generalize st ^^^ rk = x
  simp [u128ToBytesLE, invShiftRows, invSubBytes, List.ofFn_succ]

theorem evalAesOp_aesd_eq_bytesToU128LE (rk st : BitVec 128) :
    evalAesOp .AESD rk st =
      bytesToU128LE
        (invSubBytes (invShiftRows (addRoundKey (u128ToBytesLE st) (u128ToBytesLE rk)))) := by
  rw [← u128ToBytesLE_evalAesOp_aesd, bytesToU128LE_u128ToBytesLE]

private theorem toBitVec_xor (a b : UInt8) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

theorem u128ToBytesLE_evalAesOp_aesmc (vd st : BitVec 128) :
    u128ToBytesLE (evalAesOp .AESMC vd st) = mixColumns (u128ToBytesLE st) := by
  rw [evalAesOp_aesmc_unfold]; dsimp only; rw [u128ToBytesLE_packUInt8s16]
  simp only [toBitVec_xor, getByte128_eq_ofBitVec, arm64_gfMul_02_eq, arm64_gfMul_03_eq]
  simp [u128ToBytesLE, mixColumns, mixColumn, List.ofFn_succ]

theorem evalAesOp_aesmc_eq_bytesToU128LE (vd st : BitVec 128) :
    evalAesOp .AESMC vd st = bytesToU128LE (mixColumns (u128ToBytesLE st)) := by
  rw [← u128ToBytesLE_evalAesOp_aesmc vd st, bytesToU128LE_u128ToBytesLE]

theorem u128ToBytesLE_evalAesOp_aesimc (vd st : BitVec 128) :
    u128ToBytesLE (evalAesOp .AESIMC vd st) = invMixColumns (u128ToBytesLE st) := by
  rw [evalAesOp_aesimc_unfold]; dsimp only; rw [u128ToBytesLE_packUInt8s16]
  simp only [toBitVec_xor, getByte128_eq_ofBitVec,
    arm64_gfMul_09_eq, arm64_gfMul_0b_eq, arm64_gfMul_0d_eq, arm64_gfMul_0e_eq]
  simp [u128ToBytesLE, invMixColumns, invMixColumn, List.ofFn_succ]

theorem evalAesOp_aesimc_eq_bytesToU128LE (vd st : BitVec 128) :
    evalAesOp .AESIMC vd st = bytesToU128LE (invMixColumns (u128ToBytesLE st)) := by
  rw [← u128ToBytesLE_evalAesOp_aesimc vd st, bytesToU128LE_u128ToBytesLE]

/-! ## 4. Equivalent Inverse Cipher Algebraic Commutation (FIPS 197 §5.3.5) -/

theorem gfMul_xor_right (c x y : BitVec 8) :
    CryptoGames.AES256.gfMul c (x ^^^ y) =
      CryptoGames.AES256.gfMul c x ^^^ CryptoGames.AES256.gfMul c y :=
  Aes256Roundtrip.gfMul_xor_right c x y

theorem subBytes_shiftRows {s : State} (hs : s.length = 16) :
    subBytes (shiftRows s) = shiftRows (subBytes s) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp_all [subBytes, shiftRows, List.ofFn_succ]

theorem invSubBytes_invShiftRows {s : State} (hs : s.length = 16) :
    invSubBytes (invShiftRows s) = invShiftRows (invSubBytes s) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp_all [invSubBytes, invShiftRows, List.ofFn_succ]

private theorem xor8_4 (a b c d : BitVec 8) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc b, BitVec.xor_comm b c,
    BitVec.xor_assoc c, ← BitVec.xor_assoc]

private theorem xor8_8 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) =
      (a0 ^^^ a1 ^^^ a2 ^^^ a3) ^^^ (b0 ^^^ b1 ^^^ b2 ^^^ b3) := by
  rw [xor8_4 a0 b0 a1 b1, xor8_4 _ _ a2 b2, xor8_4 _ _ a3 b3]

theorem invMixColumn_xor (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) :
    invMixColumn (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) =
      xorWord (invMixColumn a0 a1 a2 a3) (invMixColumn b0 b1 b2 b3) := by
  simp [invMixColumn, xorWord, List.ofFn_succ, gfMul_xor_right, xor8_8]

theorem mixColumn_xor (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) :
    mixColumn (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) =
      xorWord (mixColumn a0 a1 a2 a3) (mixColumn b0 b1 b2 b3) := by
  simp [mixColumn, xorWord, List.ofFn_succ, gfMul_xor_right, xor8_8]

private theorem getD_addRoundKey (s rk : State) (i : Nat) (hi : i < 16) :
    (addRoundKey s rk).getD i 0#8 = s.getD i 0#8 ^^^ rk.getD i 0#8 := by
  have hlen : i < (addRoundKey s rk).length := by simp [length_addRoundKey, hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp only [addRoundKey, List.getElem_ofFn, Option.getD_some]

theorem invMixColumns_addRoundKey (s rk : State) :
    invMixColumns (addRoundKey s rk) = addRoundKey (invMixColumns s) (invMixColumns rk) := by
  have h := getD_addRoundKey s rk
  simp only [invMixColumns, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceMul, Nat.reduceAdd, List.flatten_cons, List.flatten_nil,
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega),
    h 8 (by omega), h 9 (by omega), h 10 (by omega), h 11 (by omega),
    h 12 (by omega), h 13 (by omega), h 14 (by omega), h 15 (by omega),
    invMixColumn_xor]
  simp [invMixColumn, xorWord, addRoundKey, List.ofFn_succ]

theorem mixColumns_addRoundKey (s rk : State) :
    mixColumns (addRoundKey s rk) = addRoundKey (mixColumns s) (mixColumns rk) := by
  have h := getD_addRoundKey s rk
  simp only [mixColumns, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceMul, Nat.reduceAdd, List.flatten_cons, List.flatten_nil,
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega),
    h 8 (by omega), h 9 (by omega), h 10 (by omega), h 11 (by omega),
    h 12 (by omega), h 13 (by omega), h 14 (by omega), h 15 (by omega),
    mixColumn_xor]
  simp [mixColumn, xorWord, addRoundKey, List.ofFn_succ]

theorem u128ToBytesLE_armv8InvExpandedKeys_zero (ek : Vector (BitVec 128) 15) :
    u128ToBytesLE (armv8InvExpandedKeys ek)[0] = u128ToBytesLE ek[14] := rfl

theorem u128ToBytesLE_armv8InvExpandedKeys_mid (ek : Vector (BitVec 128) 15)
    (r : Nat) (hr1 : 1 ≤ r) (hr13 : r ≤ 13) :
    u128ToBytesLE ((armv8InvExpandedKeys ek)[r]'(by omega)) =
      invMixColumns (u128ToBytesLE (ek[14 - r]'(by omega))) := by
  interval_cases r <;> exact u128ToBytesLE_evalAesOp_aesimc 0#128 _

theorem u128ToBytesLE_armv8InvExpandedKeys_last (ek : Vector (BitVec 128) 15) :
    u128ToBytesLE (armv8InvExpandedKeys ek)[14] = u128ToBytesLE ek[0] := rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.OpsEquiv
