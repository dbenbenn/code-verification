/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.OpsEquiv

/-!
# End-to-End ARMv8 Hardware AES-256 Equivalence (`Armv8.Pure.CipherEquiv`)

Proves that the pure ARMv8 Cryptography Extension AES-256 key expansion, inverse key derivation,
single-block encryption/decryption, and 17-block parallel decryption in `Armv8.Defs` agree with the
FIPS 197 AES-256 specifications in `CryptoGames.AES256` (`expandKey256`, `aes256Cipher`,
`aes256InvCipher`, `aes256Enc`, `aes256Dec`), both on typed `(AesKey, Block)` values and directly on
little-endian byte buffers matching `Fixslice64.Equiv` and `CBCProof.CBCDec`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv

open Arm64 (evalAesOp)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconWords bytesToU32LE u32ToBytesLE u128OfU32sLE bytesToU128LE u128ToBytesLE
   armv8SubWord armv8ExpandStep armv8ExpandKeyWords armv8PackRoundKeys armv8ExpandKey
   armv8InvExpandedKeys armv8Encrypt15 armv8Decrypt15 armv8DecryptPar17
   roundKeys15Bytes blocks17Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.OpsEquiv
  (length_u32ToBytesLE u32ToBytesLE_u32OfBytesLE u32OfBytesLE_extractLsb'
   u32ToBytesLE_bytesToU32LE u32ToBytesLE_xor rotateRight8_u32OfBytesLE
   u128ToBytesLE_eq_blockToBytesLE length_u128ToBytesLE getElem_u128ToBytesLE
   u128ToBytesLE_u128OfU32sLE u128ToBytesLE_bytesToU128LE bytesToU128LE_eq_bytesToBlock
   u128ToBytesLE_xor addRoundKey_comm
   u128ToBytesLE_evalAesOp_aese u128ToBytesLE_evalAesOp_aesd
   u128ToBytesLE_evalAesOp_aesmc u128ToBytesLE_evalAesOp_aesimc
   subBytes_shiftRows invSubBytes_invShiftRows invMixColumns_addRoundKey
   u128ToBytesLE_armv8InvExpandedKeys_zero u128ToBytesLE_armv8InvExpandedKeys_mid
   u128ToBytesLE_armv8InvExpandedKeys_last)
open CryptoGames.AES256
  (State Word sbox subBytes invSubBytes shiftRows invShiftRows mixColumns invMixColumns
   addRoundKey rotWord subWord xorWord rcon expandKey256 roundKey
   aes256Cipher aes256InvCipher aes256Enc aes256Dec)
open CryptoGames.CBC (AesKey Block blockToBytesLE bytesToBlock chunks16)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)

private theorem length_addRoundKey (s rk : State) : (addRoundKey s rk).length = 16 := by
  simp [addRoundKey]

private theorem bytesToBlock_blockToBytesLE (b : Block) :
    bytesToBlock (blockToBytesLE b) = b := by
  rw [← u128ToBytesLE_eq_blockToBytesLE,
    ← bytesToU128LE_eq_bytesToBlock (length_u128ToBytesLE b),
    OpsEquiv.bytesToU128LE_u128ToBytesLE]

private theorem chunks16_append_of_length16 (b16 rest : List (BitVec 8)) (hb : b16.length = 16) :
    chunks16 (b16 ++ rest) = bytesToBlock b16 :: chunks16 rest := by
  unfold chunks16
  have hdiv : (b16 ++ rest).length / 16 = 1 + rest.length / 16 := by
    rw [List.length_append, hb]; omega
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_cons, List.length_ofFn, hdiv]; omega
  · intro i hi1 hi2
    cases i with
    | zero =>
      simp [List.take_append_of_le_length (by omega : 16 ≤ b16.length),
        List.take_of_length_le (by omega : b16.length ≤ 16)]
    | succ j =>
      simp only [List.getElem_ofFn, List.getElem_cons_succ]
      rw [show 16 * (j + 1) = b16.length + 16 * j by omega, List.drop_append,
        List.drop_eq_nil_of_le (by omega : b16.length ≤ b16.length + 16 * j), List.nil_append,
        Nat.add_sub_cancel_left]

private theorem chunks16_flatMap (xs : List Block) :
    chunks16 (xs.flatMap blockToBytesLE) = xs := by
  induction xs with
  | nil => simp [chunks16]
  | cons x xs ih =>
    rw [List.flatMap_cons,
      chunks16_append_of_length16 _ _ (by simp [← u128ToBytesLE_eq_blockToBytesLE]),
      bytesToBlock_blockToBytesLE, ih]

/-! ## 1. 32-Byte Little-Endian Key Buffer Round-Trips (`keyToBytes32` / `bytesToKey32`) -/

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp [hi, show i < 256 by omega]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hb : b.getLsbD (8 * (j + 1) + i) = false :=
    BitVec.getLsbD_of_ge b _ (by omega)
  simp [show ¬ (8 * (j + 1) + i < 8) by omega, show 8 * (j + 1) + i < 256 by omega,
    show 8 * (j + 1) + i - 8 = 8 * j + i by omega, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      change ((bytesToKey32 rest <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 = _
      rw [extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

/-- `keyToBytes32` inverts `bytesToKey32` on every 32-byte key buffer. -/
theorem keyToBytes32_bytesToKey32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j _ h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

/-- `bytesToKey32` inverts `keyToBytes32` on every 256-bit key. -/
@[simp] theorem bytesToKey32_keyToBytes32 (k : AesKey) :
    bytesToKey32 (keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < (keyToBytes32 k).length := by simp [keyToBytes32]; omega
  have hex := extractLsb'_bytesToKey32 (keyToBytes32 k) (i / 8) hj (by omega)
  conv_rhs at hex => simp only [keyToBytes32, List.getElem_ofFn]
  have hbit := congrArg (fun x => x.getLsbD (i % 8)) hex
  simpa [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, Nat.div_add_mod i 8] using hbit

@[simp] theorem length_keyToBytes32 (k : AesKey) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

/-! ## 2. ARMv8 Key Schedule Equivalence (`armv8ExpandKeyWords` & `armv8ExpandKey`) -/

private theorem u32ToBytesLE_extractLsb'_zero (v : BitVec 128) :
    u32ToBytesLE (v.extractLsb' 0 32) = (u128ToBytesLE v).take 4 := by
  have hex : ∀ j : Nat, j < 4 → (v.extractLsb' 0 32).extractLsb' (8 * j) 8 =
      v.extractLsb' (8 * j) 8 := by
    intro j hj; apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk, show 8 * j + k < 32 by omega]
  simp [u32ToBytesLE, u128ToBytesLE, List.ofFn_succ,
    hex 0 (by omega), hex 1 (by omega), hex 2 (by omega), hex 3 (by omega)]

theorem u32ToBytesLE_armv8SubWord (w : BitVec 32) :
    u32ToBytesLE (armv8SubWord w) = subWord (u32ToBytesLE w) := by
  unfold armv8SubWord; dsimp only
  rw [u32ToBytesLE_extractLsb'_zero, Defs.evalAesOp_aese_comm, u128ToBytesLE_evalAesOp_aese,
    ← u128ToBytesLE_xor, BitVec.xor_zero]
  change (subBytes (shiftRows (u128ToBytesLE (u128OfU32sLE w w w w)))).take 4 = _
  rw [u128ToBytesLE_u128OfU32sLE]
  simp [u32ToBytesLE, shiftRows, subBytes, subWord, List.ofFn_succ]

theorem u32ToBytesLE_rotateRight8 (w : BitVec 32) :
    u32ToBytesLE (w.rotateRight 8) = rotWord (u32ToBytesLE w) := by
  conv_lhs => rw [← u32OfBytesLE_extractLsb' w]
  rw [rotateRight8_u32OfBytesLE, u32ToBytesLE_u32OfBytesLE]
  rfl

private theorem rotWord_subWord_u32 (w : BitVec 32) :
    rotWord (subWord (u32ToBytesLE w)) = subWord (rotWord (u32ToBytesLE w)) := by
  simp [u32ToBytesLE, subWord, rotWord]

private theorem xorWord_comm (u v : Word) : xorWord u v = xorWord v u := by
  simp only [xorWord]; congr 1; funext j; exact BitVec.xor_comm _ _

private theorem u32ToBytesLE_aesRconWords_getD (m : Fin 7) :
    u32ToBytesLE (aesRconWords.getD m.val 0#32) = [rcon.getD m.val 0#8, 0#8, 0#8, 0#8] := by
  revert m; decide

private def ksStepWord (w : List Word) (i : Nat) : Word :=
  let temp := w.getD (i - 1) []
  let temp :=
    if i % 8 = 0 then
      xorWord (subWord (rotWord temp)) [rcon.getD (i / 8 - 1) 0#8, 0#8, 0#8, 0#8]
    else if i % 8 = 4 then
      subWord temp
    else
      temp
  xorWord (w.getD (i - 8) []) temp

private def ksInitWords (key : List (BitVec 8)) : List Word :=
  List.ofFn fun i : Fin 8 =>
    [key.getD (4 * i.val) 0#8, key.getD (4 * i.val + 1) 0#8,
     key.getD (4 * i.val + 2) 0#8, key.getD (4 * i.val + 3) 0#8]

private def ksFold (w0 : List Word) (n : Nat) : List Word :=
  Fin.foldl n (fun w (k : Fin n) => w ++ [ksStepWord w (8 + k.val)]) w0

private def hwInitWords (key : List (BitVec 8)) : Vector (BitVec 32) 60 :=
  Vector.ofFn fun j : Fin 60 =>
    if j.val < 8 then bytesToU32LE key (4 * j.val) else 0#32

private def hwFold (init : Vector (BitVec 32) 60) (n : Nat) (hn : n ≤ 52) :
    Vector (BitVec 32) 60 :=
  Fin.foldl n (fun ws (k : Fin n) => armv8ExpandStep ws ⟨k.val, by omega⟩) init

private theorem ksFold_succ (w0 : List Word) (n : Nat) :
    ksFold w0 (n + 1) = ksFold w0 n ++ [ksStepWord (ksFold w0 n) (8 + n)] := by
  unfold ksFold; rw [Fin.foldl_succ_last]; rfl

private theorem hwFold_succ (init : Vector (BitVec 32) 60) (n : Nat) (hn : n + 1 ≤ 52) :
    hwFold init (n + 1) hn = armv8ExpandStep (hwFold init n (by omega)) ⟨n, by omega⟩ := by
  unfold hwFold; rw [Fin.foldl_succ_last]; rfl

private theorem getD_append_of_lt {α : Type} (xs ys : List α) (d : α) (j : Nat) (h : j < xs.length) :
    (xs ++ ys).getD j d = xs.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_singleton_of_len {α : Type} (xs : List α) (y d : α) (k : Nat)
    (hk : xs.length = k) : (xs ++ [y]).getD k d = y := by
  subst hk; simp [List.getD_eq_getElem?_getD]

private theorem ksFold_eq_hwFold (key : List (BitVec 8)) (n : Nat) (hn : n ≤ 52) :
    (ksFold (ksInitWords key) n).length = 8 + n ∧
    ∀ j : Nat, (hj : j < 8 + n) →
      (ksFold (ksInitWords key) n).getD j [] =
        u32ToBytesLE ((hwFold (hwInitWords key) n hn)[j]'(by omega)) := by
  induction n with
  | zero =>
    refine ⟨by simp [ksFold, ksInitWords], fun j hj => ?_⟩
    have hlt : j < (ksInitWords key).length := by simp [ksInitWords]; omega
    simp only [ksFold, hwFold, Fin.foldl_zero, hwInitWords, Vector.getElem_ofFn,
      show j < 8 by omega, ↓reduceIte, u32ToBytesLE_bytesToU32LE]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp only [ksInitWords, List.getElem_ofFn, Option.getD_some]
  | succ n ih =>
    obtain ⟨hlen, hwords⟩ := ih (by omega)
    rw [ksFold_succ, hwFold_succ _ n hn]
    refine ⟨by simp [hlen]; omega, fun j hj => ?_⟩
    by_cases hlt : j < 8 + n
    · have hj_len : j < (ksFold (ksInitWords key) n).length := by omega
      rw [getD_append_of_lt _ _ _ j hj_len, hwords j hlt]
      unfold armv8ExpandStep; dsimp only
      rw [Vector.getElem_setIfInBounds_ne (by omega) (by omega)]
    · have hjeq : j = 8 + n := by omega
      subst hjeq
      rw [getD_append_singleton_of_len _ _ _ (8 + n) hlen]
      unfold armv8ExpandStep ksStepWord; dsimp only
      have hidx : n + 8 = 8 + n := by omega
      simp only [hidx]
      rw [Vector.getElem_setIfInBounds_self (by omega), u32ToBytesLE_xor,
        show 8 + n - 1 = n + 7 by omega, show 8 + n - 8 = n by omega,
        hwords n (by omega), hwords (n + 7) (by omega)]
      by_cases hm0 : (8 + n) % 8 = 0
      · have hrc_lt : (8 + n) / 8 - 1 < 7 := by omega
        simp only [hm0, Nat.reduceEqDiff, ↓reduceIte, u32ToBytesLE_xor, u32ToBytesLE_rotateRight8,
          u32ToBytesLE_armv8SubWord, rotWord_subWord_u32,
          u32ToBytesLE_aesRconWords_getD ⟨(8 + n) / 8 - 1, hrc_lt⟩,
          xorWord_comm [rcon.getD ((8 + n) / 8 - 1) 0#8, 0#8, 0#8, 0#8]]
      · by_cases hm4 : (8 + n) % 8 = 4
        · simp only [hm4, Nat.reduceEqDiff, ↓reduceIte, u32ToBytesLE_armv8SubWord]
        · simp only [hm0, hm4, ↓reduceIte]

theorem u32ToBytesLE_armv8ExpandKeyWords (keyBytes : List (BitVec 8)) (j : Nat) (hj : j < 60) :
    u32ToBytesLE (armv8ExpandKeyWords keyBytes)[j] = (expandKey256 keyBytes).getD j [] := by
  have hexp : expandKey256 keyBytes = ksFold (ksInitWords keyBytes) 52 := rfl
  have hhw : armv8ExpandKeyWords keyBytes = hwFold (hwInitWords keyBytes) 52 (by omega) := rfl
  rw [hexp, hhw]
  exact ((ksFold_eq_hwFold keyBytes 52 (by omega)).2 j (by omega)).symm

private theorem armv8PackRoundKeys_getElem (ws : Vector (BitVec 32) 60) (r : Nat) (hr : r < 15) :
    (armv8PackRoundKeys ws)[r] =
      u128OfU32sLE (ws[4 * r]'(by omega)) (ws[4 * r + 1]'(by omega))
        (ws[4 * r + 2]'(by omega)) (ws[4 * r + 3]'(by omega)) := by
  simp [armv8PackRoundKeys]

private theorem u128OfU32sLE_eq_roundKey (w0 w1 w2 w3 : BitVec 32) (w : List Word) (r : Nat)
    (hw0 : u32ToBytesLE w0 = w.getD (4 * r) [])
    (hw1 : u32ToBytesLE w1 = w.getD (4 * r + 1) [])
    (hw2 : u32ToBytesLE w2 = w.getD (4 * r + 2) [])
    (hw3 : u32ToBytesLE w3 = w.getD (4 * r + 3) []) :
    u128ToBytesLE (u128OfU32sLE w0 w1 w2 w3) = roundKey w r := by
  rw [u128ToBytesLE_u128OfU32sLE]
  apply List.ext_getElem
  · simp [roundKey]
  · intro i hi1 _
    have hi : i < 16 := by simpa [u32ToBytesLE] using hi1
    simp only [roundKey, List.getElem_ofFn]
    interval_cases i <;>
      simp only [Nat.reduceDiv, Nat.reduceMod, Nat.add_zero, ← hw0, ← hw1, ← hw2, ← hw3] <;>
      rfl

/-- Every round key produced by `armv8ExpandKey keyBytes` (`Nat`-indexed) matches `roundKey`. -/
theorem u128ToBytesLE_armv8ExpandKey_nat (keyBytes : List (BitVec 8)) (r : Nat) (hr : r < 15) :
    u128ToBytesLE (armv8ExpandKey keyBytes)[r] = roundKey (expandKey256 keyBytes) r := by
  rw [armv8ExpandKey, armv8PackRoundKeys_getElem _ r hr]
  exact u128OfU32sLE_eq_roundKey _ _ _ _ _ r
    (u32ToBytesLE_armv8ExpandKeyWords keyBytes (4 * r) (by omega))
    (u32ToBytesLE_armv8ExpandKeyWords keyBytes (4 * r + 1) (by omega))
    (u32ToBytesLE_armv8ExpandKeyWords keyBytes (4 * r + 2) (by omega))
    (u32ToBytesLE_armv8ExpandKeyWords keyBytes (4 * r + 3) (by omega))

/-- Every round key produced by `armv8ExpandKey keyBytes` (`Fin 15`-indexed) matches `roundKey`. -/
theorem u128ToBytesLE_armv8ExpandKey (keyBytes : List (BitVec 8)) (r : Fin 15) :
    u128ToBytesLE (armv8ExpandKey keyBytes)[r] = roundKey (expandKey256 keyBytes) r.val :=
  u128ToBytesLE_armv8ExpandKey_nat keyBytes r.val r.isLt

theorem armv8ExpandKey_getElem (keyBytes : List (BitVec 8)) (r : Fin 15) :
    (armv8ExpandKey keyBytes)[r] = bytesToU128LE (roundKey (expandKey256 keyBytes) r.val) := by
  rw [← u128ToBytesLE_armv8ExpandKey, OpsEquiv.bytesToU128LE_u128ToBytesLE]

@[simp] theorem length_roundKeys15Bytes (rks : Vector (BitVec 128) 15) :
    (roundKeys15Bytes rks).length = 240 := by
  have hlen : rks.toList.length = 15 := rks.length_toList
  rcases h : rks.toList with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7,
    _ | ⟨x8, _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp_all [roundKeys15Bytes]

/-! ## 3. Single-Block Encryption Equivalence (`armv8Encrypt15` vs `aes256Cipher` / `aes256Enc`) -/

private def hwEncFold (ek : Vector (BitVec 128) 15) (blk : BitVec 128)
    (n : Nat) (hn : n ≤ 13) : BitVec 128 :=
  Fin.foldl n (fun s (r : Fin n) =>
    evalAesOp .AESMC 0#128 (evalAesOp .AESE (ek[r.val]'(by omega)) s)) blk

private def fipsEncFold (w : List Word) (s0 : State) (n : Nat) : State :=
  Fin.foldl n (fun s (r : Fin n) =>
    addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (r.val + 1))) s0

private theorem hwEncFold_succ (ek : Vector (BitVec 128) 15) (blk : BitVec 128)
    (n : Nat) (hn : n + 1 ≤ 13) :
    hwEncFold ek blk (n + 1) hn =
      evalAesOp .AESMC 0#128 (evalAesOp .AESE (ek[n]'(by omega))
        (hwEncFold ek blk n (by omega))) := by
  unfold hwEncFold; rw [Fin.foldl_succ_last]; rfl

private theorem fipsEncFold_succ (w : List Word) (s0 : State) (n : Nat) :
    fipsEncFold w s0 (n + 1) =
      addRoundKey (mixColumns (shiftRows (subBytes (fipsEncFold w s0 n))))
        (roundKey w (n + 1)) := by
  unfold fipsEncFold; rw [Fin.foldl_succ_last]; rfl

private theorem fipsEncFold_eq_hwEncFold (keyBytes : List (BitVec 8)) (blk : BitVec 128)
    (n : Nat) (hn : n ≤ 13) :
    fipsEncFold (expandKey256 keyBytes)
      (addRoundKey (u128ToBytesLE blk) (roundKey (expandKey256 keyBytes) 0)) n =
      addRoundKey (u128ToBytesLE (hwEncFold (armv8ExpandKey keyBytes) blk n hn))
        (roundKey (expandKey256 keyBytes) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fipsEncFold_succ, hwEncFold_succ _ _ n hn, ih (by omega),
      ← subBytes_shiftRows (length_addRoundKey _ _),
      u128ToBytesLE_evalAesOp_aesmc, u128ToBytesLE_evalAesOp_aese,
      u128ToBytesLE_armv8ExpandKey_nat keyBytes n (by omega)]

/-- Byte-level encryption equivalence for arbitrary key byte list and 128-bit block. -/
theorem u128ToBytesLE_armv8Encrypt15 (keyBytes : List (BitVec 8)) (blk : BitVec 128) :
    u128ToBytesLE (armv8Encrypt15 (armv8ExpandKey keyBytes) blk) =
      aes256Cipher keyBytes (u128ToBytesLE blk) := by
  have h13 := fipsEncFold_eq_hwEncFold keyBytes blk 13 (by omega)
  have hhw : Fin.foldl 13 (fun s (r : Fin 13) =>
      evalAesOp .AESMC 0#128 (evalAesOp .AESE (armv8ExpandKey keyBytes)[r.val] s)) blk =
      hwEncFold (armv8ExpandKey keyBytes) blk 13 (by omega) := rfl
  have hfips : aes256Cipher keyBytes (u128ToBytesLE blk) =
      addRoundKey (shiftRows (subBytes (fipsEncFold (expandKey256 keyBytes)
        (addRoundKey (u128ToBytesLE blk) (roundKey (expandKey256 keyBytes) 0)) 13)))
        (roundKey (expandKey256 keyBytes) 14) := rfl
  unfold armv8Encrypt15; dsimp only
  rw [hhw, u128ToBytesLE_xor, addRoundKey_comm, u128ToBytesLE_evalAesOp_aese,
    u128ToBytesLE_armv8ExpandKey_nat keyBytes 14 (by omega),
    u128ToBytesLE_armv8ExpandKey_nat keyBytes 13 (by omega),
    hfips, h13, subBytes_shiftRows (length_addRoundKey _ _)]

/-- Typed `CBC.AesKey` / `CBC.Block` encryption equivalence (`armv8Encrypt15 = aes256Enc`). -/
theorem armv8Encrypt15_eq_aes256Enc (k : AesKey) (b : Block) :
    armv8Encrypt15 (armv8ExpandKey (keyToBytes32 k)) b = aes256Enc k b := by
  rw [← bytesToBlock_blockToBytesLE (armv8Encrypt15 _ _), ← u128ToBytesLE_eq_blockToBytesLE,
    u128ToBytesLE_armv8Encrypt15, u128ToBytesLE_eq_blockToBytesLE, ← aes256Enc]

/-- 32-byte key buffer corollary matching `Fixslice64.Equiv`: `armv8Encrypt15` under `keyBytes`
(`keyBytes.length = 32`) equals `aes256Enc (bytesToKey32 keyBytes) b`. -/
theorem armv8Encrypt15_bytesToKey32 {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) :
    armv8Encrypt15 (armv8ExpandKey keyBytes) b = aes256Enc (bytesToKey32 keyBytes) b := by
  conv_lhs => rw [← keyToBytes32_bytesToKey32 hkey]
  exact armv8Encrypt15_eq_aes256Enc (bytesToKey32 keyBytes) b

theorem u128ToBytesLE_armv8Encrypt15_le {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) :
    u128ToBytesLE (armv8Encrypt15 (armv8ExpandKey keyBytes) b) =
      blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) b) := by
  rw [armv8Encrypt15_bytesToKey32 hkey, u128ToBytesLE_eq_blockToBytesLE]

/-- Direct 16-byte buffer encryption corollary for `CbcEncrypt`: rewrites
`u128ToBytesLE (armv8Encrypt15 (armv8ExpandKey keyBytes) (bytesToU128LE blkBytes))` directly to
`blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) (bytesToBlock blkBytes))`. -/
theorem u128ToBytesLE_armv8Encrypt15_bytes {keyBytes blkBytes : List (BitVec 8)}
    (hkey : keyBytes.length = 32) (hblk : blkBytes.length = 16) :
    u128ToBytesLE (armv8Encrypt15 (armv8ExpandKey keyBytes) (bytesToU128LE blkBytes)) =
      blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) (bytesToBlock blkBytes)) := by
  rw [bytesToU128LE_eq_bytesToBlock hblk, u128ToBytesLE_armv8Encrypt15_le hkey]

/-! ## 4. Single-Block & 17-Block Parallel Decryption Equivalence (`armv8Decrypt15` / `Par17`) -/

private def hwDecFold (dk : Vector (BitVec 128) 15) (blk : BitVec 128)
    (n : Nat) (hn : n ≤ 13) : BitVec 128 :=
  Fin.foldl n (fun s (r : Fin n) =>
    evalAesOp .AESIMC 0#128 (evalAesOp .AESD (dk[r.val]'(by omega)) s)) blk

private def fipsDecFold (w : List Word) (s0 : State) (n : Nat) : State :=
  Fin.foldl n (fun s (j : Fin n) =>
    invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) (roundKey w (13 - j.val)))) s0

private theorem hwDecFold_succ (dk : Vector (BitVec 128) 15) (blk : BitVec 128)
    (n : Nat) (hn : n + 1 ≤ 13) :
    hwDecFold dk blk (n + 1) hn =
      evalAesOp .AESIMC 0#128 (evalAesOp .AESD (dk[n]'(by omega))
        (hwDecFold dk blk n (by omega))) := by
  unfold hwDecFold; rw [Fin.foldl_succ_last]; rfl

private theorem fipsDecFold_succ (w : List Word) (s0 : State) (n : Nat) :
    fipsDecFold w s0 (n + 1) =
      invMixColumns (addRoundKey (invSubBytes (invShiftRows (fipsDecFold w s0 n)))
        (roundKey w (13 - n))) := by
  unfold fipsDecFold; rw [Fin.foldl_succ_last]; rfl

private theorem fipsDecFold_eq_hwDecFold (keyBytes : List (BitVec 8)) (blk : BitVec 128)
    (n : Nat) (hn : n ≤ 13) :
    let dk := armv8InvExpandedKeys (armv8ExpandKey keyBytes)
    fipsDecFold (expandKey256 keyBytes)
      (addRoundKey (u128ToBytesLE blk) (roundKey (expandKey256 keyBytes) 14)) n =
      addRoundKey (u128ToBytesLE (hwDecFold dk blk n hn))
        (u128ToBytesLE (dk[n]'(by omega))) := by
  intro dk
  induction n with
  | zero =>
    have hdk0 : u128ToBytesLE dk[0] = roundKey (expandKey256 keyBytes) 14 := by
      rw [u128ToBytesLE_armv8InvExpandedKeys_zero]
      exact u128ToBytesLE_armv8ExpandKey_nat keyBytes 14 (by omega)
    simp only [fipsDecFold, hwDecFold, Fin.foldl_zero] at hdk0 ⊢
    rw [hdk0]
  | succ n ih =>
    rw [fipsDecFold_succ, hwDecFold_succ _ _ n hn, ih (by omega), invMixColumns_addRoundKey,
      u128ToBytesLE_evalAesOp_aesimc, u128ToBytesLE_evalAesOp_aesd]
    have hdk_mid : u128ToBytesLE (dk[n + 1]'(by omega)) =
        invMixColumns (roundKey (expandKey256 keyBytes) (13 - n)) := by
      rw [u128ToBytesLE_armv8InvExpandedKeys_mid _ (n + 1) (by omega) hn,
        u128ToBytesLE_armv8ExpandKey_nat keyBytes (14 - (n + 1)) (by omega),
        show 14 - (n + 1) = 13 - n by omega]
    rw [hdk_mid]

/-- Byte-level decryption equivalence via the Equivalent Inverse Cipher (FIPS 197 §5.3.5). -/
theorem u128ToBytesLE_armv8Decrypt15 (keyBytes : List (BitVec 8)) (blk : BitVec 128) :
    u128ToBytesLE
      (armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blk) =
      aes256InvCipher keyBytes (u128ToBytesLE blk) := by
  let dk := armv8InvExpandedKeys (armv8ExpandKey keyBytes)
  have h13 := fipsDecFold_eq_hwDecFold keyBytes blk 13 (by omega)
  dsimp only at h13
  have hhw : Fin.foldl 13 (fun s (r : Fin 13) =>
      evalAesOp .AESIMC 0#128 (evalAesOp .AESD dk[r.val] s)) blk =
      hwDecFold dk blk 13 (by omega) := rfl
  have hfips : aes256InvCipher keyBytes (u128ToBytesLE blk) =
      addRoundKey (invSubBytes (invShiftRows (fipsDecFold (expandKey256 keyBytes)
        (addRoundKey (u128ToBytesLE blk) (roundKey (expandKey256 keyBytes) 14)) 13)))
        (roundKey (expandKey256 keyBytes) 0) := rfl
  have hdk14 : u128ToBytesLE dk[14] = roundKey (expandKey256 keyBytes) 0 := by
    rw [u128ToBytesLE_armv8InvExpandedKeys_last]
    exact u128ToBytesLE_armv8ExpandKey_nat keyBytes 0 (by omega)
  change u128ToBytesLE (armv8Decrypt15 dk blk) = _
  unfold armv8Decrypt15; dsimp only
  rw [hhw, u128ToBytesLE_xor, addRoundKey_comm, u128ToBytesLE_evalAesOp_aesd, hdk14, hfips, h13]

/-- Typed `CBC.AesKey` / `CBC.Block` decryption equivalence (`armv8Decrypt15 = aes256Dec`). -/
theorem armv8Decrypt15_eq_aes256Dec (k : AesKey) (b : Block) :
    armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey (keyToBytes32 k))) b =
      aes256Dec k b := by
  rw [← bytesToBlock_blockToBytesLE (armv8Decrypt15 _ _), ← u128ToBytesLE_eq_blockToBytesLE,
    u128ToBytesLE_armv8Decrypt15, u128ToBytesLE_eq_blockToBytesLE, ← aes256Dec]

theorem armv8Decrypt15_bytesToKey32 {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) :
    armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) b =
      aes256Dec (bytesToKey32 keyBytes) b := by
  conv_lhs => rw [← keyToBytes32_bytesToKey32 hkey]
  exact armv8Decrypt15_eq_aes256Dec (bytesToKey32 keyBytes) b

theorem u128ToBytesLE_armv8Decrypt15_le {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) :
    u128ToBytesLE (armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) b) =
      blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) b) := by
  rw [armv8Decrypt15_bytesToKey32 hkey, u128ToBytesLE_eq_blockToBytesLE]

theorem u128ToBytesLE_armv8Decrypt15_bytes {keyBytes blkBytes : List (BitVec 8)}
    (hkey : keyBytes.length = 32) (hblk : blkBytes.length = 16) :
    u128ToBytesLE
      (armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey keyBytes))
        (bytesToU128LE blkBytes)) =
      blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) (bytesToBlock blkBytes)) := by
  rw [bytesToU128LE_eq_bytesToBlock hblk, u128ToBytesLE_armv8Decrypt15_le hkey]

/-- 17-block parallel decryption equivalence on `Vector Block 17`. -/
theorem armv8DecryptPar17_eq_aes256Dec (k : AesKey) (blks : Vector (BitVec 128) 17) :
    armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey (keyToBytes32 k))) blks =
      blks.map (aes256Dec k) := by
  unfold armv8DecryptPar17
  congr 1; funext b
  exact armv8Decrypt15_eq_aes256Dec k b

theorem armv8DecryptPar17_bytesToKey32 {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (blks : Vector (BitVec 128) 17) :
    armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blks =
      blks.map (aes256Dec (bytesToKey32 keyBytes)) := by
  unfold armv8DecryptPar17
  congr 1; funext b
  exact armv8Decrypt15_bytesToKey32 hkey b

theorem armv8DecryptPar17_getElem {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (blks : Vector (BitVec 128) 17) (i : Nat) (hi : i < 17) :
    (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blks)[i] =
      aes256Dec (bytesToKey32 keyBytes) blks[i] := by
  rw [armv8DecryptPar17_bytesToKey32 hkey, Vector.getElem_map]

theorem blocks17Bytes_eq_flatMap (blks : Vector (BitVec 128) 17) :
    blocks17Bytes blks = blks.toList.flatMap blockToBytesLE := by
  simp only [blocks17Bytes, List.flatMap_def]
  rfl

@[simp] theorem length_blocks17Bytes (blks : Vector (BitVec 128) 17) :
    (blocks17Bytes blks).length = 272 := by
  have hlen : blks.toList.length = 17 := blks.length_toList
  rcases h : blks.toList with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7,
    _ | ⟨x8, _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14, _ | ⟨x15, _ | ⟨x16, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp_all [blocks17Bytes]

theorem chunks16_blocks17Bytes (blks : Vector (BitVec 128) 17) :
    chunks16 (blocks17Bytes blks) = blks.toList := by
  rw [blocks17Bytes_eq_flatMap, chunks16_flatMap]

/-- Flat 272-byte output of `armv8DecryptPar17` equals the concatenated `blockToBytesLE` outputs
of `aes256Dec (bytesToKey32 keyBytes)` across the 17 input blocks. -/
theorem blocks17Bytes_armv8DecryptPar17 {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (blks : Vector (BitVec 128) 17) :
    blocks17Bytes (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blks) =
      (blks.toList.map (aes256Dec (bytesToKey32 keyBytes))).flatMap blockToBytesLE := by
  rw [armv8DecryptPar17_bytesToKey32 hkey, blocks17Bytes_eq_flatMap, Vector.toList_map]

/-- Slice-indexed 272-byte characterization of `blocks17Bytes (armv8DecryptPar17 ...)` in terms of
the 17 consecutive 16-byte input slices `(ctBytes.drop (16 * i)).take 16` (`chunks16 ctBytes`). -/
theorem blocks17Bytes_armv8DecryptPar17_of_bytes {keyBytes ctBytes : List (BitVec 8)}
    (hkey : keyBytes.length = 32) {blks : Vector (BitVec 128) 17}
    (hct : blocks17Bytes blks = ctBytes) :
    blocks17Bytes (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blks) =
      ((chunks16 ctBytes).map (aes256Dec (bytesToKey32 keyBytes))).flatMap blockToBytesLE ∧
    blocks17Bytes (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey keyBytes)) blks) =
      (List.ofFn fun i : Fin 17 =>
        blockToBytesLE (aes256Dec (bytesToKey32 keyBytes)
          (bytesToBlock ((ctBytes.drop (16 * i.val)).take 16)))).flatten := by
  have hchunks : chunks16 ctBytes = blks.toList := by
    rw [← hct, chunks16_blocks17Bytes]
  have hlen272 : ctBytes.length / 16 = 17 := by
    rw [← hct, length_blocks17Bytes]
  refine ⟨?_, ?_⟩
  · rw [blocks17Bytes_armv8DecryptPar17 hkey, hchunks]
  · rw [blocks17Bytes_armv8DecryptPar17 hkey, ← hchunks]
    unfold chunks16
    revert hlen272
    generalize ctBytes.length / 16 = m
    intro hm; subst hm
    simp only [List.flatMap_def, List.map_ofFn]
    rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv
