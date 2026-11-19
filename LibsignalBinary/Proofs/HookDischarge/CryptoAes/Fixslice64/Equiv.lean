/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixEquiv
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec

/-!
# End-to-End 64-Bit Fixslice AES-256 Equivalence (`Fixslice64.Equiv`)

Proves that the pure 64-bit fixslice algorithms in `Fixslice64.Model`
(`aes256KeyScheduleFs`, `aes256EncryptFs`, `aes256DecryptFs`) equal the FIPS 197 specifications
in `Spec.Aes256` (`expandKey256`, `aes256Cipher`, `aes256InvCipher`, `aes256Enc`, `aes256Dec`)
simultaneously across all four 128-bit lanes, without unrolling the 14 rounds:

- `aes256KeyScheduleFs_rk0`, `aes256KeyScheduleFs_getRound`, `aes256KeyScheduleFs_rk14`:
  characterizes all 15 fixsliced round keys produced by `aes256KeyScheduleFs`;
- `aes256EncryptFs_eq`:
  `aes256EncryptFs (aes256KeyScheduleFs key) blocks = blocks.map (aes256Cipher key)`;
- `aes256DecryptFs_eq`:
  `aes256DecryptFs (aes256KeyScheduleFs key) blocks = blocks.map (aes256InvCipher key)`;
- `aes256EncryptFs_le` / `aes256DecryptFs_le` and `keyToBytes32_bytesToKey32`:
  corollaries on little-endian `CBC.AesKey` and `CBC.Block` matching `aes256Enc` and `aes256Dec`.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Equiv

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
  (State Word sbox subBytes invSubBytes shiftRows invShiftRows mixColumns invMixColumns
   addRoundKey rotWord subWord xorWord rcon expandKey256 roundKey
   aes256Cipher aes256InvCipher aes256Enc aes256Dec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
  (length_subBytes length_invSubBytes length_shiftRows length_invShiftRows
   length_mixColumns length_invMixColumns length_addRoundKey length_roundKey
   length_aes256Cipher length_aes256InvCipher)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (FsState Blocks4 FsKeys256 ror64 rorDistance bitslice invBitslice
   subBytesFs subBytesNots invSubBytesFs
   shiftRows2 invShiftRows1 invShiftRows2 invShiftRows3
   mixColumnsQ invMixColumnsQ addRoundKeyFs addRoundConstantBit
   xorColumnWord xorColumnsFs ksEvenStep ksOddStep aes256KeyScheduleFs
   encRoundFs aes256EncryptFs decRoundFs aes256DecryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing
  (Blocks4.Wf Blocks4.wf_map Blocks4.wf_replicate state_eq_of_getD
   getLsbD_bitslice invBitslice_bitslice eq_bitslice_of_getLsbD
   shiftRowsPow invShiftRowsPow length_shiftRowsPow length_invShiftRowsPow
   shiftRowsPow_zero shiftRowsPow_one invShiftRowsPow_one shiftRowsPow_shiftRowsPow
   shiftRowsPow_subBytes shiftRowsPow_invSubBytes shiftRowsPow_addRoundKey
   shiftRows2_bitslice invShiftRows1_bitslice invShiftRows2_bitslice invShiftRows3_bitslice)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxEquiv
  (subBytesNots_subBytesFs_bitslice invSubBytesFs_subBytesNots_bitslice)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixEquiv
  (addRoundKeyFs_comm addRoundKeyFs_assoc subBytesNots_eq_addRoundKeyFs
   addRoundKeyFs_bitslice mixColumnsQ_subBytesNots invMixColumnsQ_subBytesNots
   mixColumnsQ_bitslice invMixColumnsQ_bitslice)
open CryptoGames.CBC
  (AesKey Block blockToBytesLE bytesToBlock bytesToBlock_blockToBytesLE blockToBytesLE_bytesToBlock)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)

/-! ## Prefix-Stability of `expandKey256` (`Nk = 8`, 60 Words) -/

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

private theorem expandKey256_eq_ksFold (key : List (BitVec 8)) :
    expandKey256 key = ksFold (ksInitWords key) 52 := rfl

private theorem length_ksInitWords (key : List (BitVec 8)) :
    (ksInitWords key).length = 8 := by
  simp [ksInitWords]

private theorem ksFold_succ (w0 : List Word) (n : Nat) :
    ksFold w0 (n + 1) = ksFold w0 n ++ [ksStepWord (ksFold w0 n) (8 + n)] := by
  unfold ksFold
  rw [Fin.foldl_succ_last]
  rfl

private theorem length_ksFold {w0 : List Word} (hw0 : w0.length = 8) (n : Nat) :
    (ksFold w0 n).length = 8 + n := by
  induction n with
  | zero => simpa [ksFold] using hw0
  | succ n ih =>
    rw [ksFold_succ, List.length_append, ih]
    simp; omega

private theorem getD_append_left {α : Type} (xs ys : List α) (d : α) {j : Nat}
    (hj : j < xs.length) : (xs ++ ys).getD j d = xs.getD j d := by
  have hj' : j < (xs ++ ys).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem_append_left hj]

private theorem getD_append_singleton_last {α : Type} (xs : List α) (y d : α) :
    (xs ++ [y]).getD xs.length d = y := by
  have hj : xs.length < (xs ++ [y]).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp

private theorem ksFold_getD_le {w0 : List Word} (hw0 : w0.length = 8) {n m j : Nat}
    (hnm : n ≤ m) (hj : j < 8 + n) :
    (ksFold w0 m).getD j [] = (ksFold w0 n).getD j [] := by
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ m ih =>
    by_cases h : n = m + 1
    · subst h; rfl
    · have hle : n ≤ m := by omega
      rw [ksFold_succ, getD_append_left _ _ _ (by rw [length_ksFold hw0]; omega)]
      exact ih hle

private theorem expandKey256_getD_init (key : List (BitVec 8)) {i : Nat} (hi : i < 8) :
    (expandKey256 key).getD i [] =
      [key.getD (4 * i) 0#8, key.getD (4 * i + 1) 0#8,
       key.getD (4 * i + 2) 0#8, key.getD (4 * i + 3) 0#8] := by
  rw [expandKey256_eq_ksFold, ksFold_getD_le (length_ksInitWords key) (Nat.zero_le 52) (by omega)]
  simp only [ksFold, Fin.foldl_zero, ksInitWords]
  have hlen : i < (List.ofFn fun k : Fin 8 =>
      [key.getD (4 * k.val) 0#8, key.getD (4 * k.val + 1) 0#8,
       key.getD (4 * k.val + 2) 0#8, key.getD (4 * k.val + 3) 0#8]).length := by
    simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp only [List.getElem_ofFn, Option.getD_some]

private theorem expandKey256_getD_step (key : List (BitVec 8)) {i : Nat}
    (hi8 : 8 ≤ i) (hi60 : i < 60) :
    (expandKey256 key).getD i [] = ksStepWord (expandKey256 key) i := by
  let k := i - 8
  have hik : i = 8 + k := by omega
  have hk52 : k + 1 ≤ 52 := by omega
  rw [expandKey256_eq_ksFold, hik,
    ksFold_getD_le (length_ksInitWords key) hk52 (by omega),
    ksFold_succ]
  have hlen : (ksFold (ksInitWords key) k).length = 8 + k :=
    length_ksFold (length_ksInitWords key) k
  rw [← hlen, getD_append_singleton_last, hlen]
  unfold ksStepWord
  have h1 : (ksFold (ksInitWords key) k).getD (8 + k - 1) [] =
      (ksFold (ksInitWords key) 52).getD (8 + k - 1) [] :=
    (ksFold_getD_le (length_ksInitWords key) (by omega) (by omega)).symm
  have h8 : (ksFold (ksInitWords key) k).getD (8 + k - 8) [] =
      (ksFold (ksInitWords key) 52).getD (8 + k - 8) [] :=
    (ksFold_getD_le (length_ksInitWords key) (by omega) (by omega)).symm
  rw [h1, h8]

private theorem length_word_expandKey256 (key : List (BitVec 8)) {i : Nat} (hi : i < 60) :
    ((expandKey256 key).getD i []).length = 4 := by
  by_cases hi8 : i < 8
  · rw [expandKey256_getD_init key hi8]; rfl
  · rw [expandKey256_getD_step key (by omega) hi]
    simp [ksStepWord, xorWord]

/-! ## Bit-Index Characterization of `xorColumnsFs`, `ksEvenStep`, and `ksOddStep` -/

private theorem getLsbD_ror64 (x : BitVec 64) (d : Nat) (hd : d < 64) (k : Nat) (hk : k < 64) :
    (ror64 x d).getLsbD k = x.getLsbD ((k + d) % 64) := by
  simp only [ror64, BitVec.getLsbD_rotateRight, hk, decide_true, Bool.true_and,
    Nat.mod_eq_of_lt hd]
  split
  · have h : d + k = (k + d) % 64 := by omega
    rw [h]
  · have h : k - (64 - d) = (k + d) % 64 := by omega
    rw [h]

private theorem xcol_m0_eq :
    ∀ (r c lane : Fin 4),
      (0x000f000f000f000f#64).getLsbD (16 * r.val + 4 * c.val + lane.val) =
        decide (c.val = 0) := by decide

private theorem xcol_m1_eq :
    ∀ (r c lane : Fin 4),
      (0xfff0fff0fff0fff0#64).getLsbD (16 * r.val + 4 * c.val + lane.val) =
        decide (1 ≤ c.val) := by decide

private theorem xcol_m2_eq :
    ∀ (r c lane : Fin 4),
      (0xff00ff00ff00ff00#64).getLsbD (16 * r.val + 4 * c.val + lane.val) =
        decide (2 ≤ c.val) := by decide

private theorem xcol_m3_eq :
    ∀ (r c lane : Fin 4),
      (0xf000f000f000f000#64).getLsbD (16 * r.val + 4 * c.val + lane.val) =
        decide (3 ≤ c.val) := by decide

private theorem getLsbD_xorColumnWord (prev cur : BitVec 64) (idxRor : Nat)
    (r c lane : Nat) (hr : r < 4) (hc : c < 4) (hl : lane < 4) :
    (xorColumnWord prev cur idxRor).getLsbD (16 * r + 4 * c + lane) =
      let t0 := (ror64 cur idxRor).getLsbD (16 * r + lane)
      let p0 := prev.getLsbD (16 * r + lane)
      let p1 := prev.getLsbD (16 * r + 4 + lane)
      let p2 := prev.getLsbD (16 * r + 8 + lane)
      let p3 := prev.getLsbD (16 * r + 12 + lane)
      match c with
      | 0 => p0 ^^ t0
      | 1 => p1 ^^ (p0 ^^ t0)
      | 2 => p2 ^^ p1 ^^ (p0 ^^ t0)
      | _ => p3 ^^ p2 ^^ p1 ^^ (p0 ^^ t0) := by
  let rk := prev ^^^ (0x000f000f000f000f#64 &&& ror64 cur idxRor)
  have hrk : ∀ (c' : Nat) (hc' : c' < 4),
      rk.getLsbD (16 * r + 4 * c' + lane) =
        if c' = 0 then
          prev.getLsbD (16 * r + lane) ^^ (ror64 cur idxRor).getLsbD (16 * r + lane)
        else
          prev.getLsbD (16 * r + 4 * c' + lane) := by
    intro c' hc'
    simp only [rk, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    have hm0 := xcol_m0_eq ⟨r, hr⟩ ⟨c', hc'⟩ ⟨lane, hl⟩
    dsimp only at hm0
    rw [hm0]
    match c', hc' with
    | 0, _ => simp
    | 1, _ | 2, _ | 3, _ => simp
    | _ + 4, hc' => omega
  change (rk ^^^ (0xfff0fff0fff0fff0#64 &&& (rk <<< 4))
            ^^^ (0xff00ff00ff00ff00#64 &&& (rk <<< 8))
            ^^^ (0xf000f000f000f000#64 &&& (rk <<< 12))).getLsbD
          (16 * r + 4 * c + lane) = _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  have hm1 := xcol_m1_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  have hm2 := xcol_m2_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  have hm3 := xcol_m3_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  dsimp only at hm1 hm2 hm3
  rw [hm1, hm2, hm3]
  have hk64 : 16 * r + 4 * c + lane < 64 := by omega
  simp only [hk64, decide_true, Bool.true_and]
  match c, hc with
  | 0, _ =>
    have hrk0 := hrk 0 (by omega)
    simpa using hrk0
  | 1, _ =>
    have hrk0 := hrk 0 (by omega)
    have hrk1 := hrk 1 (by omega)
    have hlt4 : ¬ (16 * r + 4 * 1 + lane < 4) := by omega
    have hsub4 : 16 * r + 4 * 1 + lane - 4 = 16 * r + 4 * 0 + lane := by omega
    simp only [hlt4, decide_false, Bool.not_false, Bool.true_and, hsub4]
    rw [hrk1, hrk0]
    simp
  | 2, _ =>
    have hrk0 := hrk 0 (by omega)
    have hrk1 := hrk 1 (by omega)
    have hrk2 := hrk 2 (by omega)
    have hlt4 : ¬ (16 * r + 4 * 2 + lane < 4) := by omega
    have hlt8 : ¬ (16 * r + 4 * 2 + lane < 8) := by omega
    have hsub4 : 16 * r + 4 * 2 + lane - 4 = 16 * r + 4 * 1 + lane := by omega
    have hsub8 : 16 * r + 4 * 2 + lane - 8 = 16 * r + 4 * 0 + lane := by omega
    simp only [hlt4, hlt8, decide_false, Bool.not_false, Bool.true_and, hsub4, hsub8]
    rw [hrk2, hrk1, hrk0]
    simp
  | 3, _ =>
    have hrk0 := hrk 0 (by omega)
    have hrk1 := hrk 1 (by omega)
    have hrk2 := hrk 2 (by omega)
    have hrk3 := hrk 3 (by omega)
    have hlt4 : ¬ (16 * r + 4 * 3 + lane < 4) := by omega
    have hlt8 : ¬ (16 * r + 4 * 3 + lane < 8) := by omega
    have hlt12 : ¬ (16 * r + 4 * 3 + lane < 12) := by omega
    have hsub4 : 16 * r + 4 * 3 + lane - 4 = 16 * r + 4 * 2 + lane := by omega
    have hsub8 : 16 * r + 4 * 3 + lane - 8 = 16 * r + 4 * 1 + lane := by omega
    have hsub12 : 16 * r + 4 * 3 + lane - 12 = 16 * r + 4 * 0 + lane := by omega
    simp only [hlt4, hlt8, hlt12, decide_false, Bool.not_false, Bool.true_and,
      hsub4, hsub8, hsub12]
    rw [hrk3, hrk2, hrk1, hrk0]
    simp
  | _ + 4, hc => omega

private theorem getD_roundKey (w : List Word) (m r c : Nat) (hr : r < 4) (hc : c < 4) :
    (roundKey w m).getD (r + 4 * c) 0#8 = (w.getD (4 * m + c) []).getD r 0#8 := by
  have hi : r + 4 * c < (roundKey w m).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [roundKey, List.getElem_ofFn, Option.getD_some]
  have hdiv : (r + 4 * c) / 4 = c := by omega
  have hmod : (r + 4 * c) % 4 = r := by omega
  rw [hdiv, hmod]

private theorem getD_xorWord (u v : Word) (r : Nat) (hr : r < 4) :
    (xorWord u v).getD r 0#8 = u.getD r 0#8 ^^^ v.getD r 0#8 := by
  have hi : r < (xorWord u v).length := by simp [xorWord]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [xorWord, List.getElem_ofFn, Option.getD_some]

private theorem getD_rotWord (u : Word) (r : Nat) (hr : r < 4) :
    (rotWord u).getD r 0#8 = u.getD ((r + 1) % 4) 0#8 := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hr => omega

private theorem getD_subWord {u : Word} (hu : u.length = 4) (r : Nat) (hr : r < 4) :
    (subWord u).getD r 0#8 = sbox (u.getD r 0#8) := by
  have hi1 : r < u.length := by omega
  have hi2 : r < (subWord u).length := by simp [subWord, hu]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
  simp [subWord]

private theorem getLane_replicate (s : State) (lane : Nat) (hl : lane < 4) :
    (Blocks4.replicate s).getLane lane = s := by
  match lane, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hl => omega

private theorem getSlice_zipWith (f : BitVec 64 → BitVec 64 → BitVec 64)
    (a b : FsState) (p : Nat) (hp : p < 8) :
    (a.zipWith f b).getSlice p = f (a.getSlice p) (b.getSlice p) := by
  match p, hp with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | _ + 8, hp => omega

private theorem ite_true {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · contradiction

private theorem ite_false {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by
  split
  · contradiction
  · rfl

private theorem xorColumnsFs_replicate (key : List (BitVec 8)) (cur : FsState)
    (m idxRor : Nat) (temp0 : Word)
    (hm2 : 2 ≤ m) (hm14 : m ≤ 14)
    (hcur : ∀ p r lane, p < 8 → r < 4 → lane < 4 →
      (ror64 (cur.getSlice p) idxRor).getLsbD (16 * r + lane) =
        (temp0.getD r 0#8).getLsbD p)
    (hw0 : (expandKey256 key).getD (4 * m) [] =
      xorWord ((expandKey256 key).getD (4 * (m - 2)) []) temp0) :
    xorColumnsFs (bitslice (Blocks4.replicate (roundKey (expandKey256 key) (m - 2)))) cur idxRor =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) m)) := by
  let w := expandKey256 key
  have hw0' : w.getD (4 * m) [] = xorWord (w.getD (4 * (m - 2)) []) temp0 := hw0
  have hw1 : w.getD (4 * m + 1) [] = xorWord (w.getD (4 * (m - 2) + 1) []) (w.getD (4 * m) []) := by
    change (expandKey256 key).getD (4 * m + 1) [] = _
    rw [expandKey256_getD_step key (by omega) (by omega)]
    unfold ksStepWord
    dsimp only
    have hm8_0 : (4 * m + 1) % 8 ≠ 0 := by omega
    have hm8_4 : (4 * m + 1) % 8 ≠ 4 := by omega
    have hsub1 : 4 * m + 1 - 1 = 4 * m := by omega
    have hsub8 : 4 * m + 1 - 8 = 4 * (m - 2) + 1 := by omega
    rw [ite_false hm8_0, ite_false hm8_4, hsub1, hsub8]
  have hw2 : w.getD (4 * m + 2) [] =
      xorWord (w.getD (4 * (m - 2) + 2) []) (w.getD (4 * m + 1) []) := by
    change (expandKey256 key).getD (4 * m + 2) [] = _
    rw [expandKey256_getD_step key (by omega) (by omega)]
    unfold ksStepWord
    dsimp only
    have hm8_0 : (4 * m + 2) % 8 ≠ 0 := by omega
    have hm8_4 : (4 * m + 2) % 8 ≠ 4 := by omega
    have hsub1 : 4 * m + 2 - 1 = 4 * m + 1 := by omega
    have hsub8 : 4 * m + 2 - 8 = 4 * (m - 2) + 2 := by omega
    rw [ite_false hm8_0, ite_false hm8_4, hsub1, hsub8]
  have hw3 : w.getD (4 * m + 3) [] =
      xorWord (w.getD (4 * (m - 2) + 3) []) (w.getD (4 * m + 2) []) := by
    change (expandKey256 key).getD (4 * m + 3) [] = _
    rw [expandKey256_getD_step key (by omega) (by omega)]
    unfold ksStepWord
    dsimp only
    have hm8_0 : (4 * m + 3) % 8 ≠ 0 := by omega
    have hm8_4 : (4 * m + 3) % 8 ≠ 4 := by omega
    have hsub1 : 4 * m + 3 - 1 = 4 * m + 2 := by omega
    have hsub8 : 4 * m + 3 - 8 = 4 * (m - 2) + 3 := by omega
    rw [ite_false hm8_0, ite_false hm8_4, hsub1, hsub8]
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  rw [xorColumnsFs, getSlice_zipWith _ _ _ p hp,
    getLsbD_xorColumnWord _ _ idxRor r c lane hr hc hl,
    getLane_replicate _ lane hl, getD_roundKey w m r c hr hc]
  have hp_col : ∀ (c' : Nat) (hc' : c' < 4),
      ((bitslice (Blocks4.replicate (roundKey w (m - 2)))).getSlice p).getLsbD
        (16 * r + 4 * c' + lane) =
        ((w.getD (4 * (m - 2) + c') []).getD r 0#8).getLsbD p := by
    intro c' hc'
    rw [getLsbD_bitslice _ p r c' lane hp hr hc' hl, getLane_replicate _ lane hl,
      getD_roundKey w (m - 2) r c' hr hc']
  have hp0 : ((bitslice (Blocks4.replicate (roundKey w (m - 2)))).getSlice p).getLsbD
      (16 * r + lane) = ((w.getD (4 * (m - 2)) []).getD r 0#8).getLsbD p := by
    simpa using hp_col 0 (by omega)
  have hp1 : ((bitslice (Blocks4.replicate (roundKey w (m - 2)))).getSlice p).getLsbD
      (16 * r + 4 + lane) = ((w.getD (4 * (m - 2) + 1) []).getD r 0#8).getLsbD p := by
    simpa using hp_col 1 (by omega)
  have hp2 : ((bitslice (Blocks4.replicate (roundKey w (m - 2)))).getSlice p).getLsbD
      (16 * r + 8 + lane) = ((w.getD (4 * (m - 2) + 2) []).getD r 0#8).getLsbD p := by
    simpa using hp_col 2 (by omega)
  have hp3 : ((bitslice (Blocks4.replicate (roundKey w (m - 2)))).getSlice p).getLsbD
      (16 * r + 12 + lane) = ((w.getD (4 * (m - 2) + 3) []).getD r 0#8).getLsbD p := by
    simpa using hp_col 3 (by omega)
  dsimp only
  rw [hcur p r lane hp hr hl, hp0, hp1, hp2, hp3]
  match c, hc with
  | 0, _ =>
    rw [Nat.add_zero (4 * m), hw0', getD_xorWord _ _ r hr, BitVec.getLsbD_xor]
    rfl
  | 1, _ =>
    rw [hw1, getD_xorWord _ _ r hr, hw0', getD_xorWord _ _ r hr,
      BitVec.getLsbD_xor, BitVec.getLsbD_xor]
    rfl
  | 2, _ =>
    rw [hw2, getD_xorWord _ _ r hr, hw1, getD_xorWord _ _ r hr, hw0', getD_xorWord _ _ r hr,
      BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_xor, Bool.xor_assoc]
    rfl
  | 3, _ =>
    rw [hw3, getD_xorWord _ _ r hr, hw2, getD_xorWord _ _ r hr, hw1, getD_xorWord _ _ r hr,
      hw0', getD_xorWord _ _ r hr]
    simp only [BitVec.getLsbD_xor, Bool.xor_assoc]
  | _ + 4, hc => omega

private theorem rconMask_rot28 :
    ∀ (r lane : Fin 4),
      (0x00000000f0000000#64).getLsbD ((16 * r.val + lane.val + 28) % 64) =
        decide (r.val = 0) := by decide

private theorem rcon_bit_eq :
    ∀ (b : Fin 7) (p : Fin 8),
      (rcon.getD b.val 0#8).getLsbD p.val = decide (p.val = b.val) := by decide

private theorem rconWord_bit (b r p : Nat) (hb : b < 7) (hr : r < 4) (hp : p < 8) :
    (([rcon.getD b 0#8, 0#8, 0#8, 0#8] : Word).getD r 0#8).getLsbD p =
      (decide (r = 0) && decide (p = b)) := by
  have hb_rcon := rcon_bit_eq ⟨b, hb⟩ ⟨p, hp⟩
  dsimp only at hb_rcon
  match r, hr with
  | 0, _ =>
    change (rcon.getD b 0#8).getLsbD p = _
    rw [hb_rcon]
    simp
  | 1, _ | 2, _ | 3, _ =>
    change (0#8).getLsbD p = _
    simp
  | _ + 4, hr => omega

private theorem getSlice_addRoundConstantBit (st : FsState) (b p : Nat) (hp : p < 8) :
    (addRoundConstantBit st b).getSlice p =
      if p = b then st.getSlice p ^^^ 0x00000000f0000000#64 else st.getSlice p := by
  match b with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    match p, hp with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | _ + 8, hp => omega
  | n + 8 =>
    have hne : p ≠ n + 8 := by omega
    simp [addRoundConstantBit, hne]

private theorem getD_subBytes_state {s : State} (hs : s.length = 16) (j : Nat) (hj : j < 16) :
    (subBytes s).getD j 0#8 = sbox (s.getD j 0#8) := by
  have hj1 : j < s.length := by omega
  have hj2 : j < (subBytes s).length := by simp [hs]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]
  simp [subBytes]

private theorem ksEvenStep_replicate (key : List (BitVec 8)) (b : Nat) (hb : b < 7) :
    ksEvenStep (bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b))))
      (bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b + 1)))) b =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b + 2))) := by
  let w := expandKey256 key
  let prevLast := w.getD (8 * b + 7) []
  let rconWord : Word := [rcon.getD b 0#8, 0#8, 0#8, 0#8]
  let temp0 : Word := xorWord (subWord (rotWord prevLast)) rconWord
  unfold ksEvenStep
  dsimp only
  rw [subBytesNots_subBytesFs_bitslice (Blocks4.wf_replicate (length_roundKey w (2 * b + 1)))]
  have hrep_map : (Blocks4.replicate (roundKey w (2 * b + 1))).map subBytes =
      Blocks4.replicate (subBytes (roundKey w (2 * b + 1))) := rfl
  rw [hrep_map]
  apply xorColumnsFs_replicate key _ (2 * b + 2) (rorDistance 1 3) temp0 (by omega) (by omega)
  · intro p r lane hp hr hl
    have hdist : rorDistance 1 3 = 28 := rfl
    rw [hdist, getLsbD_ror64 _ 28 (by omega) (16 * r + lane) (by omega),
      getSlice_addRoundConstantBit _ b p hp]
    have hidx : (16 * r + lane + 28) % 64 = 16 * ((r + 1) % 4) + 4 * 3 + lane := by omega
    have hsub_bit :
        ((bitslice (Blocks4.replicate (subBytes (roundKey w (2 * b + 1))))).getSlice p).getLsbD
          ((16 * r + lane + 28) % 64) =
          (sbox (prevLast.getD ((r + 1) % 4) 0#8)).getLsbD p := by
      rw [hidx, getLsbD_bitslice _ p ((r + 1) % 4) 3 lane hp (by omega) (by omega) hl,
        getLane_replicate _ lane hl,
        getD_subBytes_state (length_roundKey w (2 * b + 1)) _ (by omega),
        getD_roundKey w (2 * b + 1) ((r + 1) % 4) 3 (by omega) (by omega)]
      have hcol : 4 * (2 * b + 1) + 3 = 8 * b + 7 := by omega
      rw [hcol]
    have hrot_byte : (subWord (rotWord prevLast)).getD r 0#8 =
        sbox (prevLast.getD ((r + 1) % 4) 0#8) := by
      rw [getD_subWord rfl r hr, getD_rotWord prevLast r hr]
    rw [show temp0.getD r 0#8 =
        (subWord (rotWord prevLast)).getD r 0#8 ^^^ rconWord.getD r 0#8 from
        getD_xorWord _ _ r hr,
      hrot_byte, BitVec.getLsbD_xor]
    have hrw_bit : (rconWord.getD r 0#8).getLsbD p = (decide (r = 0) && decide (p = b)) :=
      rconWord_bit b r p hb hr hp
    have hm_rcon := rconMask_rot28 ⟨r, hr⟩ ⟨lane, hl⟩
    dsimp only at hm_rcon
    generalize (sbox (prevLast.getD ((r + 1) % 4) 0#8)).getLsbD p = sb at hsub_bit ⊢
    by_cases hpb : p = b
    · rw [ite_true hpb, BitVec.getLsbD_xor, hsub_bit, hm_rcon, hrw_bit]
      simp [hpb]
    · rw [ite_false hpb, hsub_bit, hrw_bit]
      simp [hpb]
  · rw [expandKey256_getD_step key (by omega) (by omega)]
    unfold ksStepWord
    dsimp only
    have hm8 : (4 * (2 * b + 2)) % 8 = 0 := by omega
    have hdiv : (4 * (2 * b + 2)) / 8 - 1 = b := by omega
    have hsub1 : 4 * (2 * b + 2) - 1 = 8 * b + 7 := by omega
    have hsub8 : 4 * (2 * b + 2) - 8 = 4 * (2 * b + 2 - 2) := by omega
    rw [ite_true hm8, hdiv, hsub1, hsub8]

private theorem ksOddStep_replicate (key : List (BitVec 8)) (b : Nat) (hb : b < 6) :
    ksOddStep (bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b + 1))))
      (bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b + 2)))) =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) (2 * b + 3))) := by
  let w := expandKey256 key
  let prevLast := w.getD (8 * b + 11) []
  let temp0 : Word := subWord prevLast
  unfold ksOddStep
  dsimp only
  rw [subBytesNots_subBytesFs_bitslice (Blocks4.wf_replicate (length_roundKey w (2 * b + 2)))]
  have hrep_map : (Blocks4.replicate (roundKey w (2 * b + 2))).map subBytes =
      Blocks4.replicate (subBytes (roundKey w (2 * b + 2))) := rfl
  rw [hrep_map]
  apply xorColumnsFs_replicate key _ (2 * b + 3) (rorDistance 0 3) temp0 (by omega) (by omega)
  · intro p r lane hp hr hl
    have hdist : rorDistance 0 3 = 12 := rfl
    have hidx : (16 * r + lane + 12) % 64 = 16 * r + 4 * 3 + lane := by omega
    rw [hdist, getLsbD_ror64 _ 12 (by omega) (16 * r + lane) (by omega), hidx,
      getLsbD_bitslice _ p r 3 lane hp hr (by omega) hl,
      getLane_replicate _ lane hl,
      getD_subBytes_state (length_roundKey w (2 * b + 2)) _ (by omega),
      getD_roundKey w (2 * b + 2) r 3 hr (by omega)]
    have hcol : 4 * (2 * b + 2) + 3 = 8 * b + 11 := by omega
    have hlen4 : prevLast.length = 4 := length_word_expandKey256 key (by omega)
    rw [hcol, show temp0.getD r 0#8 = sbox (prevLast.getD r 0#8) from getD_subWord hlen4 r hr]
  · rw [expandKey256_getD_step key (by omega) (by omega)]
    unfold ksStepWord
    dsimp only
    have hm8_0 : (4 * (2 * b + 3)) % 8 ≠ 0 := by omega
    have hm8_4 : (4 * (2 * b + 3)) % 8 = 4 := by omega
    have hsub1 : 4 * (2 * b + 3) - 1 = 8 * b + 11 := by omega
    have hsub8 : 4 * (2 * b + 3) - 8 = 4 * (2 * b + 3 - 2) := by omega
    rw [ite_false hm8_0, ite_true hm8_4, hsub1, hsub8]

private theorem roundKey0_eq_take16 {key : List (BitVec 8)} (hkey : key.length = 32) :
    roundKey (expandKey256 key) 0 = key.take 16 := by
  apply state_eq_of_getD (length_roundKey _ 0) (by simp [hkey])
  intro j hj
  have hj_eq : (j % 4) + 4 * (j / 4) = j := by omega
  rw [← hj_eq, getD_roundKey _ 0 (j % 4) (j / 4) (by omega) (by omega), Nat.zero_add,
    expandKey256_getD_init key (by omega), hj_eq]
  have htake : (key.take 16).getD j 0#8 = key.getD j 0#8 := by
    have hj1 : j < (key.take 16).length := by simp [hkey]; omega
    have hj2 : j < key.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, List.getElem_take]
  rw [htake]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hj => omega

private theorem roundKey1_eq_drop16 {key : List (BitVec 8)} (hkey : key.length = 32) :
    roundKey (expandKey256 key) 1 = key.drop 16 := by
  apply state_eq_of_getD (length_roundKey _ 1) (by simp [hkey])
  intro j hj
  have hj_eq : (j % 4) + 4 * (j / 4) = j := by omega
  rw [← hj_eq, getD_roundKey _ 1 (j % 4) (j / 4) (by omega) (by omega),
    expandKey256_getD_init key (by omega), hj_eq]
  have hdrop : (key.drop 16).getD j 0#8 = key.getD (16 + j) 0#8 := by
    have hj1 : j < (key.drop 16).length := by simp [hkey]; omega
    have hj2 : 16 + j < key.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, List.getElem_drop]
  rw [hdrop]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hj => omega

/-- Round-key 0 of `aes256KeyScheduleFs` is the un-negated, un-shifted `roundKey w 0`. -/
theorem aes256KeyScheduleFs_rk0 {key : List (BitVec 8)} (hkey : key.length = 32) :
    (aes256KeyScheduleFs key).rk0 =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) 0)) := by
  simp only [aes256KeyScheduleFs, roundKey0_eq_take16 hkey]

/-- Round-keys `1..13` of `aes256KeyScheduleFs` carry `subBytesNots` and `invShiftRowsPow (r % 4)`. -/
theorem aes256KeyScheduleFs_getRound {key : List (BitVec 8)} (hkey : key.length = 32)
    {r : Nat} (hr1 : 1 ≤ r) (hr13 : r ≤ 13) :
    (aes256KeyScheduleFs key).getRound r =
      subBytesNots (bitslice (Blocks4.replicate
        (invShiftRowsPow (r % 4) (roundKey (expandKey256 key) r)))) := by
  have hrk0 : bitslice (Blocks4.replicate (key.take 16)) =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) 0)) := by
    rw [roundKey0_eq_take16 hkey]
  have hrk1 : bitslice (Blocks4.replicate (key.drop 16)) =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) 1)) := by
    rw [roundKey1_eq_drop16 hkey]
  have hrk2 := ksEvenStep_replicate key 0 (by omega)
  have hrk3 := ksOddStep_replicate key 0 (by omega)
  have hrk4 := ksEvenStep_replicate key 1 (by omega)
  have hrk5 := ksOddStep_replicate key 1 (by omega)
  have hrk6 := ksEvenStep_replicate key 2 (by omega)
  have hrk7 := ksOddStep_replicate key 2 (by omega)
  have hrk8 := ksEvenStep_replicate key 3 (by omega)
  have hrk9 := ksOddStep_replicate key 3 (by omega)
  have hrk10 := ksEvenStep_replicate key 4 (by omega)
  have hrk11 := ksOddStep_replicate key 4 (by omega)
  have hrk12 := ksEvenStep_replicate key 5 (by omega)
  have hrk13 := ksOddStep_replicate key 5 (by omega)
  unfold aes256KeyScheduleFs
  dsimp only
  rw [hrk0, hrk1, hrk2, hrk3, hrk4, hrk5, hrk6, hrk7, hrk8, hrk9, hrk10, hrk11, hrk12, hrk13]
  have hsr0 : ∀ m, invShiftRowsPow 0 (roundKey (expandKey256 key) m) =
      roundKey (expandKey256 key) m := fun m =>
    shiftRowsPow_zero (length_roundKey (expandKey256 key) m)
  match r, hr1, hr13 with
  | 1, _, _ =>
    change subBytesNots (invShiftRows1 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 1)))) = _
    rw [invShiftRows1_bitslice]; rfl
  | 2, _, _ =>
    change subBytesNots (invShiftRows2 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 2)))) = _
    rw [invShiftRows2_bitslice]; rfl
  | 3, _, _ =>
    change subBytesNots (invShiftRows3 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 3)))) = _
    rw [invShiftRows3_bitslice]; rfl
  | 4, _, _ =>
    change subBytesNots (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 4))) =
      subBytesNots (bitslice (Blocks4.replicate (invShiftRowsPow 0 (roundKey (expandKey256 key) 4))))
    rw [hsr0]
  | 5, _, _ =>
    change subBytesNots (invShiftRows1 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 5)))) = _
    rw [invShiftRows1_bitslice]; rfl
  | 6, _, _ =>
    change subBytesNots (invShiftRows2 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 6)))) = _
    rw [invShiftRows2_bitslice]; rfl
  | 7, _, _ =>
    change subBytesNots (invShiftRows3 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 7)))) = _
    rw [invShiftRows3_bitslice]; rfl
  | 8, _, _ =>
    change subBytesNots (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 8))) =
      subBytesNots (bitslice (Blocks4.replicate (invShiftRowsPow 0 (roundKey (expandKey256 key) 8))))
    rw [hsr0]
  | 9, _, _ =>
    change subBytesNots (invShiftRows1 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 9)))) = _
    rw [invShiftRows1_bitslice]; rfl
  | 10, _, _ =>
    change subBytesNots (invShiftRows2 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 10)))) = _
    rw [invShiftRows2_bitslice]; rfl
  | 11, _, _ =>
    change subBytesNots (invShiftRows3 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 11)))) = _
    rw [invShiftRows3_bitslice]; rfl
  | 12, _, _ =>
    change subBytesNots (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 12))) =
      subBytesNots (bitslice (Blocks4.replicate (invShiftRowsPow 0 (roundKey (expandKey256 key) 12))))
    rw [hsr0]
  | 13, _, _ =>
    change subBytesNots (invShiftRows1 (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 13)))) = _
    rw [invShiftRows1_bitslice]; rfl
  | 0, hr1, _ => omega
  | _ + 14, _, hr13 => omega

/-- Round-key 14 of `aes256KeyScheduleFs` carries `subBytesNots` at un-shifted parity 0. -/
theorem aes256KeyScheduleFs_rk14 {key : List (BitVec 8)} (hkey : key.length = 32) :
    (aes256KeyScheduleFs key).rk14 =
      subBytesNots (bitslice (Blocks4.replicate (roundKey (expandKey256 key) 14))) := by
  have hrk0 : bitslice (Blocks4.replicate (key.take 16)) =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) 0)) := by
    rw [roundKey0_eq_take16 hkey]
  have hrk1 : bitslice (Blocks4.replicate (key.drop 16)) =
      bitslice (Blocks4.replicate (roundKey (expandKey256 key) 1)) := by
    rw [roundKey1_eq_drop16 hkey]
  have hrk2 := ksEvenStep_replicate key 0 (by omega)
  have hrk3 := ksOddStep_replicate key 0 (by omega)
  have hrk4 := ksEvenStep_replicate key 1 (by omega)
  have hrk5 := ksOddStep_replicate key 1 (by omega)
  have hrk6 := ksEvenStep_replicate key 2 (by omega)
  have hrk7 := ksOddStep_replicate key 2 (by omega)
  have hrk8 := ksEvenStep_replicate key 3 (by omega)
  have hrk9 := ksOddStep_replicate key 3 (by omega)
  have hrk10 := ksEvenStep_replicate key 4 (by omega)
  have hrk11 := ksOddStep_replicate key 4 (by omega)
  have hrk12 := ksEvenStep_replicate key 5 (by omega)
  have hrk13 := ksOddStep_replicate key 5 (by omega)
  have hrk14 := ksEvenStep_replicate key 6 (by omega)
  unfold aes256KeyScheduleFs
  dsimp only
  rw [hrk0, hrk1, hrk2, hrk3, hrk4, hrk5, hrk6, hrk7, hrk8, hrk9, hrk10, hrk11, hrk12, hrk13,
    hrk14]

/-! ## Per-Round-Parity Equivalence for `aes256EncryptFs` and `aes256DecryptFs` -/

private theorem blocks4_map_ext (bs : Blocks4) {f g : State → State}
    (h : ∀ s, f s = g s) : bs.map f = bs.map g := by
  dsimp only [Blocks4.map]
  rw [h, h, h, h]

private theorem addRoundKeyFs_subBytesNots_right (a b : FsState) :
    addRoundKeyFs a (subBytesNots b) = subBytesNots (addRoundKeyFs a b) := by
  rw [subBytesNots_eq_addRoundKeyFs, ← addRoundKeyFs_assoc, ← subBytesNots_eq_addRoundKeyFs]

private theorem addRoundKeyFs_subBytesNots_swap (a b : FsState) :
    addRoundKeyFs a (subBytesNots b) = addRoundKeyFs (subBytesNots a) b := by
  rw [subBytesNots_eq_addRoundKeyFs, addRoundKeyFs_comm b _, ← addRoundKeyFs_assoc,
    ← subBytesNots_eq_addRoundKeyFs]

private theorem zipWith_replicate_right (f : State → State → State) (bs : Blocks4) (rk : State) :
    bs.zipWith f (Blocks4.replicate rk) = bs.map (fun b => f b rk) := rfl

private theorem blocks4_map_map (f g : State → State) (bs : Blocks4) :
    (bs.map g).map f = bs.map (fun b => f (g b)) := rfl

private def encLoop (w : List Word) (n : Nat) (s0 : State) : State :=
  Fin.foldl n (fun s (r : Fin n) =>
    addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (r.val + 1))) s0

private theorem encLoop_succ (w : List Word) (n : Nat) (s0 : State) :
    encLoop w (n + 1) s0 =
      addRoundKey (mixColumns (shiftRows (subBytes (encLoop w n s0)))) (roundKey w (n + 1)) := by
  unfold encLoop
  rw [Fin.foldl_succ_last]
  rfl

private theorem length_encLoop (w : List Word) (n : Nat) {s0 : State} (hs0 : s0.length = 16) :
    (encLoop w n s0).length = 16 := by
  cases n with
  | zero => simpa [encLoop] using hs0
  | succ n => rw [encLoop_succ]; exact length_addRoundKey _ _

private theorem invShiftRowsPow_addRoundKey (q : Nat) (a b : State) :
    invShiftRowsPow q (addRoundKey a b) =
      addRoundKey (invShiftRowsPow q a) (invShiftRowsPow q b) :=
  shiftRowsPow_addRoundKey _ a b

private theorem enc_parity_step (n : Nat) {s : State} (hs : s.length = 16) :
    subBytes (invShiftRowsPow (n % 4) s) =
      invShiftRowsPow ((n + 1) % 4) (shiftRows (subBytes s)) := by
  have hmod : (((4 - ((n + 1) % 4) % 4) % 4) + 1) % 4 = (4 - (n % 4) % 4) % 4 := by omega
  simp only [← shiftRowsPow_one (subBytes s), invShiftRowsPow]
  rw [shiftRowsPow_shiftRowsPow, hmod, ← shiftRowsPow_subBytes _ hs]

/-- 4-lane equivalence of `aes256EncryptFs` with FIPS 197 `aes256Cipher` (zero round unrolling). -/
theorem aes256EncryptFs_eq {key : List (BitVec 8)} (hkey : key.length = 32)
    {blocks : Blocks4} (hblocks : Blocks4.Wf blocks) :
    aes256EncryptFs (aes256KeyScheduleFs key) blocks = blocks.map (aes256Cipher key) := by
  let w := expandKey256 key
  let rkeys := aes256KeyScheduleFs key
  let st0 := addRoundKeyFs (bitslice blocks) rkeys.rk0
  have hloop : ∀ (n : Nat), n ≤ 13 →
      (List.range n).foldl (fun st i => encRoundFs rkeys (i + 1) st) st0 =
        bitslice (blocks.map (fun b =>
          invShiftRowsPow (n % 4) (encLoop w n (addRoundKey b (roundKey w 0))))) := by
    intro n hn
    induction n with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, st0, rkeys, aes256KeyScheduleFs_rk0 hkey,
        addRoundKeyFs_bitslice, zipWith_replicate_right]
      congr 1
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      dsimp only [encRoundFs]
      rw [show rkeys.getRound (n + 1) =
          subBytesNots (bitslice (Blocks4.replicate
            (invShiftRowsPow ((n + 1) % 4) (roundKey w (n + 1))))) from
          aes256KeyScheduleFs_getRound hkey (by omega) hn,
        addRoundKeyFs_subBytesNots_swap, ← mixColumnsQ_subBytesNots,
        subBytesNots_subBytesFs_bitslice
          (Blocks4.wf_map (fun _ _ => length_invShiftRowsPow _ _) hblocks),
        blocks4_map_map]
      have hstep : blocks.map (fun b =>
          subBytes (invShiftRowsPow (n % 4) (encLoop w n (addRoundKey b (roundKey w 0))))) =
          (blocks.map (fun b =>
            shiftRows (subBytes (encLoop w n (addRoundKey b (roundKey w 0)))))).map
              (invShiftRowsPow ((n + 1) % 4)) := by
        rw [blocks4_map_map]
        apply blocks4_map_ext
        intro b
        exact enc_parity_step n (length_encLoop w n (length_addRoundKey _ _))
      rw [hstep, mixColumnsQ_bitslice ((n + 1) % 4) (by omega),
        addRoundKeyFs_bitslice, zipWith_replicate_right, blocks4_map_map, blocks4_map_map]
      congr 1
      apply blocks4_map_ext
      intro b
      rw [← invShiftRowsPow_addRoundKey, ← encLoop_succ]
  unfold aes256EncryptFs
  dsimp only
  change invBitslice (addRoundKeyFs (subBytesFs (shiftRows2
      ((List.range 13).foldl (fun st i => encRoundFs rkeys (i + 1) st) st0))) rkeys.rk14) = _
  rw [hloop 13 (by omega), shiftRows2_bitslice, blocks4_map_map,
    show rkeys.rk14 = subBytesNots (bitslice (Blocks4.replicate (roundKey w 14))) from
      aes256KeyScheduleFs_rk14 hkey,
    addRoundKeyFs_subBytesNots_swap,
    subBytesNots_subBytesFs_bitslice
      (Blocks4.wf_map (fun _ _ => length_shiftRowsPow _ _) hblocks),
    blocks4_map_map, addRoundKeyFs_bitslice, zipWith_replicate_right, blocks4_map_map]
  have hfinal_sr : ∀ s : State, s.length = 16 →
      subBytes (shiftRowsPow 2 (invShiftRowsPow (13 % 4) s)) = shiftRows (subBytes s) := by
    intro s hs
    have h13 : invShiftRowsPow (13 % 4) s = shiftRowsPow 3 s := rfl
    rw [h13, shiftRowsPow_shiftRowsPow, show (2 + 3) % 4 = 1 from rfl,
      ← shiftRowsPow_subBytes 1 hs, shiftRowsPow_one]
  have hmap_eq : blocks.map (fun b =>
      addRoundKey (subBytes (shiftRowsPow 2 (invShiftRowsPow (13 % 4)
        (encLoop w 13 (addRoundKey b (roundKey w 0)))))) (roundKey w 14)) =
      blocks.map (aes256Cipher key) := by
    apply blocks4_map_ext
    intro b
    rw [hfinal_sr _ (length_encLoop w 13 (length_addRoundKey _ _))]
    rfl
  rw [hmap_eq, invBitslice_bitslice (Blocks4.wf_map (fun _ _ => length_aes256Cipher key _) hblocks)]

private def decLoop (w : List Word) (n : Nat) (s0 : State) : State :=
  Fin.foldl n (fun s (j : Fin n) =>
    invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) (roundKey w (13 - j.val)))) s0

private theorem decLoop_succ (w : List Word) (n : Nat) (s0 : State) :
    decLoop w (n + 1) s0 =
      invMixColumns (addRoundKey (invSubBytes (invShiftRows (decLoop w n s0)))
        (roundKey w (13 - n))) := by
  unfold decLoop
  rw [Fin.foldl_succ_last]
  rfl

private theorem length_decLoop (w : List Word) (n : Nat) {s0 : State} (hs0 : s0.length = 16) :
    (decLoop w n s0).length = 16 := by
  cases n with
  | zero => simpa [decLoop] using hs0
  | succ n => rw [decLoop_succ]; exact length_invMixColumns _

private def decState (w : List Word) (n : Nat) (b : State) : State :=
  invSubBytes (invShiftRows (decLoop w n (addRoundKey b (roundKey w 14))))

private theorem decState_zero (w : List Word) (b : State) :
    decState w 0 b = invSubBytes (invShiftRows (addRoundKey b (roundKey w 14))) := rfl

private theorem decState_succ (w : List Word) (n : Nat) (b : State) :
    decState w (n + 1) b =
      invSubBytes (invShiftRows (invMixColumns (addRoundKey (decState w n b)
        (roundKey w (13 - n))))) := by
  unfold decState
  rw [decLoop_succ]

private theorem length_decState (w : List Word) (n : Nat) (b : State) :
    (decState w n b).length = 16 := by
  simp [decState]

private theorem dec_parity_step {r : Nat} (hr : 1 ≤ r) {s : State} (hs : s.length = 16) :
    invSubBytes (invShiftRowsPow (r % 4) s) =
      invShiftRowsPow ((r - 1) % 4) (invSubBytes (invShiftRows s)) := by
  have hmod : (((4 - ((r - 1) % 4) % 4) % 4) + 3) % 4 = (4 - (r % 4) % 4) % 4 := by omega
  simp only [← invShiftRowsPow_one s, invShiftRowsPow]
  rw [← shiftRowsPow_invSubBytes _ hs, ← shiftRowsPow_invSubBytes _ hs, shiftRowsPow_shiftRowsPow]
  change shiftRowsPow _ (invSubBytes s) = shiftRowsPow ((((4 - ((r - 1) % 4) % 4) % 4) + 3) % 4) _
  rw [hmod]

/-- 4-lane equivalence of `aes256DecryptFs` with FIPS 197 `aes256InvCipher` (zero round unrolling). -/
theorem aes256DecryptFs_eq {key : List (BitVec 8)} (hkey : key.length = 32)
    {blocks : Blocks4} (hblocks : Blocks4.Wf blocks) :
    aes256DecryptFs (aes256KeyScheduleFs key) blocks = blocks.map (aes256InvCipher key) := by
  let w := expandKey256 key
  let rkeys := aes256KeyScheduleFs key
  let st0 := invShiftRows2 (invSubBytesFs (addRoundKeyFs (bitslice blocks) rkeys.rk14))
  have hloop : ∀ (n : Nat), n ≤ 13 →
      (List.range n).foldl (fun st i => decRoundFs rkeys (13 - i) st) st0 =
        bitslice (blocks.map (fun b => invShiftRowsPow ((13 - n) % 4) (decState w n b))) := by
    intro n hn
    induction n with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, st0, rkeys, aes256KeyScheduleFs_rk14 hkey,
        addRoundKeyFs_subBytesNots_right, addRoundKeyFs_bitslice, zipWith_replicate_right,
        invSubBytesFs_subBytesNots_bitslice
          (Blocks4.wf_map (fun _ _ => length_addRoundKey _ _) hblocks),
        invShiftRows2_bitslice, blocks4_map_map]
      congr 1
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      dsimp only [decRoundFs]
      rw [show rkeys.getRound (13 - n) =
          subBytesNots (bitslice (Blocks4.replicate
            (invShiftRowsPow ((13 - n) % 4) (roundKey w (13 - n))))) from
          aes256KeyScheduleFs_getRound hkey (by omega) (by omega),
        addRoundKeyFs_subBytesNots_right, addRoundKeyFs_bitslice, zipWith_replicate_right,
        blocks4_map_map]
      have hark_sr : blocks.map (fun b =>
          addRoundKey (invShiftRowsPow ((13 - n) % 4) (decState w n b))
            (invShiftRowsPow ((13 - n) % 4) (roundKey w (13 - n)))) =
          (blocks.map (fun b => addRoundKey (decState w n b) (roundKey w (13 - n)))).map
            (invShiftRowsPow ((13 - n) % 4)) := by
        rw [blocks4_map_map]
        apply blocks4_map_ext
        intro b
        rw [← invShiftRowsPow_addRoundKey]
      rw [hark_sr, invMixColumnsQ_subBytesNots,
        invMixColumnsQ_bitslice ((13 - n) % 4) (by omega),
        blocks4_map_map,
        invSubBytesFs_subBytesNots_bitslice
          (Blocks4.wf_map (fun _ _ => length_invShiftRowsPow _ _) hblocks),
        blocks4_map_map]
      have hsub_eq : 13 - n - 1 = 13 - (n + 1) := by omega
      congr 1
      apply blocks4_map_ext
      intro b
      rw [dec_parity_step (r := 13 - n) (by omega) (length_invMixColumns _), hsub_eq,
        ← decState_succ]
  unfold aes256DecryptFs
  dsimp only
  change invBitslice (addRoundKeyFs
      ((List.range 13).foldl (fun st i => decRoundFs rkeys (13 - i) st) st0) rkeys.rk0) = _
  rw [hloop 13 (by omega),
    show rkeys.rk0 = bitslice (Blocks4.replicate (roundKey w 0)) from
      aes256KeyScheduleFs_rk0 hkey,
    addRoundKeyFs_bitslice, zipWith_replicate_right, blocks4_map_map]
  have hmap_eq : blocks.map (fun b =>
      addRoundKey (invShiftRowsPow ((13 - 13) % 4) (decState w 13 b)) (roundKey w 0)) =
      blocks.map (aes256InvCipher key) := by
    apply blocks4_map_ext
    intro b
    dsimp only [Nat.sub_self, Nat.zero_mod, invShiftRowsPow]
    rw [shiftRowsPow_zero (length_decState w 13 _)]
    rfl
  rw [hmap_eq, invBitslice_bitslice (Blocks4.wf_map (fun _ _ => length_aes256InvCipher key _) hblocks)]

/-! ## Little-Endian `CBC.AesKey` / `CBC.Block` Corollaries for Binary Hook Discharges -/

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

/-- `keyToBytes32` inverts `bytesToKey32` on every 32-byte key buffer. -/
theorem keyToBytes32_bytesToKey32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

@[simp] theorem length_keyToBytes32 (k : AesKey) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

@[simp] theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

/-- 4-block LE corollary: `aes256EncryptFs` on 4 LE-encoded `CBC.Block`s under a 32-byte key buffer
`keyBytes` produces the 4 LE-encoded outputs of `aes256Enc (bytesToKey32 keyBytes)`. -/
theorem aes256EncryptFs_le {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b0 b1 b2 b3 : Block) :
    aes256EncryptFs (aes256KeyScheduleFs keyBytes)
      ⟨blockToBytesLE b0, blockToBytesLE b1, blockToBytesLE b2, blockToBytesLE b3⟩ =
      ⟨blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) b0),
       blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) b1),
       blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) b2),
       blockToBytesLE (aes256Enc (bytesToKey32 keyBytes) b3)⟩ := by
  have hwf : Blocks4.Wf ⟨blockToBytesLE b0, blockToBytesLE b1,
      blockToBytesLE b2, blockToBytesLE b3⟩ := by simp [Blocks4.Wf]
  rw [aes256EncryptFs_eq hkey hwf]
  dsimp only [Blocks4.map, aes256Enc]
  rw [keyToBytes32_bytesToKey32 hkey]
  simp only [blockToBytesLE_bytesToBlock _ (length_aes256Cipher keyBytes _)]

/-- Single-block LE corollary: lane 0 of `aes256EncryptFs` computes `aes256Enc` for any 16-byte
padding lanes `s1, s2, s3` (e.g. zero-initialized `[Block::default(); 4]` in `encrypt_block`). -/
theorem bytesToBlock_b0_aes256EncryptFs {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) {s1 s2 s3 : State} (hs1 : s1.length = 16) (hs2 : s2.length = 16)
    (hs3 : s3.length = 16) :
    bytesToBlock ((aes256EncryptFs (aes256KeyScheduleFs keyBytes)
      ⟨blockToBytesLE b, s1, s2, s3⟩).b0) =
      aes256Enc (bytesToKey32 keyBytes) b := by
  have hwf : Blocks4.Wf ⟨blockToBytesLE b, s1, s2, s3⟩ :=
    ⟨length_blockToBytesLE b, hs1, hs2, hs3⟩
  rw [aes256EncryptFs_eq hkey hwf]
  dsimp only [Blocks4.map, aes256Enc]
  rw [keyToBytes32_bytesToKey32 hkey]

/-- 4-block LE corollary: `aes256DecryptFs` on 4 LE-encoded `CBC.Block`s under a 32-byte key buffer
`keyBytes` produces the 4 LE-encoded outputs of `aes256Dec (bytesToKey32 keyBytes)`. -/
theorem aes256DecryptFs_le {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b0 b1 b2 b3 : Block) :
    aes256DecryptFs (aes256KeyScheduleFs keyBytes)
      ⟨blockToBytesLE b0, blockToBytesLE b1, blockToBytesLE b2, blockToBytesLE b3⟩ =
      ⟨blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) b0),
       blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) b1),
       blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) b2),
       blockToBytesLE (aes256Dec (bytesToKey32 keyBytes) b3)⟩ := by
  have hwf : Blocks4.Wf ⟨blockToBytesLE b0, blockToBytesLE b1,
      blockToBytesLE b2, blockToBytesLE b3⟩ := by simp [Blocks4.Wf]
  rw [aes256DecryptFs_eq hkey hwf]
  dsimp only [Blocks4.map, aes256Dec]
  rw [keyToBytes32_bytesToKey32 hkey]
  simp only [blockToBytesLE_bytesToBlock _ (length_aes256InvCipher keyBytes _)]

/-- Single-block LE corollary: lane 0 of `aes256DecryptFs` computes `aes256Dec` for any 16-byte
padding lanes `s1, s2, s3` (e.g. zero-initialized `[Block::default(); 4]` in `decrypt_block`). -/
theorem bytesToBlock_b0_aes256DecryptFs {keyBytes : List (BitVec 8)} (hkey : keyBytes.length = 32)
    (b : Block) {s1 s2 s3 : State} (hs1 : s1.length = 16) (hs2 : s2.length = 16)
    (hs3 : s3.length = 16) :
    bytesToBlock ((aes256DecryptFs (aes256KeyScheduleFs keyBytes)
      ⟨blockToBytesLE b, s1, s2, s3⟩).b0) =
      aes256Dec (bytesToKey32 keyBytes) b := by
  have hwf : Blocks4.Wf ⟨blockToBytesLE b, s1, s2, s3⟩ :=
    ⟨length_blockToBytesLE b, hs1, hs2, hs3⟩
  rw [aes256DecryptFs_eq hkey hwf]
  dsimp only [Blocks4.map, aes256Dec]
  rw [keyToBytes32_bytesToKey32 hkey]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Equiv
