/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop

/-!
# Pure streaming equivalence for `libcrux_sha2::hacl` and `libcrux_hmac::hmac`

Pure functional models and streaming equivalence proofs matching `libcrux_sha2::hacl::hash_256`
and `libcrux_hmac::hmac` (`w0 = 0`, SHA-256 arm) against `CryptoGames.HMAC.sha256With F`:

- `chunks64` splitting lemmas (`chunks64_append_of_dvd`, `chunks64_exact_one`, `chunks64_exact_two`).
- `haclPadTail` and `haclUpdateLastState` for `0 ≤ rem.length ≤ 64` (covering `< 56`, `56..63`,
  and the `rem.length = 64` full-block boundary case used by `libcrux_hmac`).
- `haclStreaming_eq_sha256With` for any 64-byte-aligned prefix `pref` and tail `rem`
  (`rem.length ≤ 64`).
- Specializations `haclHash256Pure_eq_sha256With`, `hmacInnerEmpty_eq_sha256With`,
  `hmacInnerNonEmpty_eq_sha256With`, and `hmacOuter_eq_sha256With`, used by
  `LibcruxHmacStep.libcruxHmacPure_eq_hmacWith`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV toBEBytes chunks64 sha256Pad sha256With hmacWith)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref (beBytesOfU32)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (toBEBytes_4_eq_beBytesOfU32)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
  (chunks64_of_length_lt chunks64_cons_take_drop)

/-! ## 1. `chunks64` Splitting Lemmas -/

theorem chunks64_append_of_dvd (xs ys : List (BitVec 8)) (hdvd : xs.length % 64 = 0) :
    chunks64 (xs ++ ys) = chunks64 xs ++ chunks64 ys := by
  have go : ∀ k (xs : List (BitVec 8)), xs.length ≤ k → xs.length % 64 = 0 →
      chunks64 (xs ++ ys) = chunks64 xs ++ chunks64 ys := by
    intro k
    induction k with
    | zero =>
      intro xs hle _
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp [chunks64_of_length_lt]
    | succ k ih =>
      intro xs hle hd
      by_cases h64 : xs.length < 64
      · have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp [chunks64_of_length_lt]
      · have hge : 64 ≤ xs.length := by omega
        have hge_app : 64 ≤ (xs ++ ys).length := by rw [List.length_append]; omega
        rw [chunks64_cons_take_drop hge_app, chunks64_cons_take_drop hge,
            List.take_append_of_le_length hge, List.drop_append_of_le_length hge,
            List.cons_append, ih (xs.drop 64) (by simp; omega) (by simp; omega)]
  exact go xs.length xs (Nat.le_refl _) hdvd

theorem chunks64_exact_one (bs : List (BitVec 8)) (h : bs.length = 64) :
    chunks64 bs = [bs] := by
  rw [chunks64_cons_take_drop (by omega), List.take_of_length_le (by omega),
      chunks64_of_length_lt (by simp [h])]

theorem chunks64_exact_two (bs : List (BitVec 8)) (h : bs.length = 128) :
    chunks64 bs = [bs.take 64, bs.drop 64] := by
  rw [chunks64_cons_take_drop (by omega), chunks64_exact_one (bs.drop 64) (by simp [h])]

theorem sha256With_length (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  have hlen : ((chunks64 (sha256Pad m)).foldl F sha256IV).toList.length = 8 :=
    ((chunks64 (sha256Pad m)).foldl F sha256IV).2
  rcases h : ((chunks64 (sha256Pad m)).foldl F sha256IV).toList with
    _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (rw [h] at hlen; try (simp at hlen))
  simp [toBEBytes]

/-! ## 2. `sha256_update_last` Padding Tail (`0 ≤ rem.length ≤ 64`) & `sha256_finish` -/

/-- The 64-byte (`rem.length < 56`) or 128-byte (`56 ≤ rem.length ≤ 64`) padded tail buffer
constructed on the stack by `libcrux_sha2::hacl::sha256_update_last`. -/
@[expose] def haclPadTail (totlen : Nat) (rem : List (BitVec 8)) : List (BitVec 8) :=
  let zlen := if rem.length < 56 then 55 - rem.length else 119 - rem.length
  rem ++ [0x80#8] ++ List.replicate zlen 0#8 ++ toBEBytes 8 (BitVec.ofNat 64 (8 * totlen))

/-- Pure state transition of `sha256_update_last`: 1 compression call when `rem.length < 56`,
2 compression calls when `56 ≤ rem.length ≤ 64`. -/
@[expose] def haclUpdateLastState (F : ShaState → List (BitVec 8) → ShaState)
    (totlen : Nat) (rem : List (BitVec 8)) (st : ShaState) : ShaState :=
  let pad := haclPadTail totlen rem
  if rem.length < 56 then
    F st pad
  else
    F (F st (pad.take 64)) (pad.drop 64)

private theorem toBEBytes_8_length (w : BitVec 64) : (toBEBytes 8 w).length = 8 := by
  simp [toBEBytes]

theorem haclPadTail_length_lt56 (totlen : Nat) {rem : List (BitVec 8)} (h : rem.length < 56) :
    (haclPadTail totlen rem).length = 64 := by
  unfold haclPadTail
  simp only [h, ↓reduceIte, List.length_append, List.length_singleton, List.length_replicate,
    toBEBytes_8_length]
  omega

theorem haclPadTail_length_ge56 (totlen : Nat) {rem : List (BitVec 8)}
    (hlo : 56 ≤ rem.length) (hhi : rem.length ≤ 64) :
    (haclPadTail totlen rem).length = 128 := by
  have hnot : ¬ rem.length < 56 := by omega
  unfold haclPadTail
  simp only [hnot, ↓reduceIte, List.length_append, List.length_singleton, List.length_replicate,
    toBEBytes_8_length]
  omega

theorem sha256Pad_append_eq_haclPadTail (pref rem : List (BitVec 8))
    (hpref : pref.length % 64 = 0) (hrem : rem.length ≤ 64) :
    sha256Pad (pref ++ rem) = pref ++ haclPadTail (pref.length + rem.length) rem := by
  unfold sha256Pad haclPadTail
  have hmod : (pref.length + rem.length) % 64 = rem.length % 64 := by omega
  have hz : (119 - rem.length % 64) % 64 =
      (if rem.length < 56 then 55 - rem.length else 119 - rem.length) := by
    split <;> omega
  rw [List.length_append, hmod, hz]
  dsimp only
  have h128 : (128 : BitVec 8) = 0x80#8 := rfl
  have h0 : (0 : BitVec 8) = 0#8 := rfl
  rw [h128, h0]
  simp only [List.append_assoc]

theorem foldl_chunks64_haclPadTail_eq (F : ShaState → List (BitVec 8) → ShaState)
    (totlen : Nat) (rem : List (BitVec 8)) (st : ShaState) (hrem : rem.length ≤ 64) :
    (chunks64 (haclPadTail totlen rem)).foldl F st = haclUpdateLastState F totlen rem st := by
  unfold haclUpdateLastState
  by_cases h56 : rem.length < 56
  · simp only [h56, ↓reduceIte,
      chunks64_exact_one _ (haclPadTail_length_lt56 totlen h56),
      List.foldl_cons, List.foldl_nil]
  · simp only [h56, ↓reduceIte,
      chunks64_exact_two _ (haclPadTail_length_ge56 totlen (by omega) hrem),
      List.foldl_cons, List.foldl_nil]

theorem unpack32_rev32_eq_toBEBytes_4 (w : BitVec 32) :
    unpack32 ((rev32_64 (w.zeroExtend 64)).truncate 32) = toBEBytes 4 w := by
  rw [toBEBytes_4_eq_beBytesOfU32]
  unfold unpack32 rev32_64 beBytesOfU32
  congr 1; · bv_slice
  congr 1; · bv_slice
  congr 1; · bv_slice
  congr 1; bv_slice

/-! ## 3. Streaming equivalence and `hash_256` / `libcrux_hmac` corollaries -/

/-- Streaming SHA-256 equivalence: compressing any 64-byte-aligned prefix `pref` from `sha256IV`,
applying `haclUpdateLastState` on `rem` (`rem.length ≤ 64`), and serializing big-endian 32-bit
words produces `sha256With F (pref ++ rem)`. -/
theorem haclStreaming_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (pref rem : List (BitVec 8)) (hpref : pref.length % 64 = 0) (hrem : rem.length ≤ 64) :
    (haclUpdateLastState F (pref.length + rem.length) rem
      ((chunks64 pref).foldl F sha256IV)).toList.flatMap (toBEBytes 4) =
      sha256With F (pref ++ rem) := by
  unfold sha256With
  rw [sha256Pad_append_eq_haclPadTail pref rem hpref hrem,
      chunks64_append_of_dvd pref _ hpref, List.foldl_append,
      foldl_chunks64_haclPadTail_eq F _ rem _ hrem]

/-- `libcrux_sha2::hacl::hash_256` streaming split (`nbytes = 64 * (msg.length / 64)`). -/
theorem haclHash256Pure_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (msg : List (BitVec 8)) :
    let nbytes := 64 * (msg.length / 64)
    (haclUpdateLastState F msg.length (msg.drop nbytes)
      ((chunks64 (msg.take nbytes)).foldl F sha256IV)).toList.flatMap (toBEBytes 4) =
      sha256With F msg := by
  dsimp only
  let nbytes := 64 * (msg.length / 64)
  have hle : nbytes ≤ msg.length := Nat.mul_div_le msg.length 64
  have htake_len : (msg.take nbytes).length = nbytes := List.length_take_of_le hle
  have hdrop_len : (msg.drop nbytes).length = msg.length - nbytes := List.length_drop
  have htot : (msg.take nbytes).length + (msg.drop nbytes).length = msg.length := by omega
  have hs := haclStreaming_eq_sha256With F (msg.take nbytes) (msg.drop nbytes)
    (by rw [htake_len]; omega) (by rw [hdrop_len]; omega)
  rwa [htot, List.take_append_drop] at hs

/-- `libcrux_hmac` inner SHA-256 on empty `data = []` (`sha256_update_last(64, 64, ipad)`). -/
theorem hmacInnerEmpty_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (ipad : List (BitVec 8)) (hipad : ipad.length = 64) :
    (haclUpdateLastState F 64 ipad sha256IV).toList.flatMap (toBEBytes 4) =
      sha256With F (ipad ++ []) := by
  have h := haclStreaming_eq_sha256With F [] ipad (by decide) (by omega)
  rw [chunks64_of_length_lt (by decide), List.foldl_nil, List.nil_append, List.length_nil,
      Nat.zero_add, hipad] at h
  rw [List.append_nil]
  exact h

/-- `libcrux_hmac` inner SHA-256 on non-empty `data` (`0 < data.length`,
`nblk = 64 * ((data.length - 1) / 64)`). -/
theorem hmacInnerNonEmpty_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (ipad data : List (BitVec 8)) (hipad : ipad.length = 64) (hpos : 0 < data.length) :
    let nblk := 64 * ((data.length - 1) / 64)
    (haclUpdateLastState F (64 + data.length) (data.drop nblk)
      ((chunks64 (data.take nblk)).foldl F (F sha256IV ipad))).toList.flatMap (toBEBytes 4) =
      sha256With F (ipad ++ data) := by
  dsimp only
  let nblk := 64 * ((data.length - 1) / 64)
  have hnblk_lt : nblk < data.length := by
    have := Nat.mul_div_le (data.length - 1) 64
    omega
  have hrem_le : (data.drop nblk).length ≤ 64 := by
    rw [List.length_drop]
    have := Nat.div_mul_le_self (data.length - 1) 64
    omega
  have htake_len : (data.take nblk).length = nblk := List.length_take_of_le (by omega)
  have hpref_dvd : (ipad ++ data.take nblk).length % 64 = 0 := by
    rw [List.length_append, hipad, htake_len]; omega
  have htot : (ipad ++ data.take nblk).length + (data.drop nblk).length = 64 + data.length := by
    rw [List.length_append, hipad, htake_len, List.length_drop]; omega
  have hfold :
      (chunks64 (ipad ++ data.take nblk)).foldl F sha256IV =
        (chunks64 (data.take nblk)).foldl F (F sha256IV ipad) := by
    rw [chunks64_append_of_dvd ipad _ (by omega), List.foldl_append,
        chunks64_exact_one ipad hipad, List.foldl_cons, List.foldl_nil]
  have hs := haclStreaming_eq_sha256With F (ipad ++ data.take nblk) (data.drop nblk)
    hpref_dvd hrem_le
  rwa [hfold, htot, List.append_assoc, List.take_append_drop] at hs

/-- `libcrux_hmac` outer SHA-256 (`opad` of length `64`, `inner` of length `32`, `totlen = 96`). -/
theorem hmacOuter_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (opad inner : List (BitVec 8)) (hopad : opad.length = 64) (hinner : inner.length = 32) :
    (haclUpdateLastState F 96 inner (F sha256IV opad)).toList.flatMap (toBEBytes 4) =
      sha256With F (opad ++ inner) := by
  have hfold : (chunks64 opad).foldl F sha256IV = F sha256IV opad := by
    rw [chunks64_exact_one opad hopad, List.foldl_cons, List.foldl_nil]
  have htot : opad.length + inner.length = 96 := by omega
  have hs := haclStreaming_eq_sha256With F opad inner (by omega) (by omega)
  rwa [hfold, htot] at hs

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
