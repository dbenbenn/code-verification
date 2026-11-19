/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import ProofLib.SepLogic.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Shared `Fixslice64` CBC Workspace & Loop Helpers (`CbcDec.SoftCommon`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon

open Arm64 ProofLib SepProp ProofLib.SepLogic
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (FsKeys256)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (fsKeys256At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (pack8LE pointsToBytes16_eq_pts64_pair exists_bytes16 pts64x8At)

@[expose] def cbcSoftWork (sp : BitVec 64) (ks : FsKeys256) (prevBs : List (BitVec 8)) : SepProp :=
  memRegion (sp + 0x03c#64) 168 ∗
  memRegion (sp + 0x4b0#64) 64 ∗
  memRegion (sp + 0x870#64) 64 ∗
  fsKeys256At (sp + 0xb40#64) ks ∗
  ((sp + 0xf00#64) ↦ₛ prevBs)

theorem lsr6_ofNat_eq (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 6 = BitVec.ofNat 64 (n / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem ubfx4_2_shift_and_eq (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n) >>> 4) &&& 3#64 = BitVec.ofNat 64 ((n / 16) % 4) := by
  apply BitVec.eq_of_toNat_eq
  have h3 : (3#64).toNat = 2 ^ 2 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, h3, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bv64_ofNat_sub_one {k : Nat} (hk0 : 0 < k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have h2 : (BitVec.ofNat 64 (k - 1)).toNat = k - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by change 1 ≤ (BitVec.ofNat 64 k).toNat; omega), h1, h2]
  rfl

theorem bv64_ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k == 0#64) = decide (k = 0) := by
  by_cases h0 : k = 0
  · subst h0; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at ht
    exact h0 ht

theorem bv64_add_ofNat_64 (ptr : BitVec 64) {q : Nat} (_hq : 64 * (q + 1) < 2 ^ 64) :
    ptr + BitVec.ofNat 64 (64 * q) + 64#64 = ptr + BitVec.ofNat 64 (64 * (q + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl,
      ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) from by omega]

theorem bv64_add_ofNat_16 (ptr : BitVec 64) {m : Nat} (_hm : 16 * (m + 1) < 2 ^ 64) :
    ptr + BitVec.ofNat 64 (16 * m) + 16#64 = ptr + BitVec.ofNat 64 (16 * (m + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ← BitVec.ofNat_add, show 16 * m + 16 = 16 * (m + 1) from by omega]

theorem drop_eq_take_append_drop (bs : List (BitVec 8)) (k n : Nat) :
    bs.drop k = (bs.drop k).take n ++ bs.drop (k + n) := by
  rw [← List.drop_drop, List.take_append_drop]

theorem list_slice64_eq {ct : List (BitVec 8)} {q : Nat} (_hq : 64 * (q + 1) ≤ ct.length) :
    ct = ct.take (64 * q) ++
      ((ct.drop (16 * (4 * q))).take 16 ++
       ((ct.drop (16 * (4 * q + 1))).take 16 ++
        ((ct.drop (16 * (4 * q + 2))).take 16 ++
         ((ct.drop (16 * (4 * q + 3))).take 16 ++
          ct.drop (64 * (q + 1)))))) := by
  rw [show 64 * (q + 1) = 16 * (4 * q + 3) + 16 from by omega,
      ← drop_eq_take_append_drop ct (16 * (4 * q + 3)) 16,
      show 16 * (4 * q + 3) = 16 * (4 * q + 2) + 16 from by omega,
      ← drop_eq_take_append_drop ct (16 * (4 * q + 2)) 16,
      show 16 * (4 * q + 2) = 16 * (4 * q + 1) + 16 from by omega,
      ← drop_eq_take_append_drop ct (16 * (4 * q + 1)) 16,
      show 16 * (4 * q + 1) = 16 * (4 * q) + 16 from by omega,
      ← drop_eq_take_append_drop ct (16 * (4 * q)) 16,
      show 16 * (4 * q) = 64 * q from by omega,
      List.take_append_drop]

theorem exists_bytes64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
      d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47
      d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63 : BitVec 8,
      bs = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
            d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
            d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
            d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63] := by
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : ((bs.drop 16).take 16).length = 16 := by simp [h]
  have h2 : ((bs.drop 32).take 16).length = 16 := by simp [h]
  have h3 : (bs.drop 48).length = 16 := by simp [h]
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15, hd0⟩ := exists_bytes16 h0
  obtain ⟨d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31, hd1⟩ := exists_bytes16 h1
  obtain ⟨d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44,d45,d46,d47, hd2⟩ := exists_bytes16 h2
  obtain ⟨d48,d49,d50,d51,d52,d53,d54,d55,d56,d57,d58,d59,d60,d61,d62,d63, hd3⟩ := exists_bytes16 h3
  have hsplit : bs = bs.take 16 ++ ((bs.drop 16).take 16 ++ ((bs.drop 32).take 16 ++ bs.drop 48)) := by
    rw [show (48 : Nat) = 32 + 16 from rfl, ← drop_eq_take_append_drop bs 32 16,
        show (32 : Nat) = 16 + 16 from rfl, ← drop_eq_take_append_drop bs 16 16,
        List.take_append_drop]
  rw [hsplit, hd0, hd1, hd2, hd3]
  exact ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,
         d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,
         d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44,d45,d46,d47,
         d48,d49,d50,d51,d52,d53,d54,d55,d56,d57,d58,d59,d60,d61,d62,d63, rfl⟩

theorem pts64x8At_pack8LE_eq_pointsToBytes (a : BitVec 64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
     y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32
     y33 y34 y35 y36 y37 y38 y39 y40 y41 y42 y43 y44 y45 y46 y47 y48
     y49 y50 y51 y52 y53 y54 y55 y56 y57 y58 y59 y60 y61 y62 y63 y64 : BitVec 8) :
    pts64x8At a
      (pack8LE y0 y1 y2 y3 y4 y5 y6 y7) (pack8LE y8 y9 y10 y11 y12 y13 y14 y15)
      (pack8LE y16 y17 y18 y20 y21 y22 y23 y24) (pack8LE y25 y26 y27 y28 y29 y30 y31 y32)
      (pack8LE y33 y34 y35 y36 y37 y38 y39 y40) (pack8LE y41 y42 y43 y44 y45 y46 y47 y48)
      (pack8LE y49 y50 y51 y52 y53 y54 y55 y56) (pack8LE y57 y58 y59 y60 y61 y62 y63 y64) =
      (a ↦ₛ [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
             y16, y17, y18, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, y32,
             y33, y34, y35, y36, y37, y38, y39, y40, y41, y42, y43, y44, y45, y46, y47, y48,
             y49, y50, y51, y52, y53, y54, y55, y56, y57, y58, y59, y60, y61, y62, y63, y64]) := by
  have h16_0 := pointsToBytes16_eq_pts64_pair a y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
  have h16_1 := pointsToBytes16_eq_pts64_pair (a + 16#64) y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32
  have h16_2 := pointsToBytes16_eq_pts64_pair (a + 32#64) y33 y34 y35 y36 y37 y38 y39 y40 y41 y42 y43 y44 y45 y46 y47 y48
  have h16_3 := pointsToBytes16_eq_pts64_pair (a + 48#64) y49 y50 y51 y52 y53 y54 y55 y56 y57 y58 y59 y60 y61 y62 y63 y64
  rw [show [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15,
            y16, y17, y18, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, y32,
            y33, y34, y35, y36, y37, y38, y39, y40, y41, y42, y43, y44, y45, y46, y47, y48,
            y49, y50, y51, y52, y53, y54, y55, y56, y57, y58, y59, y60, y61, y62, y63, y64] =
        [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15] ++
        ([y16, y17, y18, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, y32] ++
         ([y33, y34, y35, y36, y37, y38, y39, y40, y41, y42, y43, y44, y45, y46, y47, y48] ++
          [y49, y50, y51, y52, y53, y54, y55, y56, y57, y58, y59, y60, y61, y62, y63, y64])) from rfl,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  change _ =
    (a ↦ₛ [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]) ∗
    (((a + 16#64) ↦ₛ [y16, y17, y18, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, y32]) ∗
     (((a + 16#64 + 16#64) ↦ₛ [y33, y34, y35, y36, y37, y38, y39, y40, y41, y42, y43, y44, y45, y46, y47, y48]) ∗
      ((a + 16#64 + 16#64 + 16#64) ↦ₛ [y49, y50, y51, y52, y53, y54, y55, y56, y57, y58, y59, y60, y61, y62, y63, y64])))
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h16_0, h16_1, h16_2, h16_3]
  unfold pts64x8At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  sep_ac_rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
