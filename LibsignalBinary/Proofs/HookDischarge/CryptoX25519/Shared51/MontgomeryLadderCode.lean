/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import ProofLib.SepLogic.LoopTactics
import ProofLib.SepLogic.ByteRegion
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base

/-!
# Montgomery Ladder Machine-Code Proofs, Part 2 (`Shared51.MontgomeryLadderCode`)

Verifies the 255-bit constant-time Curve25519 Kummer-line scalar multiplication in `x25519CliMultiLib`:
1. `<core::iter::adapters::rev::Rev<...> as Iterator>::nth` (`Blk04`, 41 words, stack `16`)
2. `<&curve25519_dalek::montgomery::MontgomeryPoint as Mul<&Scalar>>::mul` (`Blk15`, 211 words, stack `1680`)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul fpInv leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (
  x25519CliMultiLib x25519CliData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base x25519Leaf_ok x25519Caller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 MontProjPoint montDiffAddAndDouble montLadderLoop)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51_one fe51_mont_a24 fe51OneBytes fe51MontA24Bytes fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables (
  fe51OneBytes_length fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16
  fe51One_readLE_24 fe51One_readLE_32)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded fe51LimbsBoundedAt fe51ValAt montFe51LimbsBoundedAt montFe51ValAt
  montProjBounded montProjOfBytes
  BlackBoxU8Ok RevNthBit254Ok MontProjectiveAsAffineOk MontDiffAddAndDoubleOk
  MontgomeryPointMulOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  sepWP_split_stack_callee sepWP_merge_stack_callee sepWP_unpeel_stack_bytes
  sepWP_callee_grow sepWP_callee_shrink pointsToBytes40_eq_cells pointsToBytesRO40_eq_cells)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  packFe51Bytes packFe51Bytes_length pointsToBytes_packFe51Bytes
  readLE_packFe51Bytes_0 readLE_packFe51Bytes_8 readLE_packFe51Bytes_16
  readLE_packFe51Bytes_24 readLE_packFe51Bytes_32
  fe51ValOfBytes_packFe51Bytes fe51LimbsBounded_packFe51Bytes
  sepWP_peel_stack_region sepWP_unpeel_stack_region)

attribute [local irreducible] x25519CliData01Bytes

/-! ## 1. Block Fetch Generation (`Blk04`, `Blk15`) -/

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 04 x25519CliMultiLib X25519CliPlacement 41 rebase rho sub

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 15 x25519CliMultiLib X25519CliPlacement 211 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl15_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl15.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

/-! ## 2. Scalar Bit Extraction & `decodeU255` Limb Unpacking Helpers -/

private theorem leBytesToNat_div_byte :
    ∀ (bs : List (BitVec 8)) (j : Nat),
      (leBytesToNat bs / 256 ^ j) % 256 = (bs.getD j 0#8).toNat
  | [], j => by simp [leBytesToNat]
  | b :: bs, 0 => by
    simp only [leBytesToNat, List.foldr_cons, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    have hb := b.isLt; omega
  | b :: bs, j + 1 => by
    have ih := leBytesToNat_div_byte bs j
    simp only [leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
    have hb := b.isLt
    generalize List.foldr (fun (b : BitVec 8) acc => acc * 256 + b.toNat) 0 bs = A at ih ⊢
    have hdiv : (A * 256 + b.toNat) / 256 ^ (j + 1) = A / 256 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul,
          show (A * 256 + b.toNat) / 256 = A by omega]
    rw [hdiv, ih]

private theorem mod256_div_pow2_mod2 (N r : Nat) (hr : r < 8) :
    ((N % 256) / 2 ^ r) % 2 = (N / 2 ^ r) % 2 := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem scalar_bit_toNat (bs : List (BitVec 8)) (k : Nat) :
    (((bs.getD (k / 8) 0#8) >>> (k % 8)) &&& 1#8).toNat = (leBytesToNat bs / 2 ^ k) % 2 := by
  have h1 : (((bs.getD (k / 8) 0#8) >>> (k % 8)) &&& 1#8).toNat =
      ((bs.getD (k / 8) 0#8).toNat / 2 ^ (k % 8)) % 2 := by
    rw [BitVec.toNat_and, show (1#8).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 1 = 2 from rfl]
  have hpow : 2 ^ k = 256 ^ (k / 8) * 2 ^ (k % 8) := by
    conv => lhs; rw [show k = 8 * (k / 8) + k % 8 by omega]
    rw [Nat.pow_add, Nat.pow_mul, show 2 ^ 8 = 256 from rfl]
  rw [h1, ← leBytesToNat_div_byte bs (k / 8), mod256_div_pow2_mod2 _ (k % 8) (by omega),
      hpow, ← Nat.div_div_eq_div_mul]

private theorem scalar_bit_u32_eq (bs : List (BitVec 8)) (k : Nat) :
    ((BitVec.zeroExtend 32 (bs.getD (k / 8) 0#8)) >>>
      BitVec.ofNat 32 (k % 8)) &&& 1#32 =
    BitVec.ofNat 32 ((leBytesToNat bs / 2 ^ k) % 2) := by
  apply BitVec.eq_of_toNat_eq
  have hr : k % 8 < 8 := by omega
  rw [BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (BitVec.zeroExtend 32 (bs.getD (k / 8) 0#8) >>> BitVec.ofNat 32 (k % 8)) =
        (BitVec.zeroExtend 32 (bs.getD (k / 8) 0#8) >>> (BitVec.ofNat 32 (k % 8)).toNat) from rfl,
      BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k % 8 < 2 ^ 32), Nat.shiftRight_eq_div_pow,
      show 2 ^ 1 = 2 from rfl, BitVec.toNat_ofNat]
  have hb : (leBytesToNat bs / 2 ^ k) % 2 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hb, ← scalar_bit_toNat bs k]
  rw [BitVec.toNat_and, show (1#8).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 1 = 2 from rfl,
      Nat.mod_eq_of_lt (Nat.lt_trans (bs.getD (k / 8) 0#8).isLt (by decide))]

private theorem scalar_bit_u64_eq (bs : List (BitVec 8)) (m' : Nat) :
    (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 (bs.getD (m' / 8) 0#8) >>>
        ((BitVec.truncate 32 (BitVec.ofNat 64 (m' % 8))).toNat % 32)) &&& 1#64) =
    BitVec.zeroExtend 64 (BitVec.ofNat 8 ((leBytesToNat bs / 2 ^ m') % 2)) := by
  have hsh : (BitVec.truncate 32 (BitVec.ofNat 64 (m' % 8))).toNat % 32 =
      (BitVec.ofNat 32 (m' % 8)).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : m' % 8 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : m' % 8 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : m' % 8 < 32)]
  rw [hsh]
  have h32 : (BitVec.zeroExtend 32 (bs.getD (m' / 8) 0#8) >>>
      (BitVec.ofNat 32 (m' % 8)).toNat) &&& 1#32 =
      BitVec.ofNat 32 ((leBytesToNat bs / 2 ^ m') % 2) := scalar_bit_u32_eq bs m'
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : (BitVec.zeroExtend 32 (bs.getD (m' / 8) 0#8) >>> (BitVec.ofNat 32 (m' % 8)).toNat).toNat < 2 ^ 64 :=
    Nat.lt_trans (BitVec.isLt _) (by decide)
  rw [Nat.mod_eq_of_lt h1, show (1#64).toNat = (1#32).toNat from rfl, ← BitVec.toNat_and, h32]
  rcases (show (leBytesToNat bs / 2 ^ m') % 2 = 0 ∨ (leBytesToNat bs / 2 ^ m') % 2 = 1 by omega) with hb0 | hb0 <;>
    simp [hb0]

private theorem bv64_toNat_bytes (v : BitVec 64) :
    v.toNat = (v.extractLsb' 0 8).toNat + (v.extractLsb' 8 8).toNat * 256 +
      (v.extractLsb' 16 8).toNat * 65536 + (v.extractLsb' 24 8).toNat * 16777216 +
      (v.extractLsb' 32 8).toNat * 4294967296 + (v.extractLsb' 40 8).toNat * 1099511627776 +
      (v.extractLsb' 48 8).toNat * 281474976710656 + (v.extractLsb' 56 8).toNat * 72057594037927936 := by
  have h (k : Nat) : (v.extractLsb' k 8).toNat = (v.toNat / 2 ^ k) % 256 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [h 0, h 8, h 16, h 24, h 32, h 40, h 48, h 56]; have := v.isLt; omega

private theorem pack64_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
      b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
      b6.toNat * 281474976710656 + b7.toNat * 72057594037927936 := by
  have h := unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  simp only [unpack64, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hv := bv64_toNat_bytes (pack64 b0 b1 b2 b3 b4 b5 b6 b7)
  unfold pack64 at hv; rw [h0, h1, h2, h3, h4, h5, h6, h7] at hv; exact hv

private theorem leBytesToNat_take_succ (bs : List (BitVec 8)) :
    ∀ k, k < bs.length →
      leBytesToNat (bs.take (k + 1)) = leBytesToNat (bs.take k) + (bs.getD k 0#8).toNat * 256 ^ k
  | 0, hk => by rcases bs with _ | ⟨b, bs⟩ <;> simp [leBytesToNat] at hk ⊢
  | k + 1, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · have ih := leBytesToNat_take_succ bs k (by simpa using hk)
      simp only [List.take_succ_cons, leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
      rw [ih, Nat.pow_succ, ← Nat.mul_assoc]; omega

private theorem leBytesToNat_32 (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    leBytesToNat bs =
      (bs.getD 0 0#8).toNat + (bs.getD 1 0#8).toNat * 256 ^ 1 +
      (bs.getD 2 0#8).toNat * 256 ^ 2 + (bs.getD 3 0#8).toNat * 256 ^ 3 +
      (bs.getD 4 0#8).toNat * 256 ^ 4 + (bs.getD 5 0#8).toNat * 256 ^ 5 +
      (bs.getD 6 0#8).toNat * 256 ^ 6 + (bs.getD 7 0#8).toNat * 256 ^ 7 +
      (bs.getD 8 0#8).toNat * 256 ^ 8 + (bs.getD 9 0#8).toNat * 256 ^ 9 +
      (bs.getD 10 0#8).toNat * 256 ^ 10 + (bs.getD 11 0#8).toNat * 256 ^ 11 +
      (bs.getD 12 0#8).toNat * 256 ^ 12 + (bs.getD 13 0#8).toNat * 256 ^ 13 +
      (bs.getD 14 0#8).toNat * 256 ^ 14 + (bs.getD 15 0#8).toNat * 256 ^ 15 +
      (bs.getD 16 0#8).toNat * 256 ^ 16 + (bs.getD 17 0#8).toNat * 256 ^ 17 +
      (bs.getD 18 0#8).toNat * 256 ^ 18 + (bs.getD 19 0#8).toNat * 256 ^ 19 +
      (bs.getD 20 0#8).toNat * 256 ^ 20 + (bs.getD 21 0#8).toNat * 256 ^ 21 +
      (bs.getD 22 0#8).toNat * 256 ^ 22 + (bs.getD 23 0#8).toNat * 256 ^ 23 +
      (bs.getD 24 0#8).toNat * 256 ^ 24 + (bs.getD 25 0#8).toNat * 256 ^ 25 +
      (bs.getD 26 0#8).toNat * 256 ^ 26 + (bs.getD 27 0#8).toNat * 256 ^ 27 +
      (bs.getD 28 0#8).toNat * 256 ^ 28 + (bs.getD 29 0#8).toNat * 256 ^ 29 +
      (bs.getD 30 0#8).toNat * 256 ^ 30 + (bs.getD 31 0#8).toNat * 256 ^ 31 := by
  have htake : bs = bs.take 32 := (List.take_of_length_le (by omega)).symm
  conv => lhs; rw [htake]
  repeat rw [leBytesToNat_take_succ bs _ (by omega)]
  have h0 : leBytesToNat (bs.take 0) = 0 := rfl
  rw [h0]; omega

private theorem bv64_mask51_toNat (v : BitVec 64) :
    (v &&& 2251799813685247#64).toNat = v.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]

private theorem fe51_decodeU255_val (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    let l0 := ByteSlice.readLE bs 0 8 &&& 2251799813685247#64
    let l1 := (ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64
    let l2 := (ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64
    let l3 := (ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64
    let l4 := (ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64
    l0.toNat < 2 ^ 52 ∧ l1.toNat < 2 ^ 52 ∧ l2.toNat < 2 ^ 52 ∧ l3.toNat < 2 ^ 52 ∧ l4.toNat < 2 ^ 52 ∧
    fe51Val l0 l1 l2 l3 l4 = decodeU255 bs := by
  intro l0 l1 l2 l3 l4
  have hle32 := leBytesToNat_32 bs hbs
  have hdec : decodeU255 bs = leBytesToNat bs % 2 ^ 255 := by
    unfold decodeU255; rw [List.take_of_length_le (by omega)]
  have hl0 : l0.toNat = (pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
      (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)).toNat % 2 ^ 51 := by
    dsimp only [l0]; rw [bv64_mask51_toNat, ← ByteSlice.pack64_eq_readLE_8 bs 0]
  have hl1 : l1.toNat = ((pack64 (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8)
      (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8)).toNat / 8) % 2 ^ 51 := by
    dsimp only [l1]; rw [bv64_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 6]
  have hl2 : l2.toNat = ((pack64 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8)
      (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)).toNat / 64) % 2 ^ 51 := by
    dsimp only [l2]; rw [bv64_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 12]
  have hl3 : l3.toNat = ((pack64 (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8)
      (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)).toNat / 2) % 2 ^ 51 := by
    dsimp only [l3]; rw [bv64_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 19]
  have hl4 : l4.toNat = ((pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
      (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8)).toNat / 4096) % 2 ^ 51 := by
    dsimp only [l4]; rw [bv64_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 24]
  rw [pack64_toNat] at hl0 hl1 hl2 hl3 hl4
  have := (bs.getD 0 0#8).isLt; have := (bs.getD 1 0#8).isLt; have := (bs.getD 2 0#8).isLt; have := (bs.getD 3 0#8).isLt
  have := (bs.getD 4 0#8).isLt; have := (bs.getD 5 0#8).isLt; have := (bs.getD 6 0#8).isLt; have := (bs.getD 7 0#8).isLt
  have := (bs.getD 8 0#8).isLt; have := (bs.getD 9 0#8).isLt; have := (bs.getD 10 0#8).isLt; have := (bs.getD 11 0#8).isLt
  have := (bs.getD 12 0#8).isLt; have := (bs.getD 13 0#8).isLt; have := (bs.getD 14 0#8).isLt; have := (bs.getD 15 0#8).isLt
  have := (bs.getD 16 0#8).isLt; have := (bs.getD 17 0#8).isLt; have := (bs.getD 18 0#8).isLt; have := (bs.getD 19 0#8).isLt
  have := (bs.getD 20 0#8).isLt; have := (bs.getD 21 0#8).isLt; have := (bs.getD 22 0#8).isLt; have := (bs.getD 23 0#8).isLt
  have := (bs.getD 24 0#8).isLt; have := (bs.getD 25 0#8).isLt; have := (bs.getD 26 0#8).isLt; have := (bs.getD 27 0#8).isLt
  have := (bs.getD 28 0#8).isLt; have := (bs.getD 29 0#8).isLt; have := (bs.getD 30 0#8).isLt; have := (bs.getD 31 0#8).isLt
  rw [hdec]; unfold fe51Val
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩; omega

/-! ## 3. Constant-Time 80-Byte `cswap` / `cselect` & Separation-Logic Helpers -/

private theorem xor_cswap_left (wa wb : BitVec 64) (s : BitVec 8) (hs : s = 0#8 ∨ s = 1#8) :
    ((wb ^^^ wa) &&& (0#64 - BitVec.zeroExtend 64 s)) ^^^ wa =
      if s == 1#8 then wb else wa := by
  rcases hs with rfl | rfl <;>
    simp only [beq_self_eq_true, ↓reduceIte, show (0#8 == 1#8) = false from rfl, Bool.false_eq_true,
               show 0#64 - BitVec.zeroExtend 64 0#8 = 0#64 from rfl,
               show 0#64 - BitVec.zeroExtend 64 1#8 = ~~~0#64 from rfl] <;>
    bv_slice

private theorem xor_cswap_right (wa wb : BitVec 64) (s : BitVec 8) (hs : s = 0#8 ∨ s = 1#8) :
    ((wb ^^^ wa) &&& (0#64 - BitVec.zeroExtend 64 s)) ^^^ wb =
      if s == 1#8 then wa else wb := by
  rcases hs with rfl | rfl <;>
    simp only [beq_self_eq_true, ↓reduceIte, show (0#8 == 1#8) = false from rfl, Bool.false_eq_true,
               show 0#64 - BitVec.zeroExtend 64 0#8 = 0#64 from rfl,
               show 0#64 - BitVec.zeroExtend 64 1#8 = ~~~0#64 from rfl] <;>
    bv_slice

private theorem cselect_word (wa wb : BitVec 64) (b : BitVec 8) (hb : b = 0#8 ∨ b = 1#8) :
    (wb &&& (0#64 - BitVec.zeroExtend 64 b)) ||| (wa &&& (BitVec.zeroExtend 64 b - 1#64)) =
      if b == 1#8 then wb else wa := by
  rcases hb with rfl | rfl <;>
    simp only [beq_self_eq_true, ↓reduceIte, show (0#8 == 1#8) = false from rfl, Bool.false_eq_true] <;>
    bv_bits

private theorem cselect_word_neg (wa wb : BitVec 64) (b : BitVec 8) (hb : b = 0#8 ∨ b = 1#8) :
    (wb &&& (-BitVec.zeroExtend 64 b)) ||| (wa &&& (BitVec.zeroExtend 64 b - 1#64)) =
      if b == 1#8 then wb else wa := by
  rcases hb with rfl | rfl <;>
    simp only [beq_self_eq_true, ↓reduceIte, show (0#8 == 1#8) = false from rfl, Bool.false_eq_true] <;>
    bv_bits

private theorem cselect_word_neg_add (wa wb : BitVec 64) (b : BitVec 8) (hb : b = 0#8 ∨ b = 1#8) :
    (wb &&& (-BitVec.zeroExtend 64 b)) ||| (wa &&& (BitVec.zeroExtend 64 b + (-1#64))) =
      if b == 1#8 then wb else wa := by
  rcases hb with rfl | rfl <;>
    simp only [beq_self_eq_true, ↓reduceIte, show (0#8 == 1#8) = false from rfl, Bool.false_eq_true] <;>
    bv_bits

private theorem sepWP_replace_sub (A B : SepProp)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (heq : A = B)
    (hf : Full = A ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (B ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, heq]; exact hnext

private theorem pointsToBytes80_eq_cells10 (p : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 80) :
    (p ↦ₛ bs) =
      ((p ↦₆₄ ByteSlice.readLE bs 0 8) ∗
       ((p + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
       ((p + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗
       ((p + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
       ((p + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8) ∗
       ((p + 40#64) ↦₆₄ ByteSlice.readLE bs 40 8) ∗
       ((p + 48#64) ↦₆₄ ByteSlice.readLE bs 48 8) ∗
       ((p + 56#64) ↦₆₄ ByteSlice.readLE bs 56 8) ∗
       ((p + 64#64) ↦₆₄ ByteSlice.readLE bs 64 8) ∗
       ((p + 72#64) ↦₆₄ ByteSlice.readLE bs 72 8)) := by
  have hsplit : (p ↦ₛ bs) = ((p ↦ₛ bs.take 40) ∗ ((p + 40#64) ↦ₛ bs.drop 40)) := by
    conv => lhs; rw [(List.take_append_drop 40 bs).symm]
    rw [pointsToBytes_append, show (bs.take 40).length = 40 by simp [h]]
  have hr_take (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE (bs.take 40) off 8 = ByteSlice.readLE bs off 8 := by
    apply ByteSlice.readLE_congr; intro i hi; simp only [List.getD, List.getElem?_take]
    split
    · rfl
    · omega
  have hr_drop : ∀ (off n : Nat), ByteSlice.readLE (bs.drop 40) off n = ByteSlice.readLE bs (40 + off) n := by
    intro off n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih]
      simp only [List.getD, List.getElem?_drop, show 40 + off + n = 40 + (off + n) by omega]
  rw [hsplit, pointsToBytes40_eq_cells p (bs.take 40) (by simp [h]),
      pointsToBytes40_eq_cells (p + 40#64) (bs.drop 40) (by simp [h]),
      hr_take 0 (by omega), hr_take 8 (by omega), hr_take 16 (by omega),
      hr_take 24 (by omega), hr_take 32 (by omega),
      hr_drop 0 8, hr_drop 8 8, hr_drop 16 8, hr_drop 24 8, hr_drop 32 8]
  have ha (a b : BitVec 64) (heq : 40#64 + a = b) : p + 40#64 + a = p + b := by
    rw [BitVec.add_assoc, heq]
  rw [ha 8#64 48#64 rfl, ha 16#64 56#64 rfl, ha 24#64 64#64 rfl, ha 32#64 72#64 rfl]
  simp only [sepConj_assoc]

private theorem sub_add_eq_sub_sub' (sp off k : BitVec 64) : (sp - off) + k = sp - (off - k) := by bv_bits

private theorem pointsToBytes80_sub320_eq (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 80) :
    ((sp - 320#64) ↦ₛ bs) =
      (((sp - 320#64) ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((sp - 312#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
       ((sp - 304#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((sp - 296#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
       ((sp - 288#64) ↦₆₄ ByteSlice.readLE bs 32 8) ∗ ((sp - 280#64) ↦₆₄ ByteSlice.readLE bs 40 8) ∗
       ((sp - 272#64) ↦₆₄ ByteSlice.readLE bs 48 8) ∗ ((sp - 264#64) ↦₆₄ ByteSlice.readLE bs 56 8) ∗
       ((sp - 256#64) ↦₆₄ ByteSlice.readLE bs 64 8) ∗ ((sp - 248#64) ↦₆₄ ByteSlice.readLE bs 72 8)) := by
  rw [pointsToBytes80_eq_cells10 (sp - 320#64) bs h]
  simp only [sub_add_eq_sub_sub', show (320#64 : BitVec 64) - 8#64 = 312#64 from rfl,
    show (320#64 : BitVec 64) - 16#64 = 304#64 from rfl, show (320#64 : BitVec 64) - 24#64 = 296#64 from rfl,
    show (320#64 : BitVec 64) - 32#64 = 288#64 from rfl, show (320#64 : BitVec 64) - 40#64 = 280#64 from rfl,
    show (320#64 : BitVec 64) - 48#64 = 272#64 from rfl, show (320#64 : BitVec 64) - 56#64 = 264#64 from rfl,
    show (320#64 : BitVec 64) - 64#64 = 256#64 from rfl, show (320#64 : BitVec 64) - 72#64 = 248#64 from rfl]

private theorem pointsToBytes80_sub240_eq (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 80) :
    ((sp - 240#64) ↦ₛ bs) =
      (((sp - 240#64) ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((sp - 232#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
       ((sp - 224#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((sp - 216#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
       ((sp - 208#64) ↦₆₄ ByteSlice.readLE bs 32 8) ∗ ((sp - 200#64) ↦₆₄ ByteSlice.readLE bs 40 8) ∗
       ((sp - 192#64) ↦₆₄ ByteSlice.readLE bs 48 8) ∗ ((sp - 184#64) ↦₆₄ ByteSlice.readLE bs 56 8) ∗
       ((sp - 176#64) ↦₆₄ ByteSlice.readLE bs 64 8) ∗ ((sp - 168#64) ↦₆₄ ByteSlice.readLE bs 72 8)) := by
  rw [pointsToBytes80_eq_cells10 (sp - 240#64) bs h]
  simp only [sub_add_eq_sub_sub', show (240#64 : BitVec 64) - 8#64 = 232#64 from rfl,
    show (240#64 : BitVec 64) - 16#64 = 224#64 from rfl, show (240#64 : BitVec 64) - 24#64 = 216#64 from rfl,
    show (240#64 : BitVec 64) - 32#64 = 208#64 from rfl, show (240#64 : BitVec 64) - 40#64 = 200#64 from rfl,
    show (240#64 : BitVec 64) - 48#64 = 192#64 from rfl, show (240#64 : BitVec 64) - 56#64 = 184#64 from rfl,
    show (240#64 : BitVec 64) - 64#64 = 176#64 from rfl, show (240#64 : BitVec 64) - 72#64 = 168#64 from rfl]

private theorem packFe51_sub_eq (sp off o8 o16 o24 o32 w0 w1 w2 w3 w4 : BitVec 64)
    (h8 : off - 8#64 = o8 := by rfl) (h16 : off - 16#64 = o16 := by rfl)
    (h24 : off - 24#64 = o24 := by rfl) (h32 : off - 32#64 = o32 := by rfl) :
    ((sp - off) ↦ₛ packFe51Bytes w0 w1 w2 w3 w4) =
      (((sp - off) ↦₆₄ w0) ∗ ((sp - o8) ↦₆₄ w1) ∗ ((sp - o16) ↦₆₄ w2) ∗
       ((sp - o24) ↦₆₄ w3) ∗ ((sp - o32) ↦₆₄ w4)) := by
  rw [pointsToBytes_packFe51Bytes (sp - off), sub_add_eq_sub_sub', h8,
      sub_add_eq_sub_sub', h16, sub_add_eq_sub_sub', h24, sub_add_eq_sub_sub', h32]

private theorem packProj80_sub_eq (sp off o8 o16 o24 o32 o40 o48 o56 o64 o72 : BitVec 64)
    (u0 u1 u2 u3 u4 w0 w1 w2 w3 w4 : BitVec 64)
    (h8 : off - 8#64 = o8 := by rfl) (h16 : off - 16#64 = o16 := by rfl)
    (h24 : off - 24#64 = o24 := by rfl) (h32 : off - 32#64 = o32 := by rfl)
    (h40 : off - 40#64 = o40 := by rfl) (h48 : off - 48#64 = o48 := by rfl)
    (h56 : off - 56#64 = o56 := by rfl) (h64 : off - 64#64 = o64 := by rfl)
    (h72 : off - 72#64 = o72 := by rfl) :
    ((sp - off) ↦ₛ (packFe51Bytes u0 u1 u2 u3 u4 ++ packFe51Bytes w0 w1 w2 w3 w4)) =
      (((sp - off) ↦₆₄ u0) ∗ ((sp - o8) ↦₆₄ u1) ∗ ((sp - o16) ↦₆₄ u2) ∗
       ((sp - o24) ↦₆₄ u3) ∗ ((sp - o32) ↦₆₄ u4) ∗ ((sp - o40) ↦₆₄ w0) ∗
       ((sp - o48) ↦₆₄ w1) ∗ ((sp - o56) ↦₆₄ w2) ∗ ((sp - o64) ↦₆₄ w3) ∗ ((sp - o72) ↦₆₄ w4)) := by
  rw [pointsToBytes_append, packFe51Bytes_length, show BitVec.ofNat 64 40 = 40#64 from rfl,
      sub_add_eq_sub_sub' sp off 40#64, h40,
      packFe51_sub_eq sp off o8 o16 o24 o32 u0 u1 u2 u3 u4 h8 h16 h24 h32,
      packFe51_sub_eq sp o40 o48 o56 o64 o72 w0 w1 w2 w3 w4
        (by subst h40 h48; bv_omega) (by subst h40 h56; bv_omega)
        (by subst h40 h64; bv_omega) (by subst h40 h72; bv_omega)]
  simp only [sepConj_assoc]

private theorem packProj80_props (u0 u1 u2 u3 u4 w0 w1 w2 w3 w4 : BitVec 64) (B : Nat)
    (hu0 : u0.toNat < B) (hu1 : u1.toNat < B) (hu2 : u2.toNat < B) (hu3 : u3.toNat < B) (hu4 : u4.toNat < B)
    (hw0 : w0.toNat < B) (hw1 : w1.toNat < B) (hw2 : w2.toNat < B) (hw3 : w3.toNat < B) (hw4 : w4.toNat < B) :
    let bs := packFe51Bytes u0 u1 u2 u3 u4 ++ packFe51Bytes w0 w1 w2 w3 w4
    montProjBounded bs B ∧
    montProjOfBytes bs = ⟨fe51Val u0 u1 u2 u3 u4 % p25519, fe51Val w0 w1 w2 w3 w4 % p25519⟩ := by
  intro bs
  have hr_l (off : Nat) (ho : off + 8 ≤ 40) :
      ByteSlice.readLE bs off 8 = ByteSlice.readLE (packFe51Bytes u0 u1 u2 u3 u4) off 8 := by
    apply ByteSlice.readLE_congr; intro i hi
    have hlt : off + i < (packFe51Bytes u0 u1 u2 u3 u4).length := by
      rw [packFe51Bytes_length]; omega
    simp only [bs, List.getD, List.getElem?_append_left hlt]
  have hr_r : ∀ (off n : Nat),
      ByteSlice.readLE bs (40 + off) n = ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) off n := by
    intro off n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih]
      have hle : (packFe51Bytes u0 u1 u2 u3 u4).length ≤ 40 + (off + n) := by
        rw [packFe51Bytes_length]; omega
      simp only [bs, List.getD, show 40 + off + n = 40 + (off + n) by omega,
                 List.getElem?_append_right hle, packFe51Bytes_length, Nat.add_sub_cancel_left]
  have h40 := hr_r 0 8; have h48 := hr_r 8 8; have h56 := hr_r 16 8
  have h64 := hr_r 24 8; have h72 := hr_r 32 8
  simp only [Nat.reduceAdd] at h40 h48 h56 h64 h72
  unfold montProjBounded montFe51LimbsBoundedAt fe51LimbsBoundedAt montProjOfBytes montFe51ValAt fe51ValAt
  simp only [Nat.reduceAdd, hr_l 0 (by omega), hr_l 8 (by omega), hr_l 16 (by omega),
    hr_l 24 (by omega), hr_l 32 (by omega), h40, h48, h56, h64, h72,
    readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
    readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
  exact ⟨⟨by simp [bs, packFe51Bytes_length], ⟨hu0, hu1, hu2, hu3, hu4⟩, ⟨hw0, hw1, hw2, hw3, hw4⟩⟩, trivial⟩

private theorem cswap_readLE_if (r0 r1 : List (BitVec 8)) (off : Nat) (s : BitVec 8) :
    (if s == 1#8 then ByteSlice.readLE r1 off 8 else ByteSlice.readLE r0 off 8) =
    ByteSlice.readLE (if s == 1#8 then r1 else r0) off 8 := by
  cases (s == 1#8) <;> rfl

private theorem truncate8_zext64 (x : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 x) = x := by bv_bits

private theorem truncate8_zext32_zext64 (x : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 x))) = x := by
  bv_bits

private theorem truncate8_zext32_trunc32 {v : BitVec 64} {x : BitVec 8}
    (w : BitVec 64) (h : BitVec.truncate 8 v = x) (hw : w = BitVec.zeroExtend 64 (BitVec.truncate 32 v) := by rfl) :
    BitVec.truncate 8 w = x := by
  subst hw; revert h; bv_bits

private theorem pure_eq_true_of {p : Prop} (hp : p) : (⌜p⌝ : SepProp) = ⌜True⌝ :=
  congrArg SepProp.pure (propext ⟨fun _ => trivial, fun _ => hp⟩)

private theorem deferred_cswap_points {x0 x1 : MontProjPoint} {r0_bs r1_bs : List (BitVec 8)}
    {prev cur : Nat} (hprev : prev < 2) (hcur : cur < 2)
    (hr : (montProjOfBytes r0_bs, montProjOfBytes r1_bs) =
      if prev == 1 then (x1, x0) else (x0, x1)) :
    let s : BitVec 8 := BitVec.ofNat 8 cur ^^^ BitVec.ofNat 8 prev
    (montProjOfBytes (if s == 1#8 then r1_bs else r0_bs),
     montProjOfBytes (if s == 1#8 then r0_bs else r1_bs)) =
      if cur == 1 then (x1, x0) else (x0, x1) := by
  have h1 := Prod.mk.inj hr
  rcases (show prev = 0 ∨ prev = 1 by omega) with rfl | rfl <;>
    rcases (show cur = 0 ∨ cur = 1 by omega) with rfl | rfl <;>
    simp_all

private theorem montLadderLoop_step_eq (idx k u1 : Nat) (x0 x1 : MontProjPoint)
    (cur : Nat) (hcur_eq : cur = (k / 2 ^ idx) % 2)
    (p0 p1 q0 q1 : MontProjPoint)
    (hp : (p0, p1) = if cur == 1 then (x1, x0) else (x0, x1))
    (hq0 : q0 = (montDiffAddAndDouble u1 p0 p1).1)
    (hq1 : q1 = (montDiffAddAndDouble u1 p0 p1).2) :
    let (x0', x1') := if cur == 1 then (q1, q0) else (q0, q1)
    (q0, q1) = (if cur == 1 then (x1', x0') else (x0', x1')) ∧
    montLadderLoop (idx + 1) k u1 x0 x1 = montLadderLoop idx k u1 x0' x1' := by
  have hcur : cur < 2 := by rw [hcur_eq]; omega
  rcases (show cur = 0 ∨ cur = 1 by omega) with rfl | rfl
  · simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at hp ⊢
    refine ⟨trivial, ?_⟩
    conv => lhs; unfold montLadderLoop
    rw [← hcur_eq]
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    subst hq0 hq1; rfl
  · simp only [BEq.rfl, ↓reduceIte] at hp ⊢
    refine ⟨trivial, ?_⟩
    conv => lhs; unfold montLadderLoop
    rw [← hcur_eq]
    simp only [BEq.rfl, ↓reduceIte]
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    subst hq0 hq1; rfl

private theorem sepWP_have_state {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (φ : State → Prop) (hφ : φ s) (h : φ s → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom := h hφ

private theorem u8_ret_and_255 {v : BitVec 64} {b : BitVec 8}
    (h : BitVec.setWidth 8 v = b) :
    (v &&& 255#64) = BitVec.zeroExtend 64 b := by
  revert h; bv_bits

private theorem nth_ret_props {v : BitVec 64} {b : BitVec 8}
    (h : BitVec.setWidth 8 v = b)
    (hb : b.toNat < 2) :
    (BitVec.truncate 32 v &&& 255#32).toNat < 2 ∧
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) &&& 255#64).toNat < 2 ∧
    ((BitVec.truncate 32 v &&& 255#32) == 2#32) = false ∧
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) &&& 255#64) = BitVec.zeroExtend 64 b ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 v &&& 255#32) = BitVec.zeroExtend 64 b ∧
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v) &&& 255#64) = b ∧
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v &&& 255#32)) = b := by
  have h1 : (BitVec.truncate 32 v &&& 255#32) = BitVec.zeroExtend 32 b := by revert h; bv_bits
  have h2 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v) &&& 255#64) = BitVec.zeroExtend 64 b := by
    revert h; bv_bits
  have hlt1 : (BitVec.truncate 32 v &&& 255#32).toNat < 2 := by
    rw [h1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)]; exact hb
  have hlt2 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v) &&& 255#64).toNat < 2 := by
    rw [h2, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]; exact hb
  have hne2 : ((BitVec.truncate 32 v &&& 255#32) == 2#32) = false := by
    apply beq_false_of_ne; intro heq; rw [heq] at hlt1; revert hlt1; decide
  refine ⟨hlt1, hlt2, hne2, h2, by revert h; bv_bits, by revert h; bv_bits, by revert h; bv_bits⟩

private theorem sepWP_peel_byte (sp : BitVec 64) (off rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - BitVec.ofNat 64 off) off ∗ P := by sep_frame)
    (hoff : off = 1 + rem := by decide) (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : ∀ b0 : BitVec 8,
      SepWP prog target_pc s
        ((((sp - BitVec.ofNat 64 off) ↦₈ b0) ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  apply sepWP_peel_stack_region sp off 1 rem (hf := hf) (hoff := hoff) (hb := hb)
  rw [memRegion_one]
  wp_pull_exists
  rename_i b0
  refine Eq.mp (congrArg (fun Q => SepWP _ _ _ Q _ _) ?_) (hnext b0)
  sep_ac_rfl

private theorem sepWP_unpeel_byte (sp : BitVec 64) (off rem : Nat) {b0 : BitVec 8}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - BitVec.ofNat 64 off) ↦₈ b0) ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P := by sep_frame)
    (hoff : off = 1 + rem := by decide) (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - BitVec.ofNat 64 off) off ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  refine SepWP.weaken_pre
    (P' := ((∃∗ b : BitVec 8, (sp - BitVec.ofNat 64 off) ↦₈ b) ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P)
    (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_right b0 (Entails.refl _)))) ?_
  rw [← memRegion_one]
  exact sepWP_unpeel_stack_region sp off 1 rem (hf := rfl) (hoff := hoff) (hb := hb) hnext

private theorem sepWP_focus_for_step {prog : Program} {target_pc : BitVec 64} {s : State}
    {Full A B C D E F P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (A ∗ B ∗ C ∗ D ∗ E ∗ F) ∗ P)
    (h : SepWP prog target_pc s (A ∗ B ∗ C ∗ D ∗ E ∗ F ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]; simpa only [sepConj_assoc] using h

/-! ## 4. Shared Kummer-Line Step, 254-Iteration Loop, & Post-Loop `cselect` + `as_affine` -/

set_option maxHeartbeats 800000 in
private theorem mont_ladder_step [X25519CliPlacement]
    (hbb : BlackBoxU8Ok) (hdadd : MontDiffAddAndDoubleOk)
    (b sp out_ptr : BitVec 64)
    (u1_bs r0_bs r1_bs : List (BitVec 8)) (prev_slot : BitVec 8)
    (idx k u1 prev cur : Nat) (x0 x1 : MontProjPoint)
    {vregs0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {target_pc : BitVec 64} {s0 : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (_hb : X25519Base x25519CliPl15 b) (hbase : x25519CliPl15.base = b)
    (hpc : s0.pc = b + 248#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp - 368#64)
    (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s0 = vregs0)
    (hx29 : s0.readReg64 (.gpr 29#5) = sp - 96#64)
    (hx19 : s0.readReg64 (.gpr 19#5) = out_ptr)
    (hx20 : s0.readReg64 (.gpr 20#5) = 0#64)
    (hx21 : s0.readReg64 (.gpr 21#5) = 0#64)
    (_hw22 : BitVec.truncate 8 (s0.readReg64 (.gpr 22#5)) = BitVec.ofNat 8 cur)
    (hx22_hi : s0.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (BitVec.ofNat 8 cur))
    (hw0 : BitVec.truncate 8 (s0.readReg64 (.gpr 0#5)) = BitVec.ofNat 8 prev)
    (hcl : x25519CliMultiLib.CodeLoaded x25519CliMpl s0.mem)
    (hprev : prev < 2) (hcur_eq : cur = (k / 2 ^ idx) % 2)
    (hu1_b : fe51LimbsBounded u1_bs (2 ^ 54))
    (hu1_v : fe51ValOfBytes u1_bs % p25519 = u1)
    (hr0_b : montProjBounded r0_bs (2 ^ 52))
    (hr1_b : montProjBounded r1_bs (2 ^ 52))
    (hr_pts : (montProjOfBytes r0_bs, montProjOfBytes r1_bs) =
      if prev == 1 then (x1, x0) else (x0, x1))
    (hnext : ∀ (s' : State) (r0_out r1_out : List (BitVec 8)) (x0' x1' : MontProjPoint),
      s'.pc = b + 192#64 →
      s'.status = .Running →
      s'.sp = sp - 368#64 →
      calleeSavedVRegs s' = vregs0 →
      s'.readReg64 (.gpr 29#5) = sp - 96#64 →
      s'.readReg64 (.gpr 19#5) = out_ptr →
      s'.readReg64 (.gpr 21#5) = 0#64 →
      BitVec.truncate 8 (s'.readReg64 (.gpr 0#5)) = BitVec.ofNat 8 cur →
      x25519CliMultiLib.CodeLoaded x25519CliMpl s'.mem →
      montProjBounded r0_out (2 ^ 52) →
      montProjBounded r1_out (2 ^ 52) →
      (montProjOfBytes r0_out, montProjOfBytes r1_out) =
        (if cur == 1 then (x1', x0') else (x0', x1')) →
      montLadderLoop (idx + 1) k u1 x0 x1 = montLadderLoop idx k u1 x0' x1' →
      SepWP (x25519CliPC15.rebase b (fun _ => none)) target_pc s'
        (((sp - 360#64) ↦ₛ u1_bs) ∗ ((sp - 320#64) ↦ₛ r0_out) ∗ ((sp - 240#64) ↦ₛ r1_out) ∗
         ((sp - 148#64) ↦₈ BitVec.ofNat 8 cur) ∗
         memRegion (sp - 368#64 - 1312#64) 1312 ∗
         (fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes) ∗ P) post oom) :
    SepWP (x25519CliPC15.rebase b (fun _ => none)) target_pc s0
      (((sp - 360#64) ↦ₛ u1_bs) ∗ ((sp - 320#64) ↦ₛ r0_bs) ∗ ((sp - 240#64) ↦ₛ r1_bs) ∗
       ((sp - 148#64) ↦₈ prev_slot) ∗
       memRegion (sp - 368#64 - 1312#64) 1312 ∗
       (fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes) ∗ P) post oom := by
  have hcur : cur < 2 := by rw [hcur_eq]; omega
  apply sepWP_callee_shrink (sp - 368#64) 1312 16 1296
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hbb
  rw [hsp, hvregs, hx29, hx19, hx20, hx21, hx22_hi] at *
  norm_sf 16
  wp_conv_pre => try rw [show sp - 384#64 = sp - 368#64 - 16#64 by bv_omega]
  apply sepWP_callee_grow (sp - 368#64) 1312 16 1296
  generalize hs_eq : (BitVec.ofNat 8 cur ^^^ BitVec.ofNat 8 prev) = swap_b at *
  have hswap_or : swap_b = 0#8 ∨ swap_b = 1#8 := by
    subst hs_eq
    rcases (show cur = 0 ∨ cur = 1 by omega) with rfl | rfl <;>
      rcases (show prev = 0 ∨ prev = 1 by omega) with rfl | rfl <;> decide
  have hr0_len : r0_bs.length = 80 := hr0_b.1
  have hr1_len : r1_bs.length = 80 := hr1_b.1
  wp_conv_pre =>
    rw [pointsToBytes80_sub320_eq sp r0_bs hr0_len, pointsToBytes80_sub240_eq sp r1_bs hr1_len]
  wp_cut_codeLoaded
  wp_sym_steps 64
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_cswap
  have hmask_eq :
      (-BitVec.setWidth 64 (BitVec.ofNat 8 (k / 2 ^ idx % 2) ^^^ BitVec.ofNat 8 prev)) =
      0#64 - BitVec.zeroExtend 64 swap_b := by
    rw [← hcur_eq, hs_eq]; bv_bits
  have hp0_len : (if swap_b == 1#8 then r1_bs else r0_bs).length = 80 := by
    cases (swap_b == 1#8) <;> assumption
  have hp1_len : (if swap_b == 1#8 then r0_bs else r1_bs).length = 80 := by
    cases (swap_b == 1#8) <;> assumption
  wp_conv_pre =>
    simp only [hmask_eq, xor_cswap_left _ _ swap_b hswap_or, xor_cswap_right _ _ swap_b hswap_or,
               cswap_readLE_if]
  apply sepWP_replace_sub _ _ (pointsToBytes80_sub320_eq sp (if swap_b == 1#8 then r1_bs else r0_bs) hp0_len).symm
  apply sepWP_replace_sub _ _ (pointsToBytes80_sub240_eq sp (if swap_b == 1#8 then r0_bs else r1_bs) hp1_len).symm
  have hp0_b53 : montProjBounded (if swap_b == 1#8 then r1_bs else r0_bs) (2 ^ 53) := by
    have h0' : montProjBounded r0_bs (2 ^ 53) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨b0,b1,b2,b3,b4⟩⟩ := hr0_b
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    have h1' : montProjBounded r1_bs (2 ^ 53) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨b0,b1,b2,b3,b4⟩⟩ := hr1_b
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    cases (swap_b == 1#8) <;> assumption
  have hp1_b53 : montProjBounded (if swap_b == 1#8 then r0_bs else r1_bs) (2 ^ 53) := by
    have h0' : montProjBounded r0_bs (2 ^ 53) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨b0,b1,b2,b3,b4⟩⟩ := hr0_b
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    have h1' : montProjBounded r1_bs (2 ^ 53) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨b0,b1,b2,b3,b4⟩⟩ := hr1_b
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    cases (swap_b == 1#8) <;> assumption
  obtain ⟨_, hu1_0, hu1_1, hu1_2, hu1_3, hu1_4⟩ := hu1_b
  obtain ⟨_, ⟨hp0_0,hp0_1,hp0_2,hp0_3,hp0_4⟩, ⟨hp0_5,hp0_6,hp0_7,hp0_8,hp0_9⟩⟩ := hp0_b53
  obtain ⟨_, ⟨hp1_0,hp1_1,hp1_2,hp1_3,hp1_4⟩, ⟨hp1_5,hp1_6,hp1_7,hp1_8,hp1_9⟩⟩ := hp1_b53
  apply sepWP_callee_shrink (sp - 368#64) 1312 1056 256
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hdadd
  clean_prev_sf; norm_sf 1056
  wp_conv_pre => try rw [show sp - 1424#64 = sp - 368#64 - 1056#64 by bv_omega]
  apply sepWP_callee_grow (sp - 368#64) 1312 1056 256
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_end
  have hcswap_pts := deferred_cswap_points hprev hcur hr_pts
  rw [hs_eq] at hcswap_pts
  have hstep_math := montLadderLoop_step_eq idx k u1 x0 x1 cur hcur_eq
    (montProjOfBytes (if swap_b == 1#8 then r1_bs else r0_bs))
    (montProjOfBytes (if swap_b == 1#8 then r0_bs else r1_bs))
    (montProjOfBytes w) (montProjOfBytes w_1) hcswap_pts
    (by rw [‹montProjOfBytes w = _›, hu1_v]) (by rw [‹montProjOfBytes w_1 = _›, hu1_v])
  let x01' := if cur == 1 then (montProjOfBytes w_1, montProjOfBytes w) else (montProjOfBytes w, montProjOfBytes w_1)
  refine Eq.mp (congrArg (fun Q => SepWP _ target_pc _ Q post oom) ?_)
    (hnext _ w w_1 x01'.1 x01'.2
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by
        (conv => lhs; arg 2; simp only [wp_norm, arm64_norm])
        try rw [← hcur_eq]
        exact truncate8_zext64 _)
      hcl_end
      ‹montProjBounded w (2 ^ 52)› ‹montProjBounded w_1 (2 ^ 52)›
      hstep_math.1 hstep_math.2)
  try rw [truncate8_zext64]
  try rw [← hcur_eq]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
private theorem mont_ladder_loop [X25519CliPlacement]
    (hbb : BlackBoxU8Ok) (hdadd : MontDiffAddAndDoubleOk)
    (b sp out_ptr scalar_ptr : BitVec 64)
    (u1_bs scalar_bs r0_init r1_init : List (BitVec 8))
    (u1 : Nat) (x0_init x1_init res : MontProjPoint)
    {s1 : State}
    (hb : X25519Base x25519CliPl15 b) (hbase : x25519CliPl15.base = b)
    (hpc1 : s1.pc = b + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp - 368#64)
    (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hx29_1 : s1.readReg64 (.gpr 29#5) = sp - 96#64)
    (hx19_1 : s1.readReg64 (.gpr 19#5) = out_ptr)
    (hx21_1 : s1.readReg64 (.gpr 21#5) = 0#64)
    (hw0_1 : BitVec.truncate 8 (s1.readReg64 (.gpr 0#5)) =
      BitVec.ofNat 8 ((leBytesToNat scalar_bs / 2 ^ 254) % 2))
    (hcl1 : x25519CliMultiLib.CodeLoaded x25519CliMpl s1.mem)
    (hsc_len : scalar_bs.length = 32)
    (hu1_b : fe51LimbsBounded u1_bs (2 ^ 54))
    (hu1_v : fe51ValOfBytes u1_bs % p25519 = u1)
    (hr0_b1 : montProjBounded r0_init (2 ^ 52))
    (hr1_b1 : montProjBounded r1_init (2 ^ 52))
    (hr_pts1 : (montProjOfBytes r0_init, montProjOfBytes r1_init) =
      if ((leBytesToNat scalar_bs / 2 ^ 254) % 2) == 1 then (x1_init, x0_init) else (x0_init, x1_init))
    (hloop1 : montLadderLoop 254 (leBytesToNat scalar_bs) u1 x0_init x1_init = res) :
    let exit_pc := b + 576#64
    let k := leBytesToNat scalar_bs
    SepWP (x25519CliPC15.rebase b (fun _ => none)) exit_pc s1
      (((sp - 360#64) ↦ₛ u1_bs) ∗ ((sp - 320#64) ↦ₛ r0_init) ∗ ((sp - 240#64) ↦ₛ r1_init) ∗
       ((sp - 148#64) ↦₈ BitVec.ofNat 8 ((k / 2 ^ 254) % 2)) ∗
       ((sp - 144#64) ↦₆₄ scalar_ptr) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
       ((sp - 128#64) ↦₆₄ 254#64) ∗ ((sp - 120#64) ↦₆₄ 0#64) ∗
       memRegion (sp - 368#64 - 1312#64) 1312 ∗
       (scalar_ptr ↦ₛ scalar_bs) ∗
       (fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes))
      (sepPost (fun st =>
        st.sp = sp - 368#64 ∧
        calleeSavedVRegs st = calleeSavedVRegs s1 ∧
        st.readReg64 (.gpr 29#5) = sp - 96#64 ∧
        st.readReg64 (.gpr 19#5) = out_ptr ∧
        BitVec.truncate 8 (st.readReg64 (.gpr 0#5)) = BitVec.ofNat 8 (k % 2) ∧
        x25519CliMultiLib.CodeLoaded x25519CliMpl st.mem)
        (∃∗ r0_end : List (BitVec 8), ∃∗ r1_end : List (BitVec 8),
          ((sp - 360#64) ↦ₛ u1_bs) ∗ ((sp - 320#64) ↦ₛ r0_end) ∗ ((sp - 240#64) ↦ₛ r1_end) ∗
          ((sp - 148#64) ↦₈ BitVec.ofNat 8 (k % 2)) ∗
          ((sp - 144#64) ↦₆₄ scalar_ptr) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
          ((sp - 128#64) ↦₆₄ 0#64) ∗ ((sp - 120#64) ↦₆₄ 0#64) ∗
          memRegion (sp - 368#64 - 1312#64) 1312 ∗
          (scalar_ptr ↦ₛ scalar_bs) ∗
          (fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes) ∗
          ⌜montProjBounded r0_end (2 ^ 52) ∧ montProjBounded r1_end (2 ^ 52) ∧
            montProjOfBytes (if BitVec.ofNat 8 (k % 2) == 1#8 then r1_end else r0_end) = res⌝)) := by
  intro exit_pc k
  wp_loop_measure 254
    (fun idx st =>
      idx ≤ 254 ∧
      st.sp = sp - 368#64 ∧
      calleeSavedVRegs st = calleeSavedVRegs s1 ∧
      st.readReg64 (.gpr 29#5) = sp - 96#64 ∧
      st.readReg64 (.gpr 19#5) = out_ptr ∧
      st.readReg64 (.gpr 21#5) = 0#64 ∧
      BitVec.truncate 8 (st.readReg64 (.gpr 0#5)) = BitVec.ofNat 8 ((k / 2 ^ idx) % 2) ∧
      x25519CliMultiLib.CodeLoaded x25519CliMpl st.mem)
    (fun idx _ =>
      ∃∗ r0_bs : List (BitVec 8), ∃∗ r1_bs : List (BitVec 8),
        ((sp - 360#64) ↦ₛ u1_bs) ∗ ((sp - 320#64) ↦ₛ r0_bs) ∗ ((sp - 240#64) ↦ₛ r1_bs) ∗
        ((sp - 148#64) ↦₈ BitVec.ofNat 8 ((k / 2 ^ idx) % 2)) ∗
        ((sp - 144#64) ↦₆₄ scalar_ptr) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 idx) ∗ ((sp - 120#64) ↦₆₄ 0#64) ∗
        memRegion (sp - 368#64 - 1312#64) 1312 ∗
        (scalar_ptr ↦ₛ scalar_bs) ∗
        (fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes) ∗
        ⌜montProjBounded r0_bs (2 ^ 52) ∧ montProjBounded r1_bs (2 ^ 52) ∧
          ∃ x0_c x1_c : MontProjPoint,
            (montProjOfBytes r0_bs, montProjOfBytes r1_bs) =
              (if ((k / 2 ^ idx) % 2) == 1 then (x1_c, x0_c) else (x0_c, x1_c)) ∧
            montLadderLoop idx k u1 x0_c x1_c = res⌝)
  case init =>
    refine Entails.sepExists_right r0_init (Entails.sepExists_right r1_init ?_)
    have hpure : montProjBounded r0_init (2 ^ 52) ∧ montProjBounded r1_init (2 ^ 52) ∧
        ∃ x0_c x1_c : MontProjPoint,
          (montProjOfBytes r0_init, montProjOfBytes r1_init) =
            (if ((k / 2 ^ 254) % 2) == 1 then (x1_c, x0_c) else (x0_c, x1_c)) ∧
          montLadderLoop 254 k u1 x0_c x1_c = res :=
      ⟨hr0_b1, hr1_b1, x0_init, x1_init, hr_pts1, hloop1⟩
    rw [pure_eq_true_of hpure, sepConj_pure_true]
    exact Entails.of_eq (by sep_ac_rfl)
  case base =>
    wp_pull_exists
    rename_i r0_end r1_end
    wp_focus_pure
    rintro ⟨hr0_b, hr1_b, x0_c, x1_c, hr_pts, hloop0⟩
    have hx0_eq : x0_c = res := hloop0
    have hsel : montProjOfBytes (if BitVec.ofNat 8 (k % 2) == 1#8 then r1_end else r0_end) = res := by
      rw [← hx0_eq]
      simp only [Nat.pow_zero, Nat.div_one] at hr_pts
      rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with hm | hm
      · simp only [hm, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at hr_pts
        have hc : (BitVec.ofNat 8 0 == 1#8) = false := rfl
        simp only [hm, hc, Bool.false_eq_true, ↓reduceIte]
        exact (Prod.mk.inj hr_pts).1
      · simp only [hm, BEq.rfl, ↓reduceIte] at hr_pts
        have hc : (BitVec.ofNat 8 1 == 1#8) = true := rfl
        simp only [hm, hc, ↓reduceIte]
        exact (Prod.mk.inj hr_pts).2
    wp_cut_codeLoaded
    wp_steps 3
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl_base
    refine SepWP.done
      (by conv => lhs; simp only [wp_norm, arm64_norm])
      (by wp_norm_lhs) ⟨?_, ?_⟩
    · simp only [Nat.pow_zero, Nat.div_one] at *
      refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, hcl_base⟩
      (conv => lhs; arg 2; simp only [wp_norm, arm64_norm])
      assumption
    · refine Entails.sepExists_right r0_end (Entails.sepExists_right r1_end ?_)
      simp only [Nat.pow_zero, Nat.div_one]
      have hpure : montProjBounded r0_end (2 ^ 52) ∧ montProjBounded r1_end (2 ^ 52) ∧
          montProjOfBytes (if BitVec.ofNat 8 (k % 2) == 1#8 then r1_end else r0_end) = res :=
        ⟨hr0_b, hr1_b, hsel⟩
      rw [pure_eq_true_of hpure, sepConj_pure_true]
      exact Entails.of_eq (by simp only [bv_lin_norm])
  case step =>
    right
    apply sepWP_have_state
      (fun st =>
        BitVec.truncate 8 (st.readReg64 (.gpr 0#5)) = BitVec.ofNat 8 ((k / 2 ^ (m' + 1)) % 2) ∧
        calleeSavedVRegs st = calleeSavedVRegs s1)
      ⟨by assumption, by assumption⟩
    rintro ⟨hw0_step, hvregs_step⟩
    wp_pull_exists
    rename_i r0_bs r1_bs
    wp_focus_pure
    rintro ⟨hr0_b, hr1_b, x0_c, x1_c, hr_pts, hloop_m⟩
    have hm_le : m' ≤ 253 := ‹m' ≤ 253›
    have hcmp1 : (BitVec.ule (BitVec.ofNat 64 (m' + 1)) 0#64) = false := by
      simp [BitVec.ule]; omega
    have hsub1 : BitVec.ofNat 64 (m' + 1) - 1#64 = BitVec.ofNat 64 m' := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    have hsub1' : BitVec.ofNat 64 (m' + 1) + 0xffffffffffffffff#64 = BitVec.ofNat 64 m' := by
      rw [← hsub1]; bv_lin
    have hcmp2 : (BitVec.ule 257#64 (BitVec.ofNat 64 (m' + 1))) = false := by
      simp [BitVec.ule]; omega
    have hlsr3 : (BitVec.ofNat 64 m' >>> 3) = BitVec.ofNat 64 (m' / 8) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (by omega : m' < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m' / 8 < 2 ^ 64)]
    have hand7 : (BitVec.ofNat 64 m' &&& 7#64) = BitVec.ofNat 64 (m' % 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
          BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : m' < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m' % 8 < 2 ^ 64)]
    have hdiv8_lt : (BitVec.ofNat 64 (m' / 8)).toNat < 32 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m' / 8 < 2 ^ 64)]; omega
    wp_cut_codeLoaded
    wp_steps 14
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl_step
    wp_conv_pre => try rw [show sp - 1680#64 = sp - 368#64 - 1312#64 by bv_lin]
    refine Eq.mp (congrArg (fun Q => SepWP _ _ _ Q _ _) ?_)
      (mont_ladder_step hbb hdadd b sp out_ptr u1_bs r0_bs r1_bs
        (BitVec.ofNat 8 ((k / 2 ^ (m' + 1)) % 2))
        m' k u1 ((k / 2 ^ (m' + 1)) % 2) ((k / 2 ^ m') % 2) x0_c x1_c
        (P := ((sp - 144#64) ↦₆₄ scalar_ptr) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
              ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 m') ∗ ((sp - 120#64) ↦₆₄ 0#64) ∗
              (scalar_ptr ↦ₛ scalar_bs))
        hb hbase (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) h_sp_align
        (by conv => lhs; simp only [wp_norm, arm64_norm])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by
          (conv => lhs; arg 2; simp only [wp_norm, arm64_norm])
          try simp only [hsub1, hsub1', hlsr3, hand7, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : m' / 8 < 2 ^ 64)]
          rw [scalar_bit_u64_eq scalar_bs m']
          exact truncate8_zext64 _)
        (by
          (conv => lhs; simp only [wp_norm, arm64_norm])
          try simp only [hsub1, hsub1', hlsr3, hand7, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : m' / 8 < 2 ^ 64)]
          exact scalar_bit_u64_eq scalar_bs m')
        (by
          (conv => lhs; arg 2; simp only [wp_norm, arm64_norm])
          exact hw0_step)
        hcl_step (by omega) rfl hu1_b hu1_v hr0_b hr1_b hr_pts ?_)
    · simp only [bv_lin_norm]; sep_ac_rfl
    · intro s' r0_out r1_out x0' x1' hpc' hrun' hsp' hvregs' hx29' hx19' hx21' hw0' hcl' hr0_out hr1_out hpts' hstep_eq
      refine SepWP.done hpc' hrun' ⟨⟨by omega, hsp', hvregs'.trans hvregs_step, hx29', hx19', hx21', hw0', hcl'⟩, ?_⟩
      refine Entails.sepExists_right r0_out (Entails.sepExists_right r1_out ?_)
      have hpure : montProjBounded r0_out (2 ^ 52) ∧ montProjBounded r1_out (2 ^ 52) ∧
          ∃ x0_n x1_n : MontProjPoint,
            (montProjOfBytes r0_out, montProjOfBytes r1_out) =
              (if ((k / 2 ^ m') % 2) == 1 then (x1_n, x0_n) else (x0_n, x1_n)) ∧
            montLadderLoop m' k u1 x0_n x1_n = res :=
        ⟨hr0_out, hr1_out, x0', x1', hpts', hstep_eq.symm.trans hloop_m⟩
      rw [pure_eq_true_of hpure, sepConj_pure_true]
      exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 600000 in
private theorem mont_post_loop_cselect_affine [X25519CliPlacement]
    (hbb : BlackBoxU8Ok) (haff : MontProjectiveAsAffineOk)
    (b sp out_ptr : BitVec 64)
    (out_bs r0_end r1_end : List (BitVec 8))
    (prev_end b0 : BitVec 8) (res : MontProjPoint)
    (vregs0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    {target_pc : BitVec 64} {s0 : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (_hb : X25519Base x25519CliPl15 b) (hbase : x25519CliPl15.base = b)
    (hpc : s0.pc = b + 576#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp - 368#64)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s0 = vregs0)
    (hx29 : s0.readReg64 (.gpr 29#5) = sp - 96#64)
    (hx19 : s0.readReg64 (.gpr 19#5) = out_ptr)
    (hw0 : BitVec.truncate 8 (s0.readReg64 (.gpr 0#5)) = b0)
    (hcl : x25519CliMultiLib.CodeLoaded x25519CliMpl s0.mem)
    (hb0_or : b0 = 0#8 ∨ b0 = 1#8)
    (hout_len : out_bs.length = 32)
    (hr0_eb : montProjBounded r0_end (2 ^ 52))
    (hr1_eb : montProjBounded r1_end (2 ^ 52))
    (hsel_res : montProjOfBytes (if b0 == 1#8 then r1_end else r0_end) = res)
    (hnext : ∀ (sf : State) (r_sel : List (BitVec 8)),
      sf.pc = b + 792#64 →
      sf.status = .Running →
      sf.sp = sp - 368#64 →
      calleeSavedVRegs sf = vregs0 →
      x25519CliMultiLib.CodeLoaded x25519CliMpl sf.mem →
      r_sel.length = 80 →
      SepWP (x25519CliPC15.rebase b (fun _ => none)) target_pc sf
        ((out_ptr ↦ₛ natToLeBytes 32 (fpMul res.U (fpInv res.W))) ∗
         ((sp - 320#64) ↦ₛ r_sel) ∗
         ((sp - 240#64) ↦ₛ r1_end) ∗
         ((sp - 148#64) ↦₈ 0#8) ∗
         memRegion (sp - 368#64 - 1312#64) 1312 ∗
         (fe51_one x25519CliMpl ↦ᵣ fe51OneBytes) ∗ P) post oom) :
    SepWP (x25519CliPC15.rebase b (fun _ => none)) target_pc s0
      ((out_ptr ↦ₛ out_bs) ∗
       ((sp - 320#64) ↦ₛ r0_end) ∗
       ((sp - 240#64) ↦ₛ r1_end) ∗
       ((sp - 148#64) ↦₈ prev_end) ∗
       memRegion (sp - 368#64 - 1312#64) 1312 ∗
       (fe51_one x25519CliMpl ↦ᵣ fe51OneBytes) ∗ P) post oom := by
  apply sepWP_callee_shrink (sp - 368#64) 1312 16 1296
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hbb
  rw [hsp, hvregs, hx29, hx19] at *
  norm_sf 16
  wp_conv_pre => try rw [show sp - 384#64 = sp - 368#64 - 16#64 by bv_lin]
  apply sepWP_callee_grow (sp - 368#64) 1312 16 1296
  apply sepWP_have_state
    (fun st => (st.readReg64 (.gpr 0#5) &&& 255#64) = BitVec.zeroExtend 64 b0)
    (by
      apply u8_ret_and_255
      simp only [BitVec.truncate_eq_setWidth] at *
      assumption)
  intro hzext_b0
  have hr0_elen : r0_end.length = 80 := hr0_eb.1
  have hr1_elen : r1_end.length = 80 := hr1_eb.1
  wp_conv_pre =>
    rw [pointsToBytes80_sub320_eq sp r0_end hr0_elen,
        pointsToBytes80_sub240_eq sp r1_end hr1_elen]
  wp_cut_codeLoaded
  wp_sym_steps 49
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_sel
  have hrsel_len : (if b0 == 1#8 then r1_end else r0_end).length = 80 := by
    cases (b0 == 1#8) <;> assumption
  wp_conv_pre =>
    simp only [hzext_b0, cselect_word _ _ b0 hb0_or,
               cselect_word_neg _ _ b0 hb0_or, cselect_word_neg_add _ _ b0 hb0_or,
               cswap_readLE_if]
  clear hzext_b0
  apply sepWP_replace_sub _ _ (pointsToBytes80_sub320_eq sp (if b0 == 1#8 then r1_end else r0_end) hrsel_len).symm
  apply sepWP_replace_sub _ _ (pointsToBytes80_sub240_eq sp r1_end hr1_elen).symm
  have hrsel_b54 : montProjBounded (if b0 == 1#8 then r1_end else r0_end) (2 ^ 54) := by
    have h0' : montProjBounded r0_end (2 ^ 54) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨c0,c1,c2,c3,c4⟩⟩ := hr0_eb
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    have h1' : montProjBounded r1_end (2 ^ 54) := by
      obtain ⟨hl, ⟨a0,a1,a2,a3,a4⟩, ⟨c0,c1,c2,c3,c4⟩⟩ := hr1_eb
      exact ⟨hl, ⟨by omega,by omega,by omega,by omega,by omega⟩, ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    cases (b0 == 1#8) <;> assumption
  obtain ⟨_, ⟨hs0,hs1,hs2,hs3,hs4⟩, ⟨hs5,hs6,hs7,hs8,hs9⟩⟩ := hrsel_b54
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call haff
  clean_prev_sf; norm_sf 1312
  wp_conv_pre => rw [hsel_res]
  refine Eq.mp (congrArg (fun Q => SepWP _ target_pc _ Q post oom) ?_)
    (hnext _ (if b0 == 1#8 then r1_end else r0_end)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by exact ‹calleeSavedVRegs _ = vregs0›)
      (by assumption)
      hrsel_len)
  sep_ac_rfl

public section

/-! ## 5. Exported Subroutine Contracts (`Blk04`, `Blk15`) -/

/-- `Rev::nth` (`Blk04`, 41 words, stack 16) at `n = 1#64`: advances `[0, 256)` reverse bit
    iterator to `254` and returns bit `254` of `scalar_bs`. -/
theorem rev_nth_bit254_ok : RevNthBit254Ok := by
  intro _
  apply x25519Leaf_ok x25519CliPC04 x25519CliPl04
  intro b _hb _hbase
  wp_init
  subst ‹a = 1#64›
  open_cells (s0.sp - 16#64) 16 2
  wp_steps
  close_cells (s0.sp - 16#64) 16 2
  have hret : BitVec.truncate 8 (((BitVec.zeroExtend 32 (a_rest.getD 31 0#8)) >>> 6#32) &&& 1#32) =
      BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2) := by
    have h254 := scalar_bit_u32_eq a_rest 254
    simp only [show 254 / 8 = 31 from rfl, show BitVec.ofNat 32 (254 % 8) = 6#32 from rfl] at h254
    rw [h254]
    rcases (show (leBytesToNat a_rest / 2 ^ 254) % 2 = 0 ∨ (leBytesToNat a_rest / 2 ^ 254) % 2 = 1 by omega) with h0 | h0 <;>
      rw [h0] <;> rfl
  wp_done

set_option maxHeartbeats 800000 in
/-- `<&MontgomeryPoint as Mul<&Scalar>>::mul` (`Blk15`, 211 words, stack 1680). -/
theorem montgomery_point_mul_ok_of
    (hrev : RevNthBit254Ok) (hbb : BlackBoxU8Ok)
    (hdadd : MontDiffAddAndDoubleOk) (haff : MontProjectiveAsAffineOk) :
    MontgomeryPointMulOk := by
  intro _
  apply x25519Caller_ok x25519CliPC15 x25519CliPl15
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 32 := ‹a_3.length = 32›
  have hself_len : a_4.length = 32 := ‹a_4.length = 32›
  have hsc_len : a_rest.length = 32 := ‹a_rest.length = 32›
  have hone_cells : (fe51_one x25519CliMpl ↦ᵣ fe51OneBytes) =
      ((fe51_one x25519CliMpl ↦₆₄ᵣ 1#64) ∗
       ((fe51_one x25519CliMpl + 8#64) ↦₆₄ᵣ 0#64) ∗
       ((fe51_one x25519CliMpl + 16#64) ↦₆₄ᵣ 0#64) ∗
       ((fe51_one x25519CliMpl + 24#64) ↦₆₄ᵣ 0#64) ∗
       ((fe51_one x25519CliMpl + 32#64) ↦₆₄ᵣ 0#64)) := by
    rw [pointsToBytesRO40_eq_cells _ fe51OneBytes fe51OneBytes_length,
        fe51One_readLE_0, fe51One_readLE_8, fe51One_readLE_16, fe51One_readLE_24, fe51One_readLE_32]
  apply sepWP_split_stack_callee 1312 368
  apply sepWP_peel_stack_region s0.sp 368 8 360
  apply sepWP_peel_stack_region s0.sp 360 40 320
  apply sepWP_peel_stack_region s0.sp 320 80 240
  apply sepWP_peel_stack_region s0.sp 240 80 160
  apply sepWP_peel_stack_region s0.sp 160 12 148
  apply sepWP_peel_byte s0.sp 148 147; intro prev_init
  apply sepWP_peel_stack_region s0.sp 147 3 144
  apply sepWP_peel_stack_region s0.sp 144 32 112
  apply sepWP_peel_stack_region s0.sp 112 16 96
  open_cells (s0.sp - 360#64) 40 5
  open_cells (s0.sp - 320#64) 80 10
  open_cells (s0.sp - 240#64) 80 10
  open_cells (s0.sp - 144#64) 32 4
  open_cells (s0.sp - 96#64) 96 12
  wp_conv_pre => rw [hone_cells]
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_init
  obtain ⟨hl0_b, hl1_b, hl2_b, hl3_b, hl4_b, hdec_val⟩ := fe51_decodeU255_val a_4 hself_len
  let l0 := ByteSlice.readLE a_4 0 8 &&& 2251799813685247#64
  let l1 := (ByteSlice.readLE a_4 6 8 >>> 3) &&& 2251799813685247#64
  let l2 := (ByteSlice.readLE a_4 12 8 >>> 6) &&& 2251799813685247#64
  let l3 := (ByteSlice.readLE a_4 19 8 >>> 1) &&& 2251799813685247#64
  let l4 := (ByteSlice.readLE a_4 24 8 >>> 12) &&& 2251799813685247#64
  apply sepWP_replace_sub _ _ hone_cells.symm
  apply sepWP_replace_sub _ _ (packFe51_sub_eq s0.sp 360#64 352#64 344#64 336#64 328#64 l0 l1 l2 l3 l4).symm
  apply sepWP_replace_sub _ _ (packProj80_sub_eq s0.sp 320#64 312#64 304#64 296#64 288#64 280#64 272#64 264#64 256#64 248#64
      1#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64).symm
  apply sepWP_replace_sub _ _ (packProj80_sub_eq s0.sp 240#64 232#64 224#64 216#64 208#64 200#64 192#64 184#64 176#64 168#64
      l0 l1 l2 l3 l4 1#64 0#64 0#64 0#64 0#64).symm
  let r1_0 := packFe51Bytes l0 l1 l2 l3 l4 ++ packFe51Bytes 1#64 0#64 0#64 0#64 0#64
  let r0_0 := packFe51Bytes 1#64 0#64 0#64 0#64 0#64 ++ packFe51Bytes 0#64 0#64 0#64 0#64 0#64
  let u1_bs := packFe51Bytes l0 l1 l2 l3 l4
  clear hone_cells
  wp_conv_pre =>
    try rw [show s0.sp - 136#64 = (s0.sp - 144#64) + 8#64 by bv_lin,
            show s0.sp - 128#64 = (s0.sp - 144#64) + 16#64 by bv_lin,
            show s0.sp - 1680#64 = s0.sp - 368#64 - 1312#64 by bv_lin]
  apply sepWP_callee_shrink (s0.sp - 368#64) 1312 16 1296
  wp_x25519_call hrev
  norm_sf 16
  apply sepWP_callee_grow (s0.sp - 368#64) 1312 16 1296
  have hb254_lt : (BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2)).toNat < 2 := by
    rw [BitVec.toNat_ofNat]; omega
  apply sepWP_have_state
    (fun st =>
      calleeSavedVRegs st = calleeSavedVRegs s0 ∧
      (BitVec.truncate 32 (st.readReg64 (.gpr 0#5)) &&& 255#32).toNat < 2 ∧
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (st.readReg64 (.gpr 0#5))) &&& 255#64).toNat < 2 ∧
      ((BitVec.truncate 32 (st.readReg64 (.gpr 0#5)) &&& 255#32) == 2#32) = false ∧
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (st.readReg64 (.gpr 0#5))) &&& 255#64) =
        BitVec.zeroExtend 64 (BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2)) ∧
      BitVec.zeroExtend 64 (BitVec.truncate 32 (st.readReg64 (.gpr 0#5)) &&& 255#32) =
        BitVec.zeroExtend 64 (BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2)) ∧
      BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (st.readReg64 (.gpr 0#5))) &&& 255#64) =
        BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2) ∧
      BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (st.readReg64 (.gpr 0#5)) &&& 255#32)) =
        BitVec.ofNat 8 ((leBytesToNat a_rest / 2 ^ 254) % 2))
    ⟨by assumption,
     by
       apply nth_ret_props ?_ hb254_lt
       simp only [BitVec.truncate_eq_setWidth] at *
       assumption⟩
  rintro ⟨hvregs_nth, _hret_lt1, _hret_lt2, _hret_ne2, _hret64, _hret64', _hret8, _hret8'⟩
  wp_cut_codeLoaded
  wp_steps 7
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_pre254
  have hu1_b54 : fe51LimbsBounded u1_bs (2 ^ 54) :=
    fe51LimbsBounded_packFe51Bytes l0 l1 l2 l3 l4 (2 ^ 54)
      (Nat.lt_trans hl0_b (by decide)) (Nat.lt_trans hl1_b (by decide))
      (Nat.lt_trans hl2_b (by decide)) (Nat.lt_trans hl3_b (by decide))
      (Nat.lt_trans hl4_b (by decide))
  have hu1_val : fe51ValOfBytes u1_bs % p25519 = decodeU255 a_4 % p25519 := by
    rw [fe51ValOfBytes_packFe51Bytes, hdec_val]
  obtain ⟨hr0_b52, hr0_val⟩ := packProj80_props 1#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 (2 ^ 52)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hr1_b52, hr1_val⟩ := packProj80_props l0 l1 l2 l3 l4 1#64 0#64 0#64 0#64 0#64 (2 ^ 52)
    hl0_b hl1_b hl2_b hl3_b hl4_b (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr_init_pts : (montProjOfBytes r0_0, montProjOfBytes r1_0) =
      (if (0 : Nat) == 1 then (⟨decodeU255 a_4 % p25519, 1⟩, ⟨1, 0⟩) else (⟨1, 0⟩, ⟨decodeU255 a_4 % p25519, 1⟩)) := by
    rw [hr0_val, hr1_val, hdec_val]
    have h1 : fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519 = 1 := by decide +kernel
    have h0 : fe51Val 0#64 0#64 0#64 0#64 0#64 % p25519 = 0 := by decide +kernel
    rw [h1, h0]; rfl
  let k := leBytesToNat a_rest
  let u1 := decodeU255 a_4 % p25519
  generalize hres_def : montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩ = res
  refine sepWP_focus_for_step
    (A := (s0.sp - 360#64) ↦ₛ u1_bs)
    (B := (s0.sp - 320#64) ↦ₛ r0_0)
    (C := (s0.sp - 240#64) ↦ₛ r1_0)
    (D := (s0.sp - 148#64) ↦₈ prev_init)
    (E := memRegion (s0.sp - 368#64 - 1312#64) 1312)
    (F := fe51_mont_a24 x25519CliMpl ↦ᵣ fe51MontA24Bytes)
    (by dsimp only [u1_bs, r0_0, r1_0]; sep_frame)
    (mont_ladder_step hbb hdadd b s0.sp a_1 u1_bs r0_0 r1_0 prev_init
      254 k u1 0 ((k / 2 ^ 254) % 2) ⟨1, 0⟩ ⟨u1, 1⟩
      hb hbase (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
      (by conv => lhs; simp only [wp_norm, arm64_norm, isCalleeSavedVReg, Bool.cond_false])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by
        (conv => lhs; arg 2; simp only [wp_norm, arm64_norm])
        (conv => rhs; dsimp only [k]; simp only [Nat.reducePow])
        exact truncate8_zext64 _)
      (by
        (conv => lhs; simp only [wp_norm, arm64_norm])
        (conv => rhs; dsimp only [k]; simp only [Nat.reducePow]))
      (by (conv => lhs; arg 2; simp only [wp_norm, arm64_norm]); decide)
      hcl_pre254 (by decide) rfl
      hu1_b54 hu1_val hr0_b52 hr1_b52 hr_init_pts ?_)
  intro s1 r0_1 r1_1 x0_1 x1_1 hpc1 hrun1 hsp1 hvregs1 hx29_1 hx19_1 hx21_1 hw0_1 hcl1 hr0_1 hr1_1 hpts1 hstep1
  have hvregs_s1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs_nth
  clear hvregs1 hvregs_nth hcl_pre254 _hret_lt1 _hret_lt2 _hret_ne2 _hret64 _hret64' _hret8 _hret8'
  clean_prev_sf
  have hloop := mont_ladder_loop hbb hdadd b s0.sp a_1 a_2 u1_bs a_rest r0_1 r1_1 u1 x0_1 x1_1 res
    hb hbase hpc1 hrun1 hsp1 hsp_align hx29_1 hx19_1 hx21_1 hw0_1 hcl1
    hsc_len hu1_b54 hu1_val hr0_1 hr1_1 hpts1 (hstep1.symm.trans hres_def)
  wp_conv_pre => dsimp only [k]
  dsimp only [k] at hloop
  refine SepWP.bind_sepPost hloop (by sep_frame) ?_
  rintro s_exit hpc_e hrun_e ⟨hsp_e, hvregs_e, hx29_e, hx19_e, hw0_e, hcl_e⟩
  have hvregs_exit : calleeSavedVRegs s_exit = calleeSavedVRegs s0 := hvregs_e.trans hvregs_s1
  clear hloop hpc1 hrun1 hsp1 hvregs_s1 hvregs_e hx29_1 hx19_1 hx21_1 hw0_1 hcl1 hr0_1 hr1_1 hpts1 hstep1 r0_1 r1_1 x0_1 x1_1 s1
  wp_pull_exists
  rename_i r0_end r1_end
  wp_focus_pure
  rintro ⟨hr0_eb, hr1_eb, hsel_res⟩
  have hb0_or : BitVec.ofNat 8 (leBytesToNat a_rest % 2) = 0#8 ∨
      BitVec.ofNat 8 (leBytesToNat a_rest % 2) = 1#8 := by
    rcases (show leBytesToNat a_rest % 2 = 0 ∨ leBytesToNat a_rest % 2 = 1 by omega) with hm | hm <;> simp [hm]
  have hr1_elen : r1_end.length = 80 := hr1_eb.1
  wp_conv_pre => try rw [show s0.sp - 1680#64 = s0.sp - 368#64 - 1312#64 by bv_lin]
  refine sepWP_focus_for_step
    (A := _ ↦ₛ a_3)
    (B := (s0.sp - 320#64) ↦ₛ r0_end)
    (C := (s0.sp - 240#64) ↦ₛ r1_end)
    (D := (s0.sp - 148#64) ↦₈ BitVec.ofNat 8 (leBytesToNat a_rest % 2))
    (E := memRegion (s0.sp - 368#64 - 1312#64) 1312)
    (F := fe51_one x25519CliMpl ↦ᵣ fe51OneBytes)
    (by sep_frame)
    (mont_post_loop_cselect_affine hbb haff b s0.sp _ a_3 r0_end r1_end
      (BitVec.ofNat 8 (leBytesToNat a_rest % 2))
      (BitVec.ofNat 8 (leBytesToNat a_rest % 2)) res (calleeSavedVRegs s0)
      hb hbase hpc_e hrun_e hsp_e hsp_align hvregs_exit hx29_e hx19_e hw0_e hcl_e hb0_or
      hout_len hr0_eb hr1_eb hsel_res ?_)
  intro sf_end r_sel hpc_f hrun_f hsp_f hvregs_f hcl_f hrsel_len
  clear hpc_e hrun_e hsp_e hvregs_exit hx29_e hx19_e hw0_e hcl_e hb0_or hr0_eb hr1_eb hsel_res s_exit
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_ret
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_region s0.sp 112 16 96
  close_cells (s0.sp - 144#64) 32 4
  apply sepWP_unpeel_stack_region s0.sp 144 32 112
  apply sepWP_unpeel_stack_region s0.sp 147 3 144
  apply sepWP_unpeel_byte s0.sp 148 147
  apply sepWP_unpeel_stack_region s0.sp 160 12 148
  apply sepWP_unpeel_stack_bytes s0.sp 240 80 160 (hbs := hr1_elen)
  apply sepWP_unpeel_stack_bytes s0.sp 320 80 240 (hbs := hrsel_len)
  apply sepWP_unpeel_stack_bytes s0.sp 360 40 320 (hbs := hu1_b54.1)
  apply sepWP_unpeel_stack_region s0.sp 368 8 360
  wp_conv_pre => try rw [show s0.sp - 1680#64 = s0.sp - 368#64 - 1312#64 by bv_lin]
  apply sepWP_merge_stack_callee 1312 368
  clear hu1_val hr0_val hr1_val hr_init_pts hdec_val hres_def
  generalize natToLeBytes 32 (fpMul res.U (fpInv res.W)) = out_res
  wp_done

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode
