/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `CompressedEdwardsY::decompress` Proof

Machine-code proof in `dalekCliMultiLib` for `CompressedEdwardsY::decompress`
(`compressed_edwards_y_decompress_ok_of`).
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress3

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded sqrtRatioM1
  Fe51MulOk Fe51MulRoRightOk Fe51Pow2kOk Fe51SqrtRatioIOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes fpPow_two_eq_fpSq
  CompressedEdwardsYDecompressOk)
open VerifiedLibraries.Common (
  p25519 edD sqrtM1 fpAdd fpSub fpMul fpNeg fpSq fpPow
  EdExtPoint edExtOfAffine recoverXEven decodeEdDalek leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes fe51EdwardsDBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (
  black_box_u8_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe write64_length_eq readLE_write64_self' readLE_write64_ne
  fe51Reduce_bounded fe51Reduce_val_mod fe51Sub_val_mod fe51Neg_val_mod
  pointsToBytes40_eq_cells sepWP_norm_stackFrame
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_shrink sepWP_callee_grow sepWP_abstract_bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  bv64_and_mask51_toNat fe51LimbsBounded_of_52
  pointsToBytes40_sub_eq_cells pointsToBytes168_split
  fe51EdwardsDBytes_bounded sepWP_peel_stack_region sepWP_unpeel_stack_region)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 05 dalekCliMultiLib DalekCliPlacement 176 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl05_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl05.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

private theorem bv64_toNat_bytes (v : BitVec 64) :
    v.toNat = (v.extractLsb' 0 8).toNat + (v.extractLsb' 8 8).toNat * 256 +
      (v.extractLsb' 16 8).toNat * 65536 + (v.extractLsb' 24 8).toNat * 16777216 +
      (v.extractLsb' 32 8).toNat * 4294967296 + (v.extractLsb' 40 8).toNat * 1099511627776 +
      (v.extractLsb' 48 8).toNat * 281474976710656 + (v.extractLsb' 56 8).toNat * 72057594037927936 := by
  have h (k : Nat) : (v.extractLsb' k 8).toNat = (v.toNat / 2 ^ k) % 256 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [h 0, h 8, h 16, h 24, h 32, h 40, h 48, h 56]
  have := v.isLt
  omega

private theorem pack64_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
      b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
      b6.toNat * 281474976710656 + b7.toNat * 72057594037927936 := by
  have h := unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  simp only [unpack64, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hv := bv64_toNat_bytes (pack64 b0 b1 b2 b3 b4 b5 b6 b7)
  unfold pack64 at hv
  rw [h0, h1, h2, h3, h4, h5, h6, h7] at hv
  exact hv

private theorem leBytesToNat_take_succ (bs : List (BitVec 8)) :
    ∀ k, k < bs.length →
      leBytesToNat (bs.take (k + 1)) = leBytesToNat (bs.take k) + (bs.getD k 0#8).toNat * 256 ^ k
  | 0, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · simp [leBytesToNat]
  | k + 1, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · have ih := leBytesToNat_take_succ bs k (by simpa using hk)
      simp only [List.take_succ_cons, leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
      rw [ih, Nat.pow_succ, ← Nat.mul_assoc]
      omega

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
  rw [h0]
  omega

private theorem fe51_from_bytes_val (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    let l0 := ByteSlice.readLE bs 0 8 &&& 2251799813685247#64
    let l1 := (ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64
    let l2 := (ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64
    let l3 := (ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64
    let l4 := (ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64
    l0.toNat < 2 ^ 52 ∧ l1.toNat < 2 ^ 52 ∧ l2.toNat < 2 ^ 52 ∧ l3.toNat < 2 ^ 52 ∧ l4.toNat < 2 ^ 52 ∧
    fe51Val l0 l1 l2 l3 l4 = leBytesToNat bs % (2 ^ 255) ∧
    (leBytesToNat bs / 2 ^ 255) % 2 = ((bs.getD 31 0#8) >>> 7).toNat := by
  intro l0 l1 l2 l3 l4
  have hle32 := leBytesToNat_32 bs hbs
  have hl0 : l0.toNat = (pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
      (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)).toNat % 2 ^ 51 := by
    dsimp only [l0]; rw [bv64_and_mask51_toNat, ← ByteSlice.pack64_eq_readLE_8 bs 0]
  have hl1 : l1.toNat = ((pack64 (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8)
      (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8)).toNat / 8) % 2 ^ 51 := by
    dsimp only [l1]; rw [bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 6]
  have hl2 : l2.toNat = ((pack64 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8)
      (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)).toNat / 64) % 2 ^ 51 := by
    dsimp only [l2]; rw [bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 12]
  have hl3 : l3.toNat = ((pack64 (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8)
      (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)).toNat / 2) % 2 ^ 51 := by
    dsimp only [l3]; rw [bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 19]
  have hl4 : l4.toNat = ((pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
      (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8)).toNat / 4096) % 2 ^ 51 := by
    dsimp only [l4]; rw [bv64_and_mask51_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← ByteSlice.pack64_eq_readLE_8 bs 24]
  rw [pack64_toNat] at hl0 hl1 hl2 hl3 hl4
  have hb31 : ((bs.getD 31 0#8) >>> 7).toNat = (bs.getD 31 0#8).toNat / 128 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (bs.getD 0 0#8).isLt; have := (bs.getD 1 0#8).isLt; have := (bs.getD 2 0#8).isLt; have := (bs.getD 3 0#8).isLt
  have := (bs.getD 4 0#8).isLt; have := (bs.getD 5 0#8).isLt; have := (bs.getD 6 0#8).isLt; have := (bs.getD 7 0#8).isLt
  have := (bs.getD 8 0#8).isLt; have := (bs.getD 9 0#8).isLt; have := (bs.getD 10 0#8).isLt; have := (bs.getD 11 0#8).isLt
  have := (bs.getD 12 0#8).isLt; have := (bs.getD 13 0#8).isLt; have := (bs.getD 14 0#8).isLt; have := (bs.getD 15 0#8).isLt
  have := (bs.getD 16 0#8).isLt; have := (bs.getD 17 0#8).isLt; have := (bs.getD 18 0#8).isLt; have := (bs.getD 19 0#8).isLt
  have := (bs.getD 20 0#8).isLt; have := (bs.getD 21 0#8).isLt; have := (bs.getD 22 0#8).isLt; have := (bs.getD 23 0#8).isLt
  have := (bs.getD 24 0#8).isLt; have := (bs.getD 25 0#8).isLt; have := (bs.getD 26 0#8).isLt; have := (bs.getD 27 0#8).isLt
  have := (bs.getD 28 0#8).isLt; have := (bs.getD 29 0#8).isLt; have := (bs.getD 30 0#8).isLt; have := (bs.getD 31 0#8).isLt
  unfold fe51Val
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;> omega

private theorem fe51_from_bytes_post (dst bs : List (BitVec 8))
    (hdst : dst.length = 40) (hbs : bs.length = 32) :
    let l0 := ByteSlice.readLE bs 0 8 &&& 2251799813685247#64
    let l1 := (ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64
    let l2 := (ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64
    let l3 := (ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64
    let l4 := (ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 0 l0) 8 l1) 16 l2) 24 l3) 32 l4
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 52) ∧ fe51LimbsBounded res (2 ^ 54) ∧
    fe51ValOfBytes res = leBytesToNat bs % (2 ^ 255) ∧
    (leBytesToNat bs / 2 ^ 255) % 2 = ((bs.getD 31 0#8) >>> 7).toNat := by
  intro l0 l1 l2 l3 l4 res
  haveI : HasLenGe dst 40 := ⟨by omega⟩
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hval, hsign⟩ := fe51_from_bytes_val bs hbs
  have hlen : res.length = 40 := by
    dsimp only [res]; simp only [write64_length_eq, hdst]; decide
  have hb52 : fe51LimbsBounded res (2 ^ 52) := by
    unfold fe51LimbsBounded
    refine ⟨hlen, ?_⟩
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    exact ⟨hb0, hb1, hb2, hb3, hb4⟩
  have hb54 : fe51LimbsBounded res (2 ^ 54) := by
    obtain ⟨hl, h0, h1, h2, h3, h4⟩ := hb52
    exact ⟨hl, by omega, by omega, by omega, by omega, by omega⟩
  have hv : fe51ValOfBytes res = leBytesToNat bs % (2 ^ 255) := by
    unfold fe51ValOfBytes
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    exact hval
  exact ⟨hlen, hb52, hb54, hv, hsign⟩

private theorem sub1_bias0_eq (l : BitVec 64) :
    l + 36028797018963663#64 = (l - 1#64) + 36028797018963664#64 := by bv_bits

private theorem sub0_bias1_eq (l : BitVec 64) :
    l + 36028797018963952#64 = (l - 0#64) + 36028797018963952#64 := by bv_bits

private theorem fe51_sub1_reduce_post (dst y2_bs : List (BitVec 8))
    (hdst : dst.length = 40) (hy2 : fe51LimbsBounded y2_bs (2 ^ 52)) :
    let l0 := ByteSlice.readLE y2_bs 0 8
    let l1 := ByteSlice.readLE y2_bs 8 8
    let l2 := ByteSlice.readLE y2_bs 16 8
    let l3 := ByteSlice.readLE y2_bs 24 8
    let l4 := ByteSlice.readLE y2_bs 32 8
    let d0 := l0 + 36028797018963663#64
    let d1 := l1 + 36028797018963952#64
    let d2 := l2 + 36028797018963952#64
    let d3 := l3 + 36028797018963952#64
    let d4 := l4 + 36028797018963952#64
    let r0 := (d0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64
    let r1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
    let r2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
    let r3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
    let r4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 16 r2) 24 r3) 0 r0) 8 r1) 32 r4
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 54) ∧
    fe51ValOfBytes res % p25519 = fpSub (fe51ValOfBytes y2_bs % p25519) 1 := by
  intro l0 l1 l2 l3 l4 d0 d1 d2 d3 d4 r0 r1 r2 r3 r4 res
  haveI : HasLenGe dst 40 := ⟨by omega⟩
  have hlen : res.length = 40 := by
    dsimp only [res]; simp only [write64_length_eq, hdst]; decide
  obtain ⟨hrb0, hrb1, hrb2, hrb3, hrb4⟩ := fe51Reduce_bounded d0 d1 d2 d3 d4
  have hb54 : fe51LimbsBounded res (2 ^ 54) := by
    unfold fe51LimbsBounded
    refine ⟨hlen, ?_⟩
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    dsimp only [r0, r1, r2, r3, r4]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨_, hy0, hy1, hy2', hy3, hy4⟩ := hy2
  have hl_b54 : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧ l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54 := by
    dsimp only [l0, l1, l2, l3, l4]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hsub := fe51Sub_val_mod l0 l1 l2 l3 l4 1#64 0#64 0#64 0#64 0#64 hl_b54
    (B2 := 2 ^ 54) ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hval1 : fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519 = 1 := by decide
  have hv : fe51ValOfBytes res % p25519 = fpSub (fe51ValOfBytes y2_bs % p25519) 1 := by
    unfold fe51ValOfBytes
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    change fe51Val r0 r1 r2 r3 r4 % p25519 = _
    rw [fe51Reduce_val_mod d0 d1 d2 d3 d4]
    dsimp only [d0, d1, d2, d3, d4]
    rw [sub1_bias0_eq l0, sub0_bias1_eq l1, sub0_bias1_eq l2, sub0_bias1_eq l3, sub0_bias1_eq l4, hsub, hval1]
  exact ⟨hlen, hb54, hv⟩

private theorem fe51_add1_post (dst dy2_bs : List (BitVec 8))
    (hdst : dst.length = 40) (hdy2 : fe51LimbsBounded dy2_bs (2 ^ 52)) :
    let l0 := ByteSlice.readLE dy2_bs 0 8
    let l1 := ByteSlice.readLE dy2_bs 8 8
    let l2 := ByteSlice.readLE dy2_bs 16 8
    let l3 := ByteSlice.readLE dy2_bs 24 8
    let l4 := ByteSlice.readLE dy2_bs 32 8
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 8 l1) 16 l2) 0 (l0 + 1#64)) 24 l3) 32 l4
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 54) ∧
    fe51ValOfBytes res % p25519 = fpAdd (fe51ValOfBytes dy2_bs % p25519) 1 := by
  intro l0 l1 l2 l3 l4 res
  haveI : HasLenGe dst 40 := ⟨by omega⟩
  obtain ⟨_, hy0, hy1, hy2, hy3, hy4⟩ := hdy2
  have hl0_b : l0.toNat < 2 ^ 52 := hy0
  have hl1_b : l1.toNat < 2 ^ 52 := hy1
  have hl2_b : l2.toNat < 2 ^ 52 := hy2
  have hl3_b : l3.toNat < 2 ^ 52 := hy3
  have hl4_b : l4.toNat < 2 ^ 52 := hy4
  have hl0_add : (l0 + 1#64).toNat = l0.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hlen : res.length = 40 := by
    dsimp only [res]; simp only [write64_length_eq, hdst]; decide
  have hb54 : fe51LimbsBounded res (2 ^ 54) := by
    unfold fe51LimbsBounded
    refine ⟨hlen, ?_⟩
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hv : fe51ValOfBytes res % p25519 = fpAdd (fe51ValOfBytes dy2_bs % p25519) 1 := by
    unfold fe51ValOfBytes fpAdd
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    unfold fe51Val
    rw [hl0_add]
    have h_eq : l0.toNat + 1 + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204 =
        (l0.toNat + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204) + 1 := by omega
    rw [h_eq]
    dsimp only [l0, l1, l2, l3, l4]
    rw [← Nat.mod_add_mod]
  exact ⟨hlen, hb54, hv⟩

private theorem u_eq_zero_arith (p s u q K M : Nat)
    (hu0 : 0 < u) (hu : u < p) (hp_odd : p % 2 = 1)
    (hdiv : p * q + u = (p - u) * s)
    (hM : (s + 1) * K = p * M + 2) : False := by
  have hle : u * s ≤ p * s := Nat.mul_le_mul_right s (Nat.le_of_lt hu)
  have h1 : u * (s + 1) = p * (s - q) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_sub_left_distrib]
    rw [Nat.sub_mul] at hdiv
    omega
  have h2 : u * ((s + 1) * K) = p * ((s - q) * K) := by
    rw [← Nat.mul_assoc, h1, Nat.mul_assoc]
  rw [hM, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm u p, Nat.mul_assoc] at h2
  have h3 : 2 * u = p * ((s - q) * K - u * M) := by
    rw [Nat.mul_sub_left_distrib]
    omega
  generalize (s - q) * K - u * M = k at h3
  rcases k with _ | _ | k
  · rw [Nat.mul_zero] at h3; omega
  · rw [Nat.zero_add, Nat.mul_one] at h3; omega
  · rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h3; omega

private theorem u_eq_zero_of_eq_fpMul_fpNeg_sqrtM1 (u : Nat) (hu : u < p25519)
    (h : u = fpMul (fpNeg u) sqrtM1) : u = 0 := by
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rfl
  have hp_pos : 0 < p25519 := Nat.lt_trans hpos hu
  have hp_sub : p25519 - u < p25519 := Nat.sub_lt hp_pos hpos
  have hneg : fpNeg u = p25519 - u := by
    unfold fpNeg
    rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hp_sub]
  have hsqrt : sqrtM1 % p25519 = sqrtM1 := Nat.mod_eq_of_lt (by unfold sqrtM1 p25519; decide)
  have hmul : fpMul (fpNeg u) sqrtM1 = ((p25519 - u) * sqrtM1) % p25519 := by
    unfold fpMul
    rw [hneg, hsqrt, Nat.mod_eq_of_lt hp_sub]
  rw [hmul] at h
  let q := ((p25519 - u) * sqrtM1) / p25519
  have hdiv : p25519 * q + u = (p25519 - u) * sqrtM1 := by
    dsimp only [q]
    have hdm := Nat.div_add_mod ((p25519 - u) * sqrtM1) p25519
    rw [← h] at hdm
    exact hdm
  let K := p25519 + 1 - sqrtM1
  let M := (sqrtM1 + 1) * K / p25519
  have hM : (sqrtM1 + 1) * K = p25519 * M + 2 := by
    dsimp only [K, M]; unfold sqrtM1 p25519; decide
  have hp_odd : p25519 % 2 = 1 := by unfold p25519; decide
  exact False.elim (u_eq_zero_arith p25519 sqrtM1 u q K M hpos hu hp_odd hdiv hM)

private theorem u_eq_zero_of_eq_fpNeg (u : Nat) (hu : u < p25519) (h : u = fpNeg u) : u = 0 := by
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rfl
  have hp_pos : 0 < p25519 := Nat.lt_trans hpos hu
  have hp_sub : p25519 - u < p25519 := Nat.sub_lt hp_pos hpos
  unfold fpNeg at h
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hp_sub] at h
  have hp_odd : p25519 % 2 = 1 := by unfold p25519; decide
  generalize p25519 = p at hu h hp_odd
  omega

private theorem fpMul_zero_left (b : Nat) : fpMul 0 b = 0 := by
  unfold fpMul; rw [Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]

private theorem fpMul_zero_right (a : Nat) : fpMul a 0 = 0 := by
  unfold fpMul; rw [Nat.zero_mod, Nat.mul_zero, Nat.zero_mod]

private theorem sqrtRatioM1_recoverXEven_core (u v r0 : Nat)
    (hu : u < p25519) (hr0_lt : r0 < p25519) (hr0_zero : u = 0 → r0 = 0) :
    let check := fpMul v (fpSq r0)
    let rPrime := fpMul sqrtM1 r0
    let r1 := if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0
    let rEven := if r1 % 2 == 1 then fpNeg r1 else r1
    let recX :=
      if check == u then
        some (if r0 % 2 == 1 then fpNeg r0 else r0)
      else if check == fpNeg u then
        let r1' := fpMul r0 sqrtM1
        some (if r1' % 2 == 1 then fpNeg r1' else r1')
      else
        none
    (((check == u) || (check == fpNeg u)) = false → recX = none) ∧
    (((check == u) || (check == fpNeg u)) = true → recX = some rEven ∧ rEven < p25519) := by
  intro check rPrime r1 rEven recX
  have hp : 0 < p25519 := by unfold p25519; decide
  have hrPrime_eq : rPrime = fpMul r0 sqrtM1 := by
    dsimp only [rPrime]; unfold fpMul; rw [Nat.mul_comm]
  have hrPrime_lt : rPrime < p25519 := by dsimp only [rPrime]; unfold fpMul; exact Nat.mod_lt _ hp
  have hneg_lt : ∀ a : Nat, fpNeg a < p25519 := fun a => by unfold fpNeg; exact Nat.mod_lt _ hp
  change (((check == u) || (check == fpNeg u)) = false →
      (if check == u then some (if r0 % 2 == 1 then fpNeg r0 else r0)
       else if check == fpNeg u then
         let r1' := fpMul r0 sqrtM1
         some (if r1' % 2 == 1 then fpNeg r1' else r1')
       else none) = none) ∧
    (((check == u) || (check == fpNeg u)) = true →
      (if check == u then some (if r0 % 2 == 1 then fpNeg r0 else r0)
       else if check == fpNeg u then
         let r1' := fpMul r0 sqrtM1
         some (if r1' % 2 == 1 then fpNeg r1' else r1')
       else none) =
      some (if (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0) % 2 == 1 then
              fpNeg (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0)
            else (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0)) ∧
      (if (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0) % 2 == 1 then
        fpNeg (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0)
      else (if (check == fpNeg u) || (check == fpMul (fpNeg u) sqrtM1) then rPrime else r0)) < p25519)
  by_cases hc1 : check == u
  · simp only [hc1, Bool.true_or, ↓reduceIte]
    refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
    have hchk_u : check = u := beq_iff_eq.mp hc1
    by_cases hc23 : (check == fpNeg u || check == fpMul (fpNeg u) sqrtM1)
    · have hu0 : u = 0 := by
        rcases Bool.or_eq_true_iff.mp hc23 with hc2 | hc3
        · exact u_eq_zero_of_eq_fpNeg u hu (hchk_u.symm.trans (beq_iff_eq.mp hc2))
        · exact u_eq_zero_of_eq_fpMul_fpNeg_sqrtM1 u hu (hchk_u.symm.trans (beq_iff_eq.mp hc3))
      have hr0_0 : r0 = 0 := hr0_zero hu0
      have hrP_0 : rPrime = 0 := by
        dsimp only [rPrime]; rw [hr0_0, fpMul_zero_right]
      have h0_mod2 : (0 % 2 == 1) = false := rfl
      simp only [hc23, ↓reduceIte, hr0_0, hrP_0, h0_mod2, Bool.false_eq_true]
      exact ⟨trivial, hp⟩
    · simp only [Bool.not_eq_true] at hc23
      simp only [hc23, Bool.false_eq_true, ↓reduceIte]
      cases (r0 % 2 == 1) <;> simp only [↓reduceIte, Bool.false_eq_true, hr0_lt, hneg_lt, and_self]
  · simp only [Bool.not_eq_true] at hc1
    simp only [hc1, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    by_cases hc2 : check == fpNeg u
    · simp only [hc2, Bool.true_or, ↓reduceIte, hrPrime_eq]
      refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
      cases (fpMul r0 sqrtM1 % 2 == 1) <;>
        simp only [↓reduceIte, Bool.false_eq_true, ← hrPrime_eq, hrPrime_lt, hneg_lt, and_self]
    · simp only [Bool.not_eq_true] at hc2
      simp only [hc2, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun _ => trivial, False.elim⟩

private theorem sqrtRatioM1_eq_recoverXEven (y : Nat) :
    let u := fpSub (fpSq y) 1
    let v := fpAdd (fpMul edD (fpSq y)) 1
    let sr := sqrtRatioM1 u v
    (sr.1 = false → recoverXEven y = none) ∧
    (sr.1 = true → recoverXEven y = some sr.2 ∧ sr.2 < p25519) := by
  intro u v sr
  have hp : 0 < p25519 := by unfold p25519; decide
  have hu : u < p25519 := by unfold u fpSub; exact Nat.mod_lt _ hp
  have hv : v < p25519 := by unfold v fpAdd; exact Nat.mod_lt _ hp
  have hu_mod : u % p25519 = u := Nat.mod_eq_of_lt hu
  have hv_mod : v % p25519 = v := Nat.mod_eq_of_lt hv
  let v3 := fpMul (fpSq v) v
  let v7 := fpMul (fpSq v3) v
  let r0 := fpMul (fpMul u v3) (fpPow (fpMul u v7) ((p25519 - 5) / 8))
  have hr0_lt : r0 < p25519 := by unfold r0 fpMul; exact Nat.mod_lt _ hp
  have hr0_zero : u = 0 → r0 = 0 := fun hu0 => by
    dsimp only [r0]; rw [hu0, fpMul_zero_left, fpMul_zero_left]
  have hcore := sqrtRatioM1_recoverXEven_core u v r0 hu hr0_lt hr0_zero
  dsimp only [sr, sqrtRatioM1, recoverXEven]
  rw [hu_mod, hv_mod]
  exact hcore

private theorem cneg_sel_limb (r0 : BitVec 64) (b : BitVec 8) (a nr : BitVec 64)
    (hr0 : BitVec.zeroExtend 8 r0 = b >>> 7) :
    (nr &&& -(r0 &&& 255#64)) ||| (a &&& ((r0 &&& 255#64) - 1#64)) =
      if (b >>> 7).toNat == 1 then nr else a := by
  have hr_eq : r0 &&& 255#64 = BitVec.zeroExtend 64 (b >>> 7) := by
    revert hr0; bv_bits
  have h1 : ∀ x : BitVec 8,
      -(BitVec.zeroExtend 64 (x >>> 7)) =
        if (x >>> 7).toNat == 1 then 18446744073709551615#64 else 0#64 := by decide
  have h2 : ∀ x : BitVec 8,
      BitVec.zeroExtend 64 (x >>> 7) - 1#64 =
        if (x >>> 7).toNat == 1 then 0#64 else 18446744073709551615#64 := by decide
  rw [hr_eq, h1 b, h2 b]
  cases ((b >>> 7).toNat == 1) <;> simp only [↓reduceIte, Bool.false_eq_true] <;> bv_bits

private theorem fe51_cneg_post (sp : BitVec 64) (r_bs : List (BitVec 8)) (r0 : BitVec 64) (b31 : BitVec 8)
    (hr : fe51LimbsBounded r_bs (2 ^ 52))
    (hr0 : BitVec.zeroExtend 8 r0 = b31 >>> 7) :
    let l0 := ByteSlice.readLE r_bs 0 8
    let l1 := ByteSlice.readLE r_bs 8 8
    let l2 := ByteSlice.readLE r_bs 16 8
    let l3 := ByteSlice.readLE r_bs 24 8
    let l4 := ByteSlice.readLE r_bs 32 8
    let d0 := (36028797018963663#64 - l0) + 1#64
    let d1 := 36028797018963952#64 - l1
    let d2 := 36028797018963952#64 - l2
    let d3 := 36028797018963952#64 - l3
    let d4 := 36028797018963952#64 - l4
    let nr0 := (d0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64
    let nr1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
    let nr2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
    let nr3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
    let nr4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
    let m1 := -(r0 &&& 255#64)
    let m0 := (r0 &&& 255#64) - 1#64
    let res4 := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      r_bs 0 ((nr0 &&& m1) ||| (l0 &&& m0)))
      8 ((nr1 &&& m1) ||| (l1 &&& m0)))
      16 ((nr2 &&& m1) ||| (l2 &&& m0)))
      24 ((nr3 &&& m1) ||| (l3 &&& m0))
    let w4 := (nr4 &&& m1) ||| (l4 &&& m0)
    let res := ByteSlice.write64 res4 32 w4
    (res.length = 40 ∧ fe51LimbsBounded res (2 ^ 52) ∧ fe51LimbsBounded res (2 ^ 54) ∧
     fe51ValOfBytes res % p25519 =
       if (b31 >>> 7).toNat == 1 then fpNeg (fe51ValOfBytes r_bs % p25519) else fe51ValOfBytes r_bs % p25519) ∧
    (((sp - 176#64) ↦ₛ res ∗
      (sp - 464#64) ↦₆₄ ByteSlice.readLE res4 0 8 ∗
      (sp - 456#64) ↦₆₄ ByteSlice.readLE res4 8 8 ∗
      (sp - 448#64) ↦₆₄ ByteSlice.readLE res4 16 8 ∗
      (sp - 440#64) ↦₆₄ ByteSlice.readLE res4 24 8 ∗
      (sp - 432#64) ↦₆₄ w4) =
     ((sp - 176#64) ↦ₛ res ∗
      (sp - 464#64) ↦₆₄ ByteSlice.readLE res 0 8 ∗
      (sp - 456#64) ↦₆₄ ByteSlice.readLE res 8 8 ∗
      (sp - 448#64) ↦₆₄ ByteSlice.readLE res 16 8 ∗
      (sp - 440#64) ↦₆₄ ByteSlice.readLE res 24 8 ∗
      (sp - 432#64) ↦₆₄ ByteSlice.readLE res 32 8)) := by
  intro l0 l1 l2 l3 l4 d0 d1 d2 d3 d4 nr0 nr1 nr2 nr3 nr4 m1 m0 res4 w4 res
  obtain ⟨hr_len, hl0, hl1, hl2, hl3, hl4⟩ := hr
  haveI : HasLenGe r_bs 40 := ⟨by omega⟩
  have hlen : res.length = 40 := by
    dsimp only [res, res4]; simp only [write64_length_eq, hr_len]; decide
  have hred_b := fe51Reduce_bounded d0 d1 d2 d3 d4
  have hs0 := cneg_sel_limb r0 b31 l0 nr0 hr0
  have hs1 := cneg_sel_limb r0 b31 l1 nr1 hr0
  have hs2 := cneg_sel_limb r0 b31 l2 nr2 hr0
  have hs3 := cneg_sel_limb r0 b31 l3 nr3 hr0
  have hs4 := cneg_sel_limb r0 b31 l4 nr4 hr0
  have hb52 : fe51LimbsBounded res (2 ^ 52) := by
    unfold fe51LimbsBounded
    refine ⟨hlen, ?_⟩
    dsimp only [res, res4, w4, m1, m0]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    rw [hs0, hs1, hs2, hs3, hs4]
    cases ((b31 >>> 7).toNat == 1) <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact ⟨hl0, hl1, hl2, hl3, hl4⟩
    · exact hred_b
  have hb54 : fe51LimbsBounded res (2 ^ 54) := by
    obtain ⟨hl, h0, h1, h2, h3, h4⟩ := hb52
    exact ⟨hl, by omega, by omega, by omega, by omega, by omega⟩
  have hd0_eq : d0 = 36028797018963664#64 - l0 := by
    dsimp only [d0]; bv_omega
  have hl_b54 : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧ l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54 := by
    dsimp only [l0, l1, l2, l3, l4]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hv : fe51ValOfBytes res % p25519 =
      if (b31 >>> 7).toNat == 1 then fpNeg (fe51ValOfBytes r_bs % p25519) else fe51ValOfBytes r_bs % p25519 := by
    unfold fe51ValOfBytes
    dsimp only [res, res4, w4, m1, m0]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    rw [hs0, hs1, hs2, hs3, hs4]
    cases ((b31 >>> 7).toNat == 1) <;> simp only [↓reduceIte, Bool.false_eq_true]
    · rfl
    · change fe51Val nr0 nr1 nr2 nr3 nr4 % p25519 = _
      rw [fe51Reduce_val_mod d0 d1 d2 d3 d4, hd0_eq,
          fe51Neg_val_mod l0 l1 l2 l3 l4 hl_b54]
  have he0 : ByteSlice.readLE res4 0 8 = ByteSlice.readLE res 0 8 :=
    (readLE_write64_ne res4 32 0 40 w4 (by decide)).symm
  have he8 : ByteSlice.readLE res4 8 8 = ByteSlice.readLE res 8 8 :=
    (readLE_write64_ne res4 32 8 40 w4 (by decide)).symm
  have he16 : ByteSlice.readLE res4 16 8 = ByteSlice.readLE res 16 8 :=
    (readLE_write64_ne res4 32 16 40 w4 (by decide)).symm
  have he24 : ByteSlice.readLE res4 24 8 = ByteSlice.readLE res 24 8 :=
    (readLE_write64_ne res4 32 24 40 w4 (by decide)).symm
  have he32 : w4 = ByteSlice.readLE res 32 8 :=
    (readLE_write64_self' res4 32 40 w4 (by decide)).symm
  refine ⟨⟨hlen, hb52, hb54, hv⟩, ?_⟩
  rw [he0, he8, he16, he24, ← he32]

private theorem sepWP_cneg_abstract (sp : BitVec 64) (r_bs : List (BitVec 8))
    (b31 : BitVec 8) {r0 : BitVec 64}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hr : fe51LimbsBounded r_bs (2 ^ 52))
    (hr0 : BitVec.zeroExtend 8 r0 = b31 >>> 7)
    (hf : Full =
      (let l0 := ByteSlice.readLE r_bs 0 8
       let l1 := ByteSlice.readLE r_bs 8 8
       let l2 := ByteSlice.readLE r_bs 16 8
       let l3 := ByteSlice.readLE r_bs 24 8
       let l4 := ByteSlice.readLE r_bs 32 8
       let d0 := (36028797018963663#64 - l0) + 1#64
       let d1 := 36028797018963952#64 - l1
       let d2 := 36028797018963952#64 - l2
       let d3 := 36028797018963952#64 - l3
       let d4 := 36028797018963952#64 - l4
       let nr0 := (d0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64
       let nr1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
       let nr2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
       let nr3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
       let nr4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
       let m1 := -(r0 &&& 255#64)
       let m0 := (r0 &&& 255#64) - 1#64
       let res4 := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
         r_bs 0 ((nr0 &&& m1) ||| (l0 &&& m0)))
         8 ((nr1 &&& m1) ||| (l1 &&& m0)))
         16 ((nr2 &&& m1) ||| (l2 &&& m0)))
         24 ((nr3 &&& m1) ||| (l3 &&& m0))
       let w4 := (nr4 &&& m1) ||| (l4 &&& m0)
       let res := ByteSlice.write64 res4 32 w4
       ((sp - 176#64) ↦ₛ res ∗
        (sp - 464#64) ↦₆₄ ByteSlice.readLE res4 0 8 ∗
        (sp - 456#64) ↦₆₄ ByteSlice.readLE res4 8 8 ∗
        (sp - 448#64) ↦₆₄ ByteSlice.readLE res4 16 8 ∗
        (sp - 440#64) ↦₆₄ ByteSlice.readLE res4 24 8 ∗
        (sp - 432#64) ↦₆₄ w4)) ∗ P := by dsimp only; sep_frame)
    (hnext : ∀ x_bs : List (BitVec 8),
      x_bs.length = 40 ∧ fe51LimbsBounded x_bs (2 ^ 52) ∧ fe51LimbsBounded x_bs (2 ^ 54) ∧
      fe51ValOfBytes x_bs % p25519 =
        (if (b31 >>> 7).toNat == 1 then fpNeg (fe51ValOfBytes r_bs % p25519) else fe51ValOfBytes r_bs % p25519) →
      SepWP prog target_pc s
        (((sp - 176#64) ↦ₛ x_bs ∗
          (sp - 464#64) ↦₆₄ ByteSlice.readLE x_bs 0 8 ∗
          (sp - 456#64) ↦₆₄ ByteSlice.readLE x_bs 8 8 ∗
          (sp - 448#64) ↦₆₄ ByteSlice.readLE x_bs 16 8 ∗
          (sp - 440#64) ↦₆₄ ByteSlice.readLE x_bs 24 8 ∗
          (sp - 432#64) ↦₆₄ ByteSlice.readLE x_bs 32 8) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  obtain ⟨hpost, hsep⟩ := fe51_cneg_post sp r_bs r0 b31 hr hr0
  rw [hf, hsep]
  exact hnext _ hpost

private theorem sr_pad_split (sp : BitVec 64) (pad_bs r_bs : List (BitVec 8))
    (hpad : pad_bs.length = 7) :
    ((sp - 127#64) ↦ₛ (pad_bs ++ r_bs)) =
      ((sp - 127#64) ↦ₛ pad_bs) ∗ ((sp - 120#64) ↦ₛ r_bs) := by
  rw [pointsToBytes_append, hpad]
  have h2 : sp - 127#64 + BitVec.ofNat 64 7 = sp - 120#64 := by bv_omega
  rw [h2]

private theorem sr_out_split (sp : BitVec 64) (b0 : BitVec 8) (pad_bs r_bs : List (BitVec 8))
    (hpad : pad_bs.length = 7) :
    ((sp - 128#64) ↦ₛ (b0 :: pad_bs ++ r_bs)) =
      ((sp - 128#64) ↦₈ b0) ∗ ((sp - 127#64) ↦ₛ pad_bs) ∗ ((sp - 120#64) ↦ₛ r_bs) := by
  change ((sp - 128#64) ↦ₛ (b0 :: (pad_bs ++ r_bs))) = _
  rw [pointsToBytes_cons]
  have h1 : sp - 128#64 + 1#64 = sp - 127#64 := by bv_omega
  rw [h1, sr_pad_split sp pad_bs r_bs hpad]

private theorem sr_out_resplit40 (sp : BitVec 64) (b0 : BitVec 8) (pad_bs r_bs : List (BitVec 8))
    (hpad : pad_bs.length = 7) (hr : r_bs.length = 40) :
    (((sp - 128#64) ↦₈ b0) ∗ ((sp - 127#64) ↦ₛ pad_bs) ∗ ((sp - 120#64) ↦ₛ r_bs)) =
      (((sp - 128#64) ↦ₛ (b0 :: pad_bs ++ r_bs).take 40) ∗
       ((sp - 88#64) ↦ₛ (b0 :: pad_bs ++ r_bs).drop 40)) ∧
    ((b0 :: pad_bs ++ r_bs).take 40).length = 40 ∧
    ((b0 :: pad_bs ++ r_bs).drop 40).length = 8 := by
  refine ⟨?_, by simp [hpad, hr], by simp [hpad, hr]⟩
  rw [← sr_out_split sp b0 pad_bs r_bs hpad,
      pointsToBytes_take_drop (sp - 128#64) 40 (b0 :: pad_bs ++ r_bs) (by simp [hpad, hr])]
  have h40 : sp - 128#64 + 40#64 = sp - 88#64 := by bv_omega
  rw [h40]

private theorem sepWP_sr_resplit40 (sp : BitVec 64) (b0 : BitVec 8) (pad_bs r_bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 128#64) ↦₈ b0) ∗ ((sp - 127#64) ↦ₛ pad_bs) ∗ ((sp - 120#64) ↦ₛ r_bs)) ∗ P := by sep_frame)
    (hpad : pad_bs.length = 7) (hr : r_bs.length = 40)
    (hnext : ∀ (sr40_bs sr8_bs : List (BitVec 8)),
      sr40_bs.length = 40 → sr8_bs.length = 8 →
      SepWP prog target_pc s ((((sp - 128#64) ↦ₛ sr40_bs) ∗ ((sp - 88#64) ↦ₛ sr8_bs)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  obtain ⟨h, h40, h8⟩ := sr_out_resplit40 sp b0 pad_bs r_bs hpad hr
  rw [hf, h]
  exact hnext _ _ h40 h8

private theorem sepWP_merge_stack_bytes40_8 (sp : BitVec 64)
    {bs1 bs2 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 128#64) ↦ₛ bs1) ∗ ((sp - 88#64) ↦ₛ bs2)) ∗ P := by sep_frame)
    (hbs1 : bs1.length = 40)
    (hnext : SepWP prog target_pc s (((sp - 128#64) ↦ₛ (bs1 ++ bs2)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h1 : ((sp - 128#64) ↦ₛ (bs1 ++ bs2)) =
      ((sp - 128#64) ↦ₛ bs1) ∗ ((sp - 88#64) ↦ₛ bs2) := by
    rw [pointsToBytes_append, hbs1, show sp - 128#64 + BitVec.ofNat 64 40 = sp - 88#64 by bv_omega]
  rw [hf, ← h1]
  exact hnext

private theorem pointsToBytes40_write64_32_0_8_16_24 (a : BitVec 64) (old src : List (BitVec 8))
    (hold : old.length = 40) (hsrc : src.length = 40) :
    (a ↦ₛ ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      old 32 (ByteSlice.readLE src 32 8))
      0 (ByteSlice.readLE src 0 8))
      8 (ByteSlice.readLE src 8 8))
      16 (ByteSlice.readLE src 16 8))
      24 (ByteSlice.readLE src 24 8)) = (a ↦ₛ src) := by
  haveI : HasLenGe old 40 := ⟨by omega⟩
  have hlen : (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      old 32 (ByteSlice.readLE src 32 8)) 0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
      16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)).length = 40 := by
    simp only [write64_length_eq, hold]; decide
  rw [pointsToBytes40_eq_cells a _ hlen, pointsToBytes40_eq_cells a src hsrc]
  simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]

private theorem decompress_epilogue_post (dst x_bs y_bs t_bs : List (BitVec 8)) (x y : Nat)
    (hdst : dst.length = 160)
    (hx_b : fe51LimbsBounded x_bs (2 ^ 52))
    (hy_b : fe51LimbsBounded y_bs (2 ^ 52))
    (ht_b : fe51LimbsBounded t_bs (2 ^ 52))
    (hx_v : fe51ValOfBytes x_bs % p25519 = x % p25519)
    (hy_v : fe51ValOfBytes y_bs % p25519 = y % p25519)
    (ht_v : fe51ValOfBytes t_bs % p25519 = fpMul (x % p25519) (y % p25519)) :
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 128 (ByteSlice.readLE t_bs 8 8)) 136 (ByteSlice.readLE t_bs 16 8))
        144 (ByteSlice.readLE t_bs 24 8)) 152 (ByteSlice.readLE t_bs 32 8))
        0 (ByteSlice.readLE x_bs 0 8)) 8 (ByteSlice.readLE x_bs 8 8))
        16 (ByteSlice.readLE x_bs 16 8)) 24 (ByteSlice.readLE x_bs 24 8))
        96 0#64) 104 0#64) 112 0#64) 120 (ByteSlice.readLE t_bs 0 8))
        80 1#64) 88 0#64) 64 (ByteSlice.readLE y_bs 24 8)) 72 (ByteSlice.readLE y_bs 32 8))
        32 (ByteSlice.readLE x_bs 32 8)) 40 (ByteSlice.readLE y_bs 0 8))
        48 (ByteSlice.readLE y_bs 8 8)) 56 (ByteSlice.readLE y_bs 16 8)
    res.length = 160 ∧ fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edExtOfAffine ⟨x, y⟩ := by
  intro res
  haveI : HasLenGe dst 160 := ⟨by omega⟩
  have hlen : res.length = 160 := by
    dsimp only [res]; simp only [write64_length_eq, hdst]; decide
  have hbnd : fe51Point4Bounded res (2 ^ 52) := by
    unfold fe51Point4Bounded fe51LimbsBoundedAt
    refine ⟨hlen, ?_⟩
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    exact ⟨hx_b.2, hy_b.2, ⟨by decide, by decide, by decide, by decide, by decide⟩, ht_b.2⟩
  have hval : edExtOfBytes res = edExtOfAffine ⟨x, y⟩ := by
    unfold edExtOfBytes edExtOfAffine fe51ValAt
    dsimp only [res]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    have hz : fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519 = 1 := by decide
    change ({ X := fe51ValOfBytes x_bs % p25519,
              Y := fe51ValOfBytes y_bs % p25519,
              Z := fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519,
              T := fe51ValOfBytes t_bs % p25519 } : EdExtPoint) = _
    rw [hx_v, hy_v, hz, ht_v]
  exact ⟨hlen, hbnd, hval⟩

private theorem decompress_epilogue_post' (dst x_bs y_bs t_bs : List (BitVec 8))
    (hdst : dst.length = 160)
    (hx_b : fe51LimbsBounded x_bs (2 ^ 52))
    (hy_b : fe51LimbsBounded y_bs (2 ^ 52))
    (ht_b : fe51LimbsBounded t_bs (2 ^ 52))
    (ht_v : fe51ValOfBytes t_bs % p25519 = fe51ValOfBytes x_bs * fe51ValOfBytes y_bs % p25519) :
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 128 (ByteSlice.readLE t_bs 8 8)) 136 (ByteSlice.readLE t_bs 16 8))
        144 (ByteSlice.readLE t_bs 24 8)) 152 (ByteSlice.readLE t_bs 32 8))
        0 (ByteSlice.readLE x_bs 0 8)) 8 (ByteSlice.readLE x_bs 8 8))
        16 (ByteSlice.readLE x_bs 16 8)) 24 (ByteSlice.readLE x_bs 24 8))
        96 0#64) 104 0#64) 112 0#64) 120 (ByteSlice.readLE t_bs 0 8))
        80 1#64) 88 0#64) 64 (ByteSlice.readLE y_bs 24 8)) 72 (ByteSlice.readLE y_bs 32 8))
        32 (ByteSlice.readLE x_bs 32 8)) 40 (ByteSlice.readLE y_bs 0 8))
        48 (ByteSlice.readLE y_bs 8 8)) 56 (ByteSlice.readLE y_bs 16 8)
    res.length = 160 ∧ fe51Point4Bounded res (2 ^ 52) ∧
    edExtOfBytes res = edExtOfAffine ⟨fe51ValOfBytes x_bs % p25519, fe51ValOfBytes y_bs % p25519⟩ := by
  apply decompress_epilogue_post dst x_bs y_bs t_bs
    (fe51ValOfBytes x_bs % p25519) (fe51ValOfBytes y_bs % p25519)
    hdst hx_b hy_b ht_b
    (Nat.mod_mod _ _).symm (Nat.mod_mod _ _).symm
  unfold fpMul
  simp only [Nat.mod_mod, ← Nat.mul_mod, ht_v]

private theorem fe51EdwardsDBytes_val :
    fe51ValOfBytes fe51EdwardsDBytes % p25519 = edD := by
  decide +kernel

private theorem decompress_sr_recoverXEven (y w u w1 v : Nat) (sr : Bool × Nat)
    (hw : w % p25519 = fpPow (y % p25519) 2)
    (hu : u % p25519 = fpSub (w % p25519) 1)
    (hw1 : w1 % p25519 = w * fe51ValOfBytes fe51EdwardsDBytes % p25519)
    (hv : v % p25519 = fpAdd (w1 % p25519) 1)
    (hsr : sqrtRatioM1 (u % p25519) (v % p25519) = sr) :
    (sr.1 = false → recoverXEven (y % p25519) = none) ∧
    (sr.1 = true → recoverXEven (y % p25519) = some sr.2 ∧ sr.2 < p25519) := by
  have hy2 : w % p25519 = fpSq (y % p25519) := by
    rw [hw, fpPow_two_eq_fpSq]
  have hu' : u % p25519 = fpSub (fpSq (y % p25519)) 1 := by
    rw [hu, hy2]
  have hw1' : w1 % p25519 = fpMul edD (fpSq (y % p25519)) := by
    unfold fpMul
    rw [← Nat.mul_mod, hw1, Nat.mul_mod, hy2, fe51EdwardsDBytes_val, Nat.mul_comm]
  have hv' : v % p25519 = fpAdd (fpMul edD (fpSq (y % p25519))) 1 := by
    rw [hv, hw1']
  rw [hu', hv'] at hsr
  rw [← hsr]
  exact sqrtRatioM1_eq_recoverXEven (y % p25519)

private theorem decodeEdDalek_eq_none_of_sr_false (bs : List (BitVec 8)) (y : Nat)
    (hbs : bs.length = 32)
    (hy : y = leBytesToNat bs % (2 ^ 255))
    (hrec : recoverXEven (y % p25519) = none) :
    decodeEdDalek bs = none := by
  unfold decodeEdDalek
  simp only [hbs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ← hy, hrec]

private theorem decodeEdDalek_eq_some_of_sr_true (bs : List (BitVec 8)) (y sr2 x : Nat)
    (hbs : bs.length = 32)
    (hy : y = leBytesToNat bs % (2 ^ 255))
    (hsign : (leBytesToNat bs / 2 ^ 255) % 2 = ((bs.getD 31 0#8) >>> 7).toNat)
    (hrec : recoverXEven (y % p25519) = some sr2)
    (hx : x = if ((bs.getD 31 0#8) >>> 7).toNat == 1 then fpNeg sr2 else sr2) :
    decodeEdDalek bs = some ⟨x, y % p25519⟩ := by
  unfold decodeEdDalek
  simp only [hbs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ← hy, hrec, hsign, ← hx]

public section

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
attribute [local irreducible] decodeEdDalek edExtOfAffine sqrtRatioM1 in
theorem compressed_edwards_y_decompress_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk)
    (hPow2k : Fe51Pow2kOk) (hSqrtRatioI : Fe51SqrtRatioIOk) :
    CompressedEdwardsYDecompressOk := by
  intro _
  apply dalekCaller_ok dalekCliPC05 dalekCliPl05
  intro b hb hbase
  wp_init
  have hout_len : a_2.length = 168 := ‹_›
  have hself_len : a_rest.length = 32 := ‹_›
  apply sepWP_split_stack_callee 1712 464
  apply sepWP_peel_stack_bytes s0.sp 464 40 424; intro dy2_init hdy2_init
  apply sepWP_peel_stack_region s0.sp 424 80 344
  apply sepWP_peel_stack_bytes s0.sp 344 40 304; intro t_init ht_init
  apply sepWP_peel_stack_bytes s0.sp 304 8 296; intro gap1_init hgap1_init
  apply sepWP_peel_stack_bytes s0.sp 296 40 256; intro y_init hy_init
  apply sepWP_peel_stack_bytes s0.sp 256 40 216; intro y2_init hy2_init
  apply sepWP_peel_stack_bytes s0.sp 216 40 176; intro u_init hu_init
  apply sepWP_peel_stack_bytes s0.sp 176 40 136; intro v_init hv_init
  apply sepWP_peel_stack_bytes s0.sp 136 8 128; intro gap2_init hgap2_init
  apply sepWP_peel_stack_bytes s0.sp 128 48 80; intro sr_init hsr_init
  open_cells (s0.sp - 80#64) 80 10
  wp_conv_pre =>
    rw [pointsToBytes168_split a_1 a_2 hout_len]
  have hdst_len : (a_2.drop 8).length = 160 := by simp [hout_len]
  haveI : HasLenGe (a_2.drop 8) 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 32 := ⟨by omega⟩
  haveI : HasLenGe y_init 40 := ⟨by omega⟩
  -- Step +0x000 .. +0x06c (from_bytes into y at s0.sp - 296#64)
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm]; assumption
  intro hcl_1
  apply sepWP_abstract_bytes (s0.sp - 296#64)
    (fun y_bs => y_bs.length = 40 ∧ fe51LimbsBounded y_bs (2 ^ 52) ∧ fe51LimbsBounded y_bs (2 ^ 54) ∧
      fe51ValOfBytes y_bs = leBytesToNat a_rest % (2 ^ 255) ∧
      (leBytesToNat a_rest / 2 ^ 255) % 2 = ((a_rest.getD 31 0#8) >>> 7).toNat)
    (hQ := fe51_from_bytes_post y_init a_rest hy_init hself_len)
  intro y_bs ⟨hy_l, hy_b52, ⟨_, hy_0, hy_1, hy_2, hy_3, hy_4⟩, hy_val, hy_sign⟩
  -- Call 1: pow2k(sp + 0xd0, sp + 0xa8, 1) -> s0.sp - 256#64 (y2)
  apply sepWP_callee_shrink (s0.sp - 464#64) 1712 96 1616
  wp_dalek_call hPow2k; clean_prev_sf; norm_sf 96
  apply sepWP_callee_grow (s0.sp - 464#64) 1712 96 1616
  clear hy_0 hy_1 hy_2 hy_3 hy_4
  -- Step +0x074 .. +0x0e4 (sub1_reduce into u at s0.sp - 216#64)
  have hw_b52 : fe51LimbsBounded w (2 ^ 52) := ‹_›
  have hw_post : fe51ValOfBytes w % p25519 = fpPow (fe51ValOfBytes y_bs % p25519) 2 := ‹_›
  have h_w_len : w.length = 40 := hw_b52.1
  haveI : HasLenGe w 40 := ⟨by omega⟩
  haveI : HasLenGe u_init 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm]; assumption
  intro hcl_2
  apply sepWP_abstract_bytes (s0.sp - 216#64)
    (fun u_bs => u_bs.length = 40 ∧ fe51LimbsBounded u_bs (2 ^ 54) ∧
      fe51ValOfBytes u_bs % p25519 = fpSub (fe51ValOfBytes w % p25519) 1)
    (hQ := fe51_sub1_reduce_post u_init w hu_init hw_b52)
  intro u_bs ⟨hu_l, ⟨_, hu_0, hu_1, hu_2, hu_3, hu_4⟩, hu_val⟩
  -- Call 2: mul(sp, sp + 0xd0, edwards_d) -> s0.sp - 464#64 (dy2)
  obtain ⟨hd_l, hd_0, hd_1, hd_2, hd_3, hd_4⟩ := fe51EdwardsDBytes_bounded
  obtain ⟨hy2_l, hy2_0, hy2_1, hy2_2, hy2_3, hy2_4⟩ := fe51LimbsBounded_of_52 w hw_b52
  apply sepWP_callee_shrink (s0.sp - 464#64) 1712 224 1488
  wp_dalek_call hMulRo; clean_prev_sf; norm_sf 224
  apply sepWP_callee_grow (s0.sp - 464#64) 1712 224 1488
  clear hd_l hd_0 hd_1 hd_2 hd_3 hd_4 hy2_0 hy2_1 hy2_2 hy2_3 hy2_4
  -- Step +0x0ec .. +0x110 (add1 into v at s0.sp - 176#64)
  have hw1_b52 : fe51LimbsBounded w_1 (2 ^ 52) := ‹_›
  have hw1_post : fe51ValOfBytes w_1 % p25519 =
      (fe51ValOfBytes w * fe51ValOfBytes fe51EdwardsDBytes) % p25519 := ‹_›
  have h_w1_len : w_1.length = 40 := hw1_b52.1
  haveI : HasLenGe w_1 40 := ⟨by omega⟩
  haveI : HasLenGe v_init 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm]; assumption
  intro hcl_3
  apply sepWP_abstract_bytes (s0.sp - 176#64)
    (fun v_bs => v_bs.length = 40 ∧ fe51LimbsBounded v_bs (2 ^ 54) ∧
      fe51ValOfBytes v_bs % p25519 = fpAdd (fe51ValOfBytes w_1 % p25519) 1)
    (hQ := fe51_add1_post v_init w_1 hv_init hw1_b52)
  intro v_bs ⟨hv_l, ⟨_, hv_0, hv_1, hv_2, hv_3, hv_4⟩, hv_val⟩
  -- Call 3: sqrt_ratio_i(x29 - 0x30, x29 - 0x88, x29 - 0x60) -> s0.sp - 128#64
  wp_dalek_call hSqrtRatioI; clean_prev_sf; norm_sf 1712
  clear hu_0 hu_1 hu_2 hu_3 hu_4 hv_0 hv_1 hv_2 hv_3 hv_4
  have hpad_l : w_2.length = 7 := ‹_›
  have hr_b52 : fe51LimbsBounded w_3 (2 ^ 52) := ‹_›
  have hr_post : fe51ValOfBytes w_3 % p25519 =
      (sqrtRatioM1 (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes v_bs % p25519)).2 := ‹_›
  generalize hsr : sqrtRatioM1 (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes v_bs % p25519) = sr at hr_post ⊢
  have hr_l : w_3.length = 40 := hr_b52.1
  haveI : HasLenGe w_3 40 := ⟨by omega⟩
  haveI : HasLenGe y_bs 40 := ⟨by omega⟩
  haveI : HasLenGe v_bs 40 := ⟨by omega⟩
  open_cells (s0.sp - 424#64) 80 10
  have h_dy2_cells := pointsToBytes40_sub_eq_cells s0.sp 464#64 456#64 448#64 440#64 432#64 w_1 h_w1_len
  wp_conv_pre =>
    rw [h_dy2_cells, sr_pad_split s0.sp w_2 w_3 hpad_l]
  -- Step +0x118 .. +0x160 (14 + 5 instructions before cbz)
  wp_cut_codeLoaded
  wp_steps 14
  apply sepWP_sr_resplit40 s0.sp (if sr.1 = true then 1#8 else 0#8) w_2 w_3 (hpad := hpad_l) (hr := hr_l)
  intro sr40_bs sr8_bs hsr40_l hsr8_l
  haveI : HasLenGe sr40_bs 40 := ⟨by omega⟩
  wp_steps 5
  apply SepWP.done
  · rfl
  · simp only [arm64_norm]; assumption
  intro hcl_cbz
  wp_conv_pre =>
    rw [pointsToBytes40_write64_32_0_8_16_24 (s0.sp - 176#64) v_bs w_3 hv_l hr_l,
        pointsToBytes40_write64_32_0_8_16_24 (s0.sp - 128#64) sr40_bs y_bs hsr40_l hy_l]
  have ⟨hsr_false, hsr_true⟩ := decompress_sr_recoverXEven
    (fe51ValOfBytes y_bs) (fe51ValOfBytes w) (fe51ValOfBytes u_bs)
    (fe51ValOfBytes w_1) (fe51ValOfBytes v_bs) sr
    hw_post hu_val hw1_post hv_val hsr
  rcases sr with ⟨sr1, sr2⟩
  cases sr1
  · -- Case sr1 = false: cbz w8 jumps to +0x29c
    have hdec := decodeEdDalek_eq_none_of_sr_false a_rest (fe51ValOfBytes y_bs) hself_len hy_val (hsr_false rfl)
    simp only [hdec]
    wp_steps
    close_cells (s0.sp - 80#64) 80 10
    apply sepWP_merge_stack_bytes40_8 s0.sp (hbs1 := hy_l)
    apply sepWP_unpeel_stack_bytes s0.sp 128 48 80 (hbs := by simp [hy_l, hsr8_l])
    apply sepWP_unpeel_stack_bytes s0.sp 136 8 128 (hbs := hgap2_init)
    apply sepWP_unpeel_stack_bytes s0.sp 176 40 136 (hbs := hr_l)
    apply sepWP_unpeel_stack_bytes s0.sp 216 40 176 (hbs := hu_l)
    apply sepWP_unpeel_stack_bytes s0.sp 256 40 216 (hbs := h_w_len)
    apply sepWP_unpeel_stack_bytes s0.sp 296 40 256 (hbs := hy_l)
    apply sepWP_unpeel_stack_bytes s0.sp 304 8 296 (hbs := hgap1_init)
    apply sepWP_unpeel_stack_bytes s0.sp 344 40 304 (hbs := ht_init)
    close_cells (s0.sp - 464#64) 120 15
    apply sepWP_unpeel_stack_region s0.sp 464 120 344
    apply sepWP_merge_stack_callee 1712 464
    wp_done
  · -- Case sr1 = true: cbz w8 falls through to +0x168
    wp_steps
    apply sepWP_callee_shrink (s0.sp - 464#64) 1712 16 1696
    wp_dalek_call black_box_u8_ok; clean_prev_sf; norm_sf 16
    apply sepWP_callee_grow (s0.sp - 464#64) 1712 16 1696
    wp_cut_codeLoaded
    wp_steps
    apply SepWP.done
    · rfl
    · simp only [arm64_norm]; assumption
    intro hcl_4
    apply sepWP_cneg_abstract s0.sp w_3 (a_rest.getD 31 0#8) (hr := hr_b52) (hr0 := ‹_›)
    intro x_bs ⟨hx_l, hx_b52, ⟨_, hx_0, hx_1, hx_2, hx_3, hx_4⟩, hx_val⟩
    obtain ⟨_, hy_0, hy_1, hy_2, hy_3, hy_4⟩ := fe51LimbsBounded_of_52 y_bs hy_b52
    apply sepWP_callee_shrink (s0.sp - 464#64) 1712 224 1488
    wp_dalek_call hMul; clean_prev_sf; norm_sf 224
    apply sepWP_callee_grow (s0.sp - 464#64) 1712 224 1488
    clear hx_0 hx_1 hx_2 hx_3 hx_4 hy_0 hy_1 hy_2 hy_3 hy_4
    have hw4_b52 : fe51LimbsBounded w_4 (2 ^ 52) := ‹_›
    have hw4_post : fe51ValOfBytes w_4 % p25519 =
        (fe51ValOfBytes x_bs * fe51ValOfBytes y_bs) % p25519 := ‹_›
    have hw4_l : w_4.length = 40 := hw4_b52.1
    have h_t_cells := pointsToBytes40_sub_eq_cells s0.sp 344#64 336#64 328#64 320#64 312#64 w_4 hw4_l
    wp_conv_pre => rw [h_t_cells]
    have hdec := decodeEdDalek_eq_some_of_sr_true a_rest (fe51ValOfBytes y_bs) sr2
      (fe51ValOfBytes x_bs % p25519) hself_len hy_val hy_sign (hsr_true rfl).1 (by rw [← hr_post, hx_val])
    simp only [hdec]
    wp_steps
    apply sepWP_abstract_bytes (a_1 + 8#64)
      (fun pt_bs => pt_bs.length = 160 ∧ fe51Point4Bounded pt_bs (2 ^ 52) ∧
        edExtOfBytes pt_bs = edExtOfAffine ⟨fe51ValOfBytes x_bs % p25519, fe51ValOfBytes y_bs % p25519⟩)
      (hQ := decompress_epilogue_post' (a_2.drop 8) x_bs y_bs w_4 hdst_len hx_b52 hy_b52
        hw4_b52 hw4_post)
    intro pt_bs ⟨hpt_l, hpt_b, hpt_val⟩
    obtain ⟨_, ⟨hpt0_0, hpt0_1, hpt0_2, hpt0_3, hpt0_4⟩,
               ⟨hpt1_0, hpt1_1, hpt1_2, hpt1_3, hpt1_4⟩,
               ⟨hpt2_0, hpt2_1, hpt2_2, hpt2_3, hpt2_4⟩,
               ⟨hpt3_0, hpt3_1, hpt3_2, hpt3_3, hpt3_4⟩⟩ := hpt_b
    close_cells (s0.sp - 80#64) 80 10
    apply sepWP_merge_stack_bytes40_8 s0.sp (hbs1 := hy_l)
    apply sepWP_unpeel_stack_bytes s0.sp 128 48 80 (hbs := by simp [hy_l, hsr8_l])
    apply sepWP_unpeel_stack_bytes s0.sp 136 8 128 (hbs := hgap2_init)
    apply sepWP_unpeel_stack_bytes s0.sp 176 40 136 (hbs := hx_l)
    apply sepWP_unpeel_stack_bytes s0.sp 216 40 176 (hbs := hu_l)
    apply sepWP_unpeel_stack_bytes s0.sp 256 40 216 (hbs := h_w_len)
    apply sepWP_unpeel_stack_bytes s0.sp 296 40 256 (hbs := hy_l)
    apply sepWP_unpeel_stack_bytes s0.sp 304 8 296 (hbs := hgap1_init)
    close_cells (s0.sp - 464#64) 160 20
    apply sepWP_unpeel_stack_region s0.sp 464 160 304
    apply sepWP_merge_stack_callee 1712 464
    wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress3
