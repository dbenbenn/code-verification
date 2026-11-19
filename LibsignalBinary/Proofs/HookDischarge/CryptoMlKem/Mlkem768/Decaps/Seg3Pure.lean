/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 3c Pure `compress_1 + serialize_1` Helpers
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 compressAndEncode compressCoeff mlkemQ neonBarrettReduce16 neonMontgomeryMul16 polySub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  neonBarrettReduce16_spec toInt_sub_of_bounds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  lane16_neonCompress1PreShift8h neonCompress1Lane16 neonCompress1Lane16_of_mod
  neonCompress1PreShift8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeChunk compressAndEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow (
  neonSerialize1MsbHalf neonSerialize1Msb_bfi_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (Vec128At polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b (seg3SubPoly)

theorem seg3SubPoly_compress1_eq {inv vPoly : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly.getD i 0#16).toInt ∧ (vPoly.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (i : Nat) (hi : i < 256) :
    neonCompress1Lane16 ((seg3SubPoly inv vPoly).getD i 0#16) =
      BitVec.ofNat 16 ((polySub vSpec invSpec).getD i 0 |> compressCoeff 1) := by
  have hget : (seg3SubPoly inv vPoly).getD i 0#16 =
      neonBarrettReduce16 (vPoly.getD i 0#16 - neonMontgomeryMul16 (inv.getD i 0#16) 1441#16) := by
    simp [seg3SubPoly, Array.getD, hi]
  rw [hget]
  let x := vPoly.getD i 0#16
  let y := neonMontgomeryMul16 (inv.getD i 0#16) 1441#16
  have hx := hv_bnd i hi
  have hy := hn_bnd i hi
  have hsub_int : (x - y).toInt = x.toInt - y.toInt :=
    toInt_sub_of_bounds (by dsimp only [x, y]; omega) (by dsimp only [x, y]; omega)
  obtain ⟨hb_lo, hb_hi, hb_mod⟩ := neonBarrettReduce16_spec (x - y)
  have hsub_spec : (polySub vSpec invSpec).getD i 0 =
      (vSpec.getD i 0 + mlkemQ - invSpec.getD i 0 % mlkemQ) % mlkemQ := by
    simp [polySub, Array.getD, hv_sz, hinv_sz, hi]
  have hmod : (neonBarrettReduce16 (x - y)).toInt % 3329 =
      ((polySub vSpec invSpec).getD i 0 : Int) % 3329 := by
    rw [hb_mod, hsub_int, hsub_spec]
    have hxr := hv_rep i hi
    have hyr := hn_rep i hi
    dsimp only [x, y, mlkemQ]
    have hvi : (invSpec.getD i 0 % 3329 : Nat) < 3329 := Nat.mod_lt _ (by decide)
    omega
  have hc := neonCompress1Lane16_of_mod (c := (polySub vSpec invSpec).getD i 0)
    (by omega) (by omega) hmod
  have hlt2 : compressCoeff 1 ((polySub vSpec invSpec).getD i 0) < 2 := by
    unfold compressCoeff; exact Nat.mod_lt _ (by decide)
  exact BitVec.eq_of_toNat_eq (by
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

@[expose] def serHalf1 (w : Poly16) (c : Nat) : BitVec 16 :=
  (evalBitfield .W32 .BFM
    ((neonSerialize1MsbHalf (neonCompress1PreShift8h (polyVecNat w (2 * c)))).zeroExtend 64)
    ((neonSerialize1MsbHalf (neonCompress1PreShift8h (polyVecNat w (2 * c + 1)))).zeroExtend 64)
    24 23).truncate 16

@[expose] def HalfRangeMem : Nat → BitVec 64 → (Nat → BitVec 16) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, h => (ptr ↦₁₆ h 0) ∗ HalfRangeMem n (ptr + 2#64) (fun i => h (i + 1))

theorem halfRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 16}
    (h : ∀ i, i < n → f i = g i) : HalfRangeMem n ptr f = HalfRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [HalfRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

theorem SepStore16.halfRange {n c : Nat} {ea ptr : BitVec 64} {val : BitVec 16}
    {w : Nat → BitVec 16} (hc : c < n) (ha : ptr + BitVec.ofNat 64 (2 * c) = ea) :
    SepStore16 ea val (HalfRangeMem n ptr w) (HalfRangeMem n ptr (Function.update w c val)) := by
  induction n generalizing c ptr w with
  | zero => omega
  | succ n ih =>
    rcases c with _ | c
    · simp only [Nat.mul_zero, BitVec.add_zero] at ha
      have htail : HalfRangeMem n (ptr + 2#64) (fun i => Function.update w 0 val (i + 1)) =
          HalfRangeMem n (ptr + 2#64) (fun i => w (i + 1)) :=
        halfRangeMem_congr fun i _ => Function.update_of_ne (Nat.succ_ne_zero i) val w
      simp only [HalfRangeMem, Function.update_self, htail]; exact (SepStore16.here ha).left
    · have ha' : (ptr + 2#64) + BitVec.ofNat 64 (2 * c) = ea := by
        rw [← ha, BitVec.add_assoc]; congr 1
        rw [show 2 * (c + 1) = 2 + 2 * c by omega, BitVec.ofNat_add]
      have hhead : Function.update w (c + 1) val 0 = w 0 :=
        Function.update_of_ne (Nat.succ_ne_zero c).symm val w
      have htail : (fun i => Function.update w (c + 1) val (i + 1)) =
          Function.update (fun i => w (i + 1)) c val := by
        funext i; by_cases h : i = c
        · subst h; simp
        · simp [Function.update_of_ne h, Function.update_of_ne (show i + 1 ≠ c + 1 by omega)]
      simp only [HalfRangeMem, hhead, htail]; exact (ih (by omega) ha').right

private theorem halfRangeMem_eq_pointsToBytes (n : Nat) (ptr : BitVec 64) (w : Nat → BitVec 16) :
    HalfRangeMem n ptr w = (ptr ↦ₛ ((List.range n).map fun i => unpack16 (w i)).flatten) := by
  induction n generalizing ptr w with
  | zero => simp [HalfRangeMem, pointsToBytes_nil]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [HalfRangeMem, List.map_cons, List.map_map, Function.comp_def, List.flatten_cons,
      ih (ptr + 2#64) (fun i => w (i + 1)), pointsTo16_eq_pointsToBytes]
    rw [pointsToBytes_append]
    simp [unpack16_length]

theorem vec128Zero2_eq_halfRangeMem (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗ Vec128At (ptr + 16#64) 0#128 = HalfRangeMem 16 ptr (fun _ => 0#16) := by
  have hrep : ((List.range 16).map fun (_ : Nat) => unpack16 0#16).flatten =
      (unpack64 0#64 ++ unpack64 0#64) ++ (unpack64 0#64 ++ unpack64 0#64) := by decide
  rw [halfRangeMem_eq_pointsToBytes, hrep, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [Vec128At, pointsTo64_eq_pointsToBytes]
  rw [show (0#128 : BitVec 128).extractLsb' 0 64 = 0#64 by decide,
    show (0#128 : BitVec 128).extractLsb' 64 64 = 0#64 by decide]
  simp [unpack64_length, show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega, sepConj_assoc]

theorem halfRangeMem_serHalf1_eq {inv vPoly : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly.getD i 0#16).toInt ∧ (vPoly.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (ptr : BitVec 64) :
    HalfRangeMem 16 ptr (serHalf1 (seg3SubPoly inv vPoly)) =
      (ptr ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) := by
  rw [halfRangeMem_eq_pointsToBytes,
    compressAndEncode_eq_flatten_chunks 1 (by decide) (polySub vSpec invSpec)]
  congr 1; congr 1
  apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  unfold serHalf1
  rw [neonSerialize1Msb_bfi_eq]
  unfold byteEncodeChunk
  congr 1
  refine Array.ext (by simp) fun j hj1 hj2 => ?_
  simp only [Array.size_ofFn] at hj1
  simp only [Array.getElem_ofFn, Nat.div_one, Nat.mod_one, Nat.shiftRight_zero]
  congr 2
  have hw_sz : (polySub vSpec invSpec).size = 256 := by simp [polySub, hv_sz, hinv_sz]
  have hmap_getD (k : Nat) (hk : k < 256) :
      ((polySub vSpec invSpec).map (compressCoeff 1)).getD k 0 =
        compressCoeff 1 ((polySub vSpec invSpec).getD k 0) := by
    simp [Array.getD, hw_sz, hk]
  by_cases hj8 : j < 8
  · simp only [hj8, lane16_neonCompress1PreShift8h]
    change neonCompress1Lane16 (lane16 (polyVecNat (seg3SubPoly inv vPoly) (2 * c)) ⟨j, hj8⟩) = _
    rw [polyVecNat, lane16_pack8x16]
    dsimp only
    rw [show 8 * (2 * c) + j = 16 * c + j by omega,
      seg3SubPoly_compress1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (16 * c + j) (by omega),
      hmap_getD (16 * c + j) (by omega)]
  · have hj16 : j - 8 < 8 := by omega
    simp only [hj8, hj16, lane16_neonCompress1PreShift8h]
    change neonCompress1Lane16 (lane16 (polyVecNat (seg3SubPoly inv vPoly) (2 * c + 1)) ⟨j - 8, hj16⟩) = _
    rw [polyVecNat, lane16_pack8x16]
    dsimp only
    rw [show 8 * (2 * c + 1) + (j - 8) = 16 * c + j by omega,
      seg3SubPoly_compress1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (16 * c + j) (by omega),
      hmap_getD (16 * c + j) (by omega)]

theorem bfi_ser1_eq (lo hi : BitVec 16) :
    (lo &&& 255#16) ||| ((hi &&& 65535#16) <<< 8) =
    setWidth 16 (evalBitfield .W32 .BFM (setWidth 64 lo) (setWidth 64 hi) 24 23) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  unfold evalBitfield
  dsimp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]
  simp only [show (BitfieldOp.BFM == BitfieldOp.UBFM) = false from rfl,
    show (BitfieldOp.BFM == BitfieldOp.SBFM) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬(23 ≥ 24) by decide,
    BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hk, show k < 32 by omega, show k < 64 by omega, decide_true,
    Bool.true_and]
  have hm24 : ∀ i, i < 64 → (BitVec.ofNat 64 (Nat.shiftLeft 1 24 - 1)).getLsbD i = decide (i < 24) := by
    intro i hi64; revert i hi64; decide
  have hm8 : ∀ i, i < 16 → (255#16 : BitVec 16).getLsbD i = decide (i < 8) := by
    intro i hi16; revert i hi16; decide
  have hm16 : ∀ i, i < 16 → (65535#16 : BitVec 16).getLsbD i = decide (i < 16) := by
    intro i hi16; revert i hi16; decide
  by_cases hk8 : k < 8
  · rw [hm8 k hk]; simp [hk8]
  · rw [hm8 k hk, hm24 (k - 8) (by omega), hm16 (k - 8) (by omega)]
    simp [hk8, show k - 8 < 16 by omega, show k - 8 < 24 by omega,
      show k - 8 < 32 by omega, show k - 8 < 64 by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
