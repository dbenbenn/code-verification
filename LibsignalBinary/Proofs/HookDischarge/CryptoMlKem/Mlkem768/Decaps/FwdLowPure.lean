/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt

/-!
# `decapsulate_compressed_key` (`B04`) — Pure Lower 2-Stage Forward `NTT` Equivalences (`FwdLowPure`)

Pure 128-bit NEON vector-pair equivalences for the shared lower 2 stages (`len = 4, 2`) of
`ntt_at_layer_7_and_6` (`FwdNTT1`) and `ntt_binomially_sampled_ring_element` (`FwdNTT2`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 neonMontgomeryMul16 neonMontgomeryReduce16 zetasTimesMontgomeryR)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup4hLow dup8x16 ext_lane16 fin8_cases lane16 lane16_dup4hLow_lt4 lane16_dup8x16
  lane16_pack8x16 lane16_setSimdLane_16 lane64 pack2x64 pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h lane16_simdMul8h lane16_simdSqdmulh8h lane16_simdSshr8h lane16_simdSub8h
  simdAdd8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  butterflyStage butterflyStage_getD foldl_range_stepK lane16_nttLayer2VecPair
  lane16_nttLayer4VecPair lane16_pack2x64_sel neonNttStage16 neonPolyNtt16 neonPolyNttBinomial16
  nttLayer2VecPair nttLayer4VecPair simdMontMul8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZetaLayer2 lane16_polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (
  neonNttStage16_size neonNttStage16_snd neonPolyNtt16_of_upper neonPolyNttBinomial16_of_upper
  upperFwdNtt16 upperFwdNttBinomial16)

private def fwdStagePairFn (kInit : Nat) :
    Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 :=
  fun blk a b =>
    let t := neonMontgomeryMul16 b (zetasTimesMontgomeryR.getD (kInit + blk) 0#16)
    (a + t, a - t)

private theorem neonNttStage16_eq_butterfly (len kInit : Nat) (p : Poly16) :
    neonNttStage16 len kInit p =
      (butterflyStage len (fwdStagePairFn kInit) 0#16 p, kInit + 256 / (2 * len)) := by
  unfold neonNttStage16 butterflyStage fwdStagePairFn
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let t := neonMontgomeryMul16 b (zetasTimesMontgomeryR.getD k 0#16)
          (arr.set! j (a + t)).set! (j + len) (a - t))
        cur)
    (· + 1) (kInit + ·) kInit (Nat.add_zero kInit) (fun b => (Nat.add_assoc kInit b 1).symm) p

@[expose] def fwdNttAfterStage4 (q : Poly16) : Poly16 :=
  (neonNttStage16 4 32 q).1

@[expose] def lowerFwdNtt16 (q : Poly16) : Poly16 :=
  (neonNttStage16 2 64 (fwdNttAfterStage4 q)).1

@[simp] theorem fwdNttAfterStage4_size (q : Poly16) : (fwdNttAfterStage4 q).size = q.size := by
  unfold fwdNttAfterStage4; exact neonNttStage16_size 4 32 q

@[simp] theorem lowerFwdNtt16_size (q : Poly16) : (lowerFwdNtt16 q).size = q.size := by
  unfold lowerFwdNtt16; simp [neonNttStage16_size]

theorem barrett_lowerFwdNtt16_upper (f : Poly16) :
    (lowerFwdNtt16 (upperFwdNtt16 f)).map neonBarrettReduce16 = neonPolyNtt16 f := by
  have h := neonPolyNtt16_of_upper f
  have hk : (neonNttStage16 4 32 (upperFwdNtt16 f)).2 = 64 := by rw [neonNttStage16_snd]
  dsimp only [lowerFwdNtt16, fwdNttAfterStage4] at h ⊢
  rw [hk] at h; exact h

theorem barrett_lowerFwdNtt16_upperBinomial (f : Poly16) :
    (lowerFwdNtt16 (upperFwdNttBinomial16 f)).map neonBarrettReduce16 =
      neonPolyNttBinomial16 f := by
  have h := neonPolyNttBinomial16_of_upper f
  have hk : (neonNttStage16 4 32 (upperFwdNttBinomial16 f)).2 = 64 := by rw [neonNttStage16_snd]
  dsimp only [lowerFwdNtt16, fwdNttAfterStage4] at h ⊢
  rw [hk] at h; exact h

@[expose] def fwdLayer4RawPair (vLo vHi c62209 c3329 zLo zHi : BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let b := pack2x64 fun c => if c.val = 0 then lane64 vLo 1 else lane64 vHi 1
  let a := pack2x64 fun c => if c.val = 0 then lane64 vLo 0 else lane64 vHi 0
  let z2 := pack2x64 fun c => if c.val = 0 then lane64 zLo 0 else lane64 zHi 0
  let kVec := simdMul8h (simdMul8h b c62209) z2
  let t := simdSub8h (simdSshr8h (simdSqdmulh8h b z2) 1)
    (simdSshr8h (simdSqdmulh8h kVec c3329) 1)
  let a' := simdAdd8h t a
  let b' := simdSub8h a t
  (pack2x64 (fun c => if c.val = 0 then lane64 a' 0 else lane64 b' 0),
   pack2x64 (fun c => if c.val = 0 then lane64 a' 1 else lane64 b' 1))

theorem fwdLayer4RawPair_eq_polyVecNat {p : Poly16} (hp : p.size = 256) (r : Nat) (hr : r < 16) :
    let k := 32 + 2 * r
    let pair := fwdLayer4RawPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1))
      (dup8x16 62209#16) (dup8x16 3329#16)
      (dup4hLow (zetaTableAt k)) (dup4hLow (zetaTableAt (k + 1)))
    pair.1 = polyVecNat (fwdNttAfterStage4 p) (2 * r) ∧
    pair.2 = polyVecNat (fwdNttAfterStage4 p) (2 * r + 1) := by
  intro k pair
  have hz2 : (pack2x64 fun c =>
      if c.val = 0 then lane64 (dup4hLow (zetaTableAt k)) 0
      else lane64 (dup4hLow (zetaTableAt (k + 1))) 0) =
      pack8x16 (fun i => if i.val < 4 then zetaTableAt k else zetaTableAt (k + 1)) := by
    apply ext_lane16; intro i
    rw [lane16_pack2x64_sel, lane16_pack8x16]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte]; exact lane16_dup4hLow_lt4 _ ⟨_, _⟩ (by dsimp; omega)
    · simp only [hc, ↓reduceDIte, ↓reduceIte]
      exact lane16_dup4hLow_lt4 _ ⟨_, _⟩ (by have := i.isLt; dsimp; omega)
  have hpair : pair = nttLayer4VecPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) k := by
    have hcomm : ∀ x y : BitVec 128, simdAdd8h y x = simdAdd8h x y := by
      intro x y; apply ext_lane16; intro i; simp [lane16_simdAdd8h, BitVec.add_comm]
    have hmul : ∀ x z : BitVec 16, x * 62209#16 * z = x * z * 62209#16 := fun x z => by
      rw [BitVec.mul_assoc, BitVec.mul_comm 62209#16 z, ← BitVec.mul_assoc]
    have hmont : ∀ d z : BitVec 128,
        simdSub8h (simdSshr8h (simdSqdmulh8h d z) 1)
          (simdSshr8h (simdSqdmulh8h (simdMul8h (simdMul8h d (dup8x16 62209#16)) z) (dup8x16 3329#16)) 1) =
        simdMontMul8h d z := by
      intro d z; apply ext_lane16; intro i
      simp [simdMontMul8h, neonMontgomeryMul16, neonMontgomeryReduce16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_pack8x16, hmul]
    dsimp only [pair, fwdLayer4RawPair, nttLayer4VecPair]
    rw [hz2, hmont, hcomm]
  rw [hpair]
  constructor
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_nttLayer4VecPair (k := k) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).1,
        fwdNttAfterStage4, neonNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 4) (idx := 8 * (2 * r) + i.val)
          (fwdStagePairFn 32) 0#16 hp (by omega) ⟨32, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r) + i.val) / (2 * 4) = 2 * r := by omega
    have hmod : (8 * (2 * r) + i.val) % (2 * 4) = i.val := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val + 4) = 8 * (2 * r) + i.val + 4 by omega,
        show k = 32 + 2 * r from rfl]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val - 4) = 8 * (2 * r) + i.val - 4 by omega,
        show k = 32 + 2 * r from rfl]
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_nttLayer4VecPair (k := k) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).2,
        fwdNttAfterStage4, neonNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 4) (idx := 8 * (2 * r + 1) + i.val)
          (fwdStagePairFn 32) 0#16 hp (by omega) ⟨32, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r + 1) + i.val) / (2 * 4) = 2 * r + 1 := by omega
    have hmod : (8 * (2 * r + 1) + i.val) % (2 * 4) = i.val := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val + 4) = 8 * (2 * r + 1) + i.val + 4 by omega,
        show k + 1 = 32 + (2 * r + 1) by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val - 4) = 8 * (2 * r + 1) + i.val - 4 by omega,
        show k + 1 = 32 + (2 * r + 1) by omega]

@[expose] def fwdLayer2RawPair (vLo vHi c62209 c3329 z2 : BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let b := simdTrn2_4s vLo vHi
  let a := simdTrn1_4s vLo vHi
  let kVec := simdMul8h (simdMul8h b c62209) z2
  let t := simdSub8h (simdSshr8h (simdSqdmulh8h b z2) 1)
    (simdSshr8h (simdSqdmulh8h kVec c3329) 1)
  let b' := simdSub8h a t
  let a' := simdAdd8h t a
  (simdTrn1_4s a' b', simdTrn2_4s a' b')

theorem fwdLayer2RawPair_eq_polyVecNat {q : Poly16} (hq : q.size = 256) (r : Nat) (hr : r < 16) :
    let k := 64 + 4 * r
    let z2 := buildZetaLayer2
      ((zetaTableAt k).zeroExtend 64)
      ((zetaTableAt (k + 2)).zeroExtend 64)
      ((zetaTableAt (k + 1)).zeroExtend 64)
      ((zetaTableAt (k + 3)).zeroExtend 64)
    let pair := fwdLayer2RawPair (polyVecNat q (2 * r)) (polyVecNat q (2 * r + 1))
      (dup8x16 62209#16) (dup8x16 3329#16) z2
    pair.1 = polyVecNat (neonNttStage16 2 64 q).1 (2 * r) ∧
    pair.2 = polyVecNat (neonNttStage16 2 64 q).1 (2 * r + 1) := by
  intro k z2 pair
  have htr : ∀ x : BitVec 16, ((x.zeroExtend 128 : BitVec 128)).truncate 16 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]
  have htr64 : ∀ x : BitVec 16, ((x.zeroExtend 64 : BitVec 64)).truncate 16 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]
  have htr0 : ∀ x : BitVec 16, lane16 (x.zeroExtend 128) 0 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane16, hb]; omega
  have hz2 : z2 = pack8x16 (fun i =>
      if i.val / 2 = 0 then zetaTableAt k
      else if i.val / 2 = 1 then zetaTableAt (k + 2)
      else if i.val / 2 = 2 then zetaTableAt (k + 1)
      else zetaTableAt (k + 3)) := by
    apply ext_lane16
    refine fin8_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [z2, buildZetaLayer2,
        (lane16_setSimdLane_16 _ _ ⟨1, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨2, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨3, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨4, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨5, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨6, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨7, by omega⟩),
        htr, htr64, htr0, lane16_pack8x16]
  have hpair : pair = nttLayer2VecPair (polyVecNat q (2 * r)) (polyVecNat q (2 * r + 1)) k := by
    have hcomm : ∀ x y : BitVec 128, simdAdd8h y x = simdAdd8h x y := by
      intro x y; apply ext_lane16; intro i; simp [lane16_simdAdd8h, BitVec.add_comm]
    have hmul : ∀ x z : BitVec 16, x * 62209#16 * z = x * z * 62209#16 := fun x z => by
      rw [BitVec.mul_assoc, BitVec.mul_comm 62209#16 z, ← BitVec.mul_assoc]
    have hmont : ∀ d z : BitVec 128,
        simdSub8h (simdSshr8h (simdSqdmulh8h d z) 1)
          (simdSshr8h (simdSqdmulh8h (simdMul8h (simdMul8h d (dup8x16 62209#16)) z) (dup8x16 3329#16)) 1) =
        simdMontMul8h d z := by
      intro d z; apply ext_lane16; intro i
      simp [simdMontMul8h, neonMontgomeryMul16, neonMontgomeryReduce16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_pack8x16, hmul]
    dsimp only [pair, fwdLayer2RawPair, nttLayer2VecPair]
    rw [hz2, hmont, hcomm]
  rw [hpair]
  constructor
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_nttLayer2VecPair (k := k) (by omega)
          (polyVecNat q (2 * r)) (polyVecNat q (2 * r + 1)) i).1,
        neonNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 2) (idx := 8 * (2 * r) + i.val)
          (fwdStagePairFn 64) 0#16 hq (by omega) ⟨64, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r) + i.val) / (2 * 2) = 4 * r + i.val / 4 := by omega
    have hmod : (8 * (2 * r) + i.val) % (2 * 2) = i.val % 4 := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val % 4 < 2
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val + 2) = 8 * (2 * r) + i.val + 2 by omega,
        show k + i.val / 4 = 64 + (4 * r + i.val / 4) by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val - 2) = 8 * (2 * r) + i.val - 2 by omega,
        show k + i.val / 4 = 64 + (4 * r + i.val / 4) by omega]
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_nttLayer2VecPair (k := k) (by omega)
          (polyVecNat q (2 * r)) (polyVecNat q (2 * r + 1)) i).2,
        neonNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 2) (idx := 8 * (2 * r + 1) + i.val)
          (fwdStagePairFn 64) 0#16 hq (by omega) ⟨64, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r + 1) + i.val) / (2 * 2) = 4 * r + 2 + i.val / 4 := by omega
    have hmod : (8 * (2 * r + 1) + i.val) % (2 * 2) = i.val % 4 := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val % 4 < 2
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val + 2) = 8 * (2 * r + 1) + i.val + 2 by omega,
        show k + (2 + i.val / 4) = 64 + (4 * r + 2 + i.val / 4) by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, fwdStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val - 2) = 8 * (2 * r + 1) + i.val - 2 by omega,
        show k + (2 + i.val / 4) = 64 + (4 * r + 2 + i.val / 4) by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
