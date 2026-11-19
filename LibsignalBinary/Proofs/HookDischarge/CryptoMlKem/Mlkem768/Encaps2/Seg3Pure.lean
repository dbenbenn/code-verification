/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base

/-!
# `encapsulate2` (`B20`) — Segment 3 Pure Vector & Stage Equivalences (`Seg3Pure`)

Pure 128-bit NEON vector-to-`Poly16` equivalences for Segment 3 (`+0x0bdc .. +0x10a0`):
1. `neonDot3` 3-way NTT dot-product accumulator identities (`polyZero16`, `simdAdd8h_polyVecNat`,
   `neonDot3_eq_encaps2_fold`);
2. 2-vector `ntt_multiply` inner-loop body (`nttMulVec0`, `nttMulVec1` = `polyVecNat (neonPolyNttMul16 lhs rhs)`);
3. Lower 2-stage `InvNTT` (`len = 2, 4`) vector-pair equivalences (`lowerInvNtt16` and
   `upperInvNtt16_lowerInvNtt16`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure

open Arm64 BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 zetasTimesMontgomeryR
  neonBarrettReduce16 neonMontgomeryReduce16 neonMontgomeryMul16
  neonPolyNttMul16 neonInvNttStage16 neonInvNttMontgomery16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane32 lane64 pack8x16 pack2x64 dup8x16 dup4hLow
  fin8_cases ext_lane16
  lane16_pack8x16 lane16_dup8x16
  lane16_dup4hLow_lt4 lane16_append64_lo lane16_append64_hi
  lane16_setSimdLane_16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s
  simdSmull4s simdSmlal4s
  lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h
  lane16_simdSqdmulh8h lane16_simdSshr8h
  lane16_simdTrn1_8h lane16_simdTrn2_8h
  lane32_simdTrn1_4s lane32_simdTrn2_4s
  lane32_simdSmull4s lane32_simdSmlal4s
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (polyAdd16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  butterflyStage butterflyStage_size butterflyStage_getD
  extract16_lane64 extract16_lane32_lo extract16_lane32_hi lane16_of_lane32
  simdMontMul8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  simdBarrett8h_eq_mla
  invNttLayer2VecPair lane16_invNttLayer2VecPair
  invNttLayer4VecPair lane16_invNttLayer4VecPair
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (zetaTableAt_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s simdUzp1_4s lane32_simdRev64_4s lane32_simdUzp1_4s lane16_zext32_zero
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16)

/-! ## 1. `neonDot3` & `polyAdd16` Accumulator Identities -/

@[expose] def polyZero16 : Poly16 := Array.replicate 256 0#16

@[expose] def neonDot3 (t0 t1 t2 r0 r1 r2 : Poly16) : Poly16 :=
  polyAdd16 (polyAdd16 (neonPolyNttMul16 t0 r0) (neonPolyNttMul16 t1 r1)) (neonPolyNttMul16 t2 r2)

@[simp] theorem polyZero16_size : polyZero16.size = 256 := by simp [polyZero16]
@[simp] theorem polyAdd16_size (a b : Poly16) : (polyAdd16 a b).size = 256 := by simp [polyAdd16]
@[simp] theorem neonPolyNttMul16_size (lhs rhs : Poly16) :
    (neonPolyNttMul16 lhs rhs).size = 256 := by simp [neonPolyNttMul16]
@[simp] theorem neonDot3_size (t0 t1 t2 r0 r1 r2 : Poly16) :
    (neonDot3 t0 t1 t2 r0 r1 r2).size = 256 := by simp [neonDot3]

private theorem getD_ofFn_256 {α : Type} (g : Fin 256 → α) (i : Nat) (d : α) (hi : i < 256) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  simp [Array.getD, hi]

@[simp] theorem lane16_polyVecNat (p : Poly16) (k : Nat) (i : Fin 8) :
    lane16 (polyVecNat p k) i = p.getD (8 * k + i.val) 0#16 := by
  simp [polyVecNat]

@[simp] theorem polyVecNat_polyZero16 (k : Nat) : polyVecNat polyZero16 k = 0#128 := by
  apply ext_lane16; intro i
  have hl0 : lane16 0#128 i = 0#16 := by simp [lane16]
  rw [polyVecNat, lane16_pack8x16, hl0]
  by_cases h : 8 * k + i.val < 256 <;> simp [polyZero16, Array.getD, h]

theorem polyAdd16_zero_left {p : Poly16} (hp : p.size = 256) :
    polyAdd16 polyZero16 p = p := by
  apply Array.ext
  · simp [hp]
  · intro i hi1 hi2
    simp [polyAdd16, polyZero16, Array.getD, hp]

theorem simdAdd8h_polyVecNat (a b : Poly16) (k : Nat) (hk : k < 32) :
    simdAdd8h (polyVecNat b k) (polyVecNat a k) = polyVecNat (polyAdd16 a b) k := by
  apply ext_lane16; intro i
  have hidx : 8 * k + i.val < 256 := by omega
  simp only [lane16_simdAdd8h, polyVecNat, lane16_pack8x16]
  rw [polyAdd16, getD_ofFn_256 _ _ _ hidx]
  exact BitVec.add_comm _ _

theorem neonDot3_eq_encaps2_fold (tHat rHat : Array Poly16) :
    (List.range 3).foldl
      (fun acc j =>
        let prod := neonPolyNttMul16 (tHat.getD j #[]) (rHat.getD j #[])
        Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + prod.getD i 0#16)
      (Array.replicate 256 0#16) =
    neonDot3 (tHat.getD 0 #[]) (tHat.getD 1 #[]) (tHat.getD 2 #[])
      (rHat.getD 0 #[]) (rHat.getD 1 #[]) (rHat.getD 2 #[]) := by
  have hrange : List.range 3 = [0, 1, 2] := by decide
  rw [hrange]
  simp only [List.foldl]
  change polyAdd16 (polyAdd16 (polyAdd16 polyZero16
      (neonPolyNttMul16 (tHat.getD 0 #[]) (rHat.getD 0 #[])))
      (neonPolyNttMul16 (tHat.getD 1 #[]) (rHat.getD 1 #[])))
      (neonPolyNttMul16 (tHat.getD 2 #[]) (rHat.getD 2 #[])) = _
  rw [polyAdd16_zero_left (neonPolyNttMul16_size _ _), neonDot3]

/-! ## 2. 2-Vector `ntt_multiply` Inner-Loop Equivalence (`+0x0ca0 .. +0x0d8c`) -/

@[expose] def buildZeta4 (w0 w1 w2 w3 : BitVec 64) : BitVec 128 :=
  setSimdLane
    (setSimdLane
      (setSimdLane ((w0.truncate 32).zeroExtend 128) 16 1 ((w1.truncate 16).zeroExtend 128))
      16 2 ((w2.truncate 16).zeroExtend 128))
    16 3 ((w3.truncate 16).zeroExtend 128)

theorem lane16_buildZeta4 (w0 w1 w2 w3 : BitVec 64) :
    lane16 (buildZeta4 w0 w1 w2 w3) 0 = w0.truncate 16 ∧
    lane16 (buildZeta4 w0 w1 w2 w3) 1 = w1.truncate 16 ∧
    lane16 (buildZeta4 w0 w1 w2 w3) 2 = w2.truncate 16 ∧
    lane16 (buildZeta4 w0 w1 w2 w3) 3 = w3.truncate 16 := by
  have htr : ∀ x : BitVec 16, ((x.zeroExtend 128 : BitVec 128)).truncate 16 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [buildZeta4, (lane16_setSimdLane_16 _ _ ⟨1, by omega⟩),
      (lane16_setSimdLane_16 _ _ ⟨2, by omega⟩),
      (lane16_setSimdLane_16 _ _ ⟨3, by omega⟩), htr, lane16_zext32_zero]

@[expose] def nttMulRawPair (vL0 vL1 vR0 vR1 qInv qMod z20 z21 : BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let a1 := simdTrn2_8h vL0 vL1
  let a0 := simdTrn1_8h vL0 vL1
  let b1 := simdTrn2_8h vR0 vR1
  let b0 := simdTrn1_8h vR0 vR1
  let oddLo32 := simdSmlal4s false (simdSmull4s false b0 a1) b1 a0
  let oddHi32 := simdSmlal4s true (simdSmull4s true b0 a1) b1 a0
  let a1b1 := simdSub8h (simdSshr8h (simdSqdmulh8h a1 b1) 1)
    (simdSshr8h (simdSqdmulh8h (simdMul8h (simdMul8h a1 b1) qInv) qMod) 1)
  let a1b1Hi := a1b1.truncate 64 ++ a1b1.extractLsb' 64 64
  let evenLo32 := simdSmlal4s false (simdSmull4s false a1b1 z20) b0 a0
  let evenHi32 := simdSmlal4s true (simdSmull4s false a1b1Hi z21) b0 a0
  let oddLow16 := simdTrn1_8h oddLo32 oddHi32
  let oddHigh16 := simdTrn2_8h oddLo32 oddHi32
  let evenLow16 := simdTrn1_8h evenLo32 evenHi32
  let evenHigh16 := simdTrn2_8h evenLo32 evenHi32
  let oddRed := simdSub8h oddHigh16
    (simdSshr8h (simdSqdmulh8h (simdMul8h oddLow16 qInv) qMod) 1)
  let evenRed := simdSub8h evenHigh16
    (simdSshr8h (simdSqdmulh8h (simdMul8h evenLow16 qInv) qMod) 1)
  let pLo := simdTrn1_8h evenRed oddRed
  let pHi := simdTrn2_8h evenRed oddRed
  let t0 := simdTrn1_4s pLo pHi
  let t1 := simdTrn2_4s pLo pHi
  (simdUzp1_4s t0 (simdRev64_4s t0), simdUzp1_4s t1 (simdRev64_4s t1))

private theorem extract32_lo_eq_truncate (x : BitVec 32) :
    x.extractLsb' 0 16 = x.truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]

private theorem extract32_hi_eq_ushr_truncate (x : BitVec 32) :
    x.extractLsb' 16 16 = (x >>> 16).truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]

private theorem lane16_simdSmlal4s (q : Bool) (vd vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdSmlal4s q vd vn vm) i =
      if i.val % 2 = 0 then
        (lane32 (simdSmlal4s q vd vn vm) ⟨i.val / 2, by omega⟩).truncate 16
      else
        ((lane32 (simdSmlal4s q vd vn vm) ⟨i.val / 2, by omega⟩) >>> 16).truncate 16 := by
  rw [lane16_of_lane32]
  by_cases h : i.val % 2 = 0 <;>
    simp only [h, ↓reduceIte, extract32_lo_eq_truncate, extract32_hi_eq_ushr_truncate]

private theorem lane16_ext8_lo (v : BitVec 128) (i : Fin 8) (h : i.val < 4 := by decide) :
    lane16 (v.truncate 64 ++ v.extractLsb' 64 64) i = lane16 v ⟨4 + i.val, by omega⟩ := by
  rw [lane16_append64_lo _ _ i h]
  exact extract16_lane64 v 1 i.val h

private theorem odd_prod32_comm (a0 a1 b0 b1 : BitVec 16) :
    b0.signExtend 32 * a1.signExtend 32 + b1.signExtend 32 * a0.signExtend 32 =
      a0.signExtend 32 * b1.signExtend 32 + a1.signExtend 32 * b0.signExtend 32 := by
  rw [BitVec.mul_comm (b0.signExtend 32) (a1.signExtend 32),
      BitVec.mul_comm (b1.signExtend 32) (a0.signExtend 32),
      BitVec.add_comm]

private theorem even_prod32_comm (m z a0 b0 : BitVec 16) :
    m.signExtend 32 * z.signExtend 32 + b0.signExtend 32 * a0.signExtend 32 =
      m.signExtend 32 * z.signExtend 32 + a0.signExtend 32 * b0.signExtend 32 := by
  rw [BitVec.mul_comm (b0.signExtend 32) (a0.signExtend 32)]

private theorem getD_neonPolyNttMul16 (lhs rhs : Poly16) (v c : Nat) (hv : v < 32) (hc : c < 8) :
    (neonPolyNttMul16 lhs rhs).getD (8 * v + c) 0#16 =
      let m := c / 2
      let a0 := lhs.getD (8 * v + 2 * m) 0#16
      let a1 := lhs.getD (8 * v + 2 * m + 1) 0#16
      let b0 := rhs.getD (8 * v + 2 * m) 0#16
      let b1 := rhs.getD (8 * v + 2 * m + 1) 0#16
      let baseZ := zetaTableAt (64 + (2 * v + m / 2))
      let zeta := if m % 2 == 0 then baseZ else -baseZ
      if c % 2 == 0 then
        let a1b1 := neonMontgomeryMul16 a1 b1
        let prod32 : BitVec 32 :=
          a1b1.signExtend 32 * zeta.signExtend 32 + a0.signExtend 32 * b0.signExtend 32
        neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)
      else
        let prod32 : BitVec 32 :=
          a0.signExtend 32 * b1.signExtend 32 + a1.signExtend 32 * b0.signExtend 32
        neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16) := by
  have hidx : 8 * v + c < 256 := by omega
  have hp : (8 * v + c) / 2 = 4 * v + c / 2 := by omega
  have him : (8 * v + c) % 2 = c % 2 := by omega
  have hpm : (4 * v + c / 2) % 2 = (c / 2) % 2 := by omega
  have hpd : (4 * v + c / 2) / 2 = 2 * v + (c / 2) / 2 := by omega
  have ha0 : 2 * (4 * v + c / 2) = 8 * v + 2 * (c / 2) := by omega
  have hz : zetasTimesMontgomeryR.getD (64 + (2 * v + (c / 2) / 2)) 0#16 =
      zetaTableAt (64 + (2 * v + (c / 2) / 2)) :=
    (zetaTableAt_eq _ (by omega)).symm
  rw [neonPolyNttMul16, getD_ofFn_256 _ _ _ hidx]
  dsimp only
  rw [hp, him, hpm, hpd, ha0, hz]

private def nttPairVec (vL vR : BitVec 128) (zFn : Fin 4 → BitVec 16) : BitVec 128 :=
  pack8x16 fun i =>
    let m : Fin 4 := ⟨i.val / 2, by omega⟩
    let a0 := lane16 vL ⟨2 * m.val, by omega⟩
    let a1 := lane16 vL ⟨2 * m.val + 1, by omega⟩
    let b0 := lane16 vR ⟨2 * m.val, by omega⟩
    let b1 := lane16 vR ⟨2 * m.val + 1, by omega⟩
    if i.val % 2 == 0 then
      let a1b1 := neonMontgomeryMul16 a1 b1
      let prod32 : BitVec 32 :=
        a1b1.signExtend 32 * (zFn m).signExtend 32 + a0.signExtend 32 * b0.signExtend 32
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)
    else
      let prod32 : BitVec 32 :=
        a0.signExtend 32 * b1.signExtend 32 + a1.signExtend 32 * b0.signExtend 32
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)

private theorem nttMulRawPair_lanes (vL0 vL1 vR0 vR1 z20 z21 : BitVec 128) :
    let pair := nttMulRawPair vL0 vL1 vR0 vR1 (dup8x16 62209#16) (dup8x16 3329#16) z20 z21
    pair.1 = nttPairVec vL0 vR0
      (fun m => if h : m.val < 2 then lane16 z20 ⟨2 * m.val, by omega⟩
                else lane16 z21 ⟨2 * (m.val - 2), by omega⟩) ∧
    pair.2 = nttPairVec vL1 vR1
      (fun m => if h : m.val < 2 then lane16 z20 ⟨2 * m.val + 1, by omega⟩
                else lane16 z21 ⟨2 * (m.val - 2) + 1, by omega⟩) := by
  let qInv := dup8x16 62209#16
  let qMod := dup8x16 3329#16
  let a1 := simdTrn2_8h vL0 vL1
  let a0 := simdTrn1_8h vL0 vL1
  let b1 := simdTrn2_8h vR0 vR1
  let b0 := simdTrn1_8h vR0 vR1
  have ha1b1 : simdSub8h (simdSshr8h (simdSqdmulh8h a1 b1) 1)
      (simdSshr8h (simdSqdmulh8h (simdMul8h (simdMul8h a1 b1) qInv) qMod) 1) =
      pack8x16 (fun j => neonMontgomeryMul16 (lane16 a1 j) (lane16 b1 j)) := by
    apply ext_lane16; intro j
    simp only [lane16_pack8x16, lane16_simdSub8h, lane16_simdSshr8h,
      lane16_simdSqdmulh8h, lane16_simdMul8h, qInv, qMod, lane16_dup8x16,
      neonMontgomeryMul16, neonMontgomeryReduce16]
  let a1b1P := pack8x16 (fun j => neonMontgomeryMul16 (lane16 a1 j) (lane16 b1 j))
  let a1b1Hi : BitVec 128 := a1b1P.truncate 64 ++ a1b1P.extractLsb' 64 64
  have ha1b1Hi (c : Nat) (h8 : c < 8) (hc : c < 4) :
      lane16 a1b1Hi ⟨c, h8⟩ =
        neonMontgomeryMul16 (lane16 a1 ⟨4 + c, by omega⟩) (lane16 b1 ⟨4 + c, by omega⟩) := by
    dsimp only [a1b1Hi, a1b1P]
    rw [lane16_ext8_lo _ ⟨c, h8⟩ hc, lane16_pack8x16]
  let oddLo32 := simdSmlal4s false (simdSmull4s false b0 a1) b1 a0
  let oddHi32 := simdSmlal4s true (simdSmull4s true b0 a1) b1 a0
  let evenLo32 := simdSmlal4s false (simdSmull4s false a1b1P z20) b0 a0
  let evenHi32 := simdSmlal4s true (simdSmull4s false a1b1Hi z21) b0 a0
  have hoddRed : simdSub8h (simdTrn2_8h oddLo32 oddHi32)
      (simdSshr8h (simdSqdmulh8h (simdMul8h (simdTrn1_8h oddLo32 oddHi32) qInv) qMod) 1) =
      pack8x16 (fun j =>
        let k : Fin 8 := ⟨j.val / 2 + 4 * (j.val % 2), by have := j.isLt; omega⟩
        let p32 : BitVec 32 :=
          (lane16 a0 k).signExtend 32 * (lane16 b1 k).signExtend 32 +
          (lane16 a1 k).signExtend 32 * (lane16 b0 k).signExtend 32
        neonMontgomeryReduce16 (p32.truncate 16) ((p32 >>> 16).truncate 16)) := by
    apply ext_lane16; intro j
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hj⟩ <;> try omega
    all_goals
      simp only [oddLo32, oddHi32, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [odd_prod32_comm]
  have hevenRed : simdSub8h (simdTrn2_8h evenLo32 evenHi32)
      (simdSshr8h (simdSqdmulh8h (simdMul8h (simdTrn1_8h evenLo32 evenHi32) qInv) qMod) 1) =
      pack8x16 (fun j =>
        let k : Fin 8 := ⟨j.val / 2 + 4 * (j.val % 2), by have := j.isLt; omega⟩
        let z := if j.val % 2 = 0 then lane16 z20 ⟨j.val / 2, by have := j.isLt; omega⟩
                 else lane16 z21 ⟨j.val / 2, by have := j.isLt; omega⟩
        let p32 : BitVec 32 :=
          (neonMontgomeryMul16 (lane16 a1 k) (lane16 b1 k)).signExtend 32 * z.signExtend 32 +
          (lane16 a0 k).signExtend 32 * (lane16 b0 k).signExtend 32
        neonMontgomeryReduce16 (p32.truncate 16) ((p32 >>> 16).truncate 16)) := by
    apply ext_lane16; intro j
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hj⟩ <;> try omega
    · simp only [evenLo32, evenHi32, a1b1P, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        ha1b1Hi 0 (by decide) (by decide),
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, a1b1P, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        ha1b1Hi 1 (by decide) (by decide),
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, a1b1P, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        ha1b1Hi 2 (by decide) (by decide),
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, a1b1P, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
    · simp only [evenLo32, evenHi32, qInv, qMod, lane16_pack8x16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_simdTrn1_8h, lane16_simdTrn2_8h,
        lane16_simdSmlal4s, lane32_simdSmlal4s, lane32_simdSmull4s,
        ha1b1Hi 3 (by decide) (by decide),
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
        neonMontgomeryReduce16]
      rw [even_prod32_comm]
  have hpair : nttMulRawPair vL0 vL1 vR0 vR1 qInv qMod z20 z21 =
      let oddR := pack8x16 (fun j =>
        let k : Fin 8 := ⟨j.val / 2 + 4 * (j.val % 2), by have := j.isLt; omega⟩
        let p32 : BitVec 32 :=
          (lane16 a0 k).signExtend 32 * (lane16 b1 k).signExtend 32 +
          (lane16 a1 k).signExtend 32 * (lane16 b0 k).signExtend 32
        neonMontgomeryReduce16 (p32.truncate 16) ((p32 >>> 16).truncate 16))
      let evenR := pack8x16 (fun j =>
        let k : Fin 8 := ⟨j.val / 2 + 4 * (j.val % 2), by have := j.isLt; omega⟩
        let z := if j.val % 2 = 0 then lane16 z20 ⟨j.val / 2, by have := j.isLt; omega⟩
                 else lane16 z21 ⟨j.val / 2, by have := j.isLt; omega⟩
        let p32 : BitVec 32 :=
          (neonMontgomeryMul16 (lane16 a1 k) (lane16 b1 k)).signExtend 32 * z.signExtend 32 +
          (lane16 a0 k).signExtend 32 * (lane16 b0 k).signExtend 32
        neonMontgomeryReduce16 (p32.truncate 16) ((p32 >>> 16).truncate 16))
      let pLo := simdTrn1_8h evenR oddR
      let pHi := simdTrn2_8h evenR oddR
      let t0 := simdTrn1_4s pLo pHi
      let t1 := simdTrn2_4s pLo pHi
      (simdUzp1_4s t0 (simdRev64_4s t0), simdUzp1_4s t1 (simdRev64_4s t1)) := by
    dsimp only [nttMulRawPair, qInv, qMod, a0, a1, b0, b1,
      oddLo32, oddHi32, evenLo32, evenHi32, a1b1Hi, a1b1P] at ha1b1 hoddRed hevenRed ⊢
    rw [ha1b1]
    rw [hoddRed, hevenRed]
  dsimp only [qInv, qMod] at hpair ⊢
  rw [hpair]
  constructor <;> (
    apply ext_lane16; intro i
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
    all_goals
      rw [lane16_of_lane32]
      simp only [nttPairVec, a0, a1, b0, b1,
        lane32_simdUzp1_4s, lane32_simdRev64_4s,
        lane32_simdTrn1_4s, lane32_simdTrn2_4s,
        extract16_lane32_lo, extract16_lane32_hi,
        lane16_simdTrn1_8h, lane16_simdTrn2_8h, lane16_pack8x16,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true,
        ↓reduceDIte, ↓reduceIte])

section
attribute [local irreducible] zetaTableAt

theorem nttMulRawPair_eq_polyVecNat (lhs rhs : Poly16) (r : Nat) (hr : r < 16)
    (z20 z21 : BitVec 128)
    (hz20_0 : lane16 z20 0 = zetaTableAt (64 + 4 * r))
    (hz20_1 : lane16 z20 1 = zetaTableAt (66 + 4 * r))
    (hz20_2 : lane16 z20 2 = -zetaTableAt (64 + 4 * r))
    (hz20_3 : lane16 z20 3 = -zetaTableAt (66 + 4 * r))
    (hz21_0 : lane16 z21 0 = zetaTableAt (65 + 4 * r))
    (hz21_1 : lane16 z21 1 = zetaTableAt (67 + 4 * r))
    (hz21_2 : lane16 z21 2 = -zetaTableAt (65 + 4 * r))
    (hz21_3 : lane16 z21 3 = -zetaTableAt (67 + 4 * r)) :
    let pair := nttMulRawPair
      (polyVecNat lhs (2 * r)) (polyVecNat lhs (2 * r + 1))
      (polyVecNat rhs (2 * r)) (polyVecNat rhs (2 * r + 1))
      (dup8x16 62209#16) (dup8x16 3329#16) z20 z21
    pair.1 = polyVecNat (neonPolyNttMul16 lhs rhs) (2 * r) ∧
    pair.2 = polyVecNat (neonPolyNttMul16 lhs rhs) (2 * r + 1) := by
  have hlanes := nttMulRawPair_lanes
    (polyVecNat lhs (2 * r)) (polyVecNat lhs (2 * r + 1))
    (polyVecNat rhs (2 * r)) (polyVecNat rhs (2 * r + 1)) z20 z21
  dsimp only at hlanes ⊢
  rw [hlanes.1, hlanes.2]
  have hz0 : 64 + 2 * (2 * r) = 64 + 4 * r := by omega
  have hz1 : 64 + (2 * (2 * r) + 1) = 65 + 4 * r := by omega
  have hz2 : 64 + 2 * (2 * r + 1) = 66 + 4 * r := by omega
  have hz3 : 64 + (2 * (2 * r + 1) + 1) = 67 + 4 * r := by omega
  have hz20_0' : ∀ h, lane16 z20 ⟨0, h⟩ = zetaTableAt (64 + 4 * r) := fun _ => hz20_0
  have hz20_1' : ∀ h, lane16 z20 ⟨1, h⟩ = zetaTableAt (66 + 4 * r) := fun _ => hz20_1
  have hz20_2' : ∀ h, lane16 z20 ⟨2, h⟩ = -zetaTableAt (64 + 4 * r) := fun _ => hz20_2
  have hz20_3' : ∀ h, lane16 z20 ⟨3, h⟩ = -zetaTableAt (66 + 4 * r) := fun _ => hz20_3
  have hz21_0' : ∀ h, lane16 z21 ⟨0, h⟩ = zetaTableAt (65 + 4 * r) := fun _ => hz21_0
  have hz21_1' : ∀ h, lane16 z21 ⟨1, h⟩ = zetaTableAt (67 + 4 * r) := fun _ => hz21_1
  have hz21_2' : ∀ h, lane16 z21 ⟨2, h⟩ = -zetaTableAt (65 + 4 * r) := fun _ => hz21_2
  have hz21_3' : ∀ h, lane16 z21 ⟨3, h⟩ = -zetaTableAt (67 + 4 * r) := fun _ => hz21_3
  constructor <;> (
    apply ext_lane16; intro i
    rw [lane16_polyVecNat, getD_neonPolyNttMul16 lhs rhs _ i.val (by omega) i.isLt]
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
    all_goals
      simp only [nttPairVec, lane16_pack8x16, lane16_polyVecNat,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, Nat.reduceBEq, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
        Nat.add_zero, Nat.add_assoc,
        hz20_0', hz20_1', hz20_2', hz20_3', hz21_0', hz21_1', hz21_2', hz21_3',
        hz0, hz1, hz2, hz3])

end

/-! ## 3. Lower 2-Stage `InvNTT` (`len = 2, 4`) & `upperInvNtt16` Composition -/

private def invStagePairFn (kInit : Nat) (barrettFirst : Bool) :
    Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 :=
  fun blk a b =>
    let sum := a + b
    let a' := if barrettFirst then neonBarrettReduce16 sum else sum
    let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD (kInit - blk) 0#16)
    (a', b')

private theorem neonInvNttStage16_eq_butterfly (len kInit : Nat) (barrettFirst : Bool) (p : Poly16) :
    neonInvNttStage16 len kInit barrettFirst p =
      (butterflyStage len (invStagePairFn kInit barrettFirst) 0#16 p,
       kInit - 256 / (2 * len)) := by
  unfold neonInvNttStage16 butterflyStage invStagePairFn
  exact LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt.foldl_range_stepK
    (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let sum := a + b
          let a' := if barrettFirst then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD k 0#16)
          (arr.set! j a').set! (j + len) b')
        cur)
    (· - 1) (kInit - ·) kInit (Nat.sub_zero kInit) (fun b => Nat.sub_sub kInit b 1) p

@[expose] def invNttAfterStage2 (dot : Poly16) : Poly16 :=
  (neonInvNttStage16 2 127 true dot).1

@[expose] def lowerInvNtt16 (dot : Poly16) : Poly16 :=
  (neonInvNttStage16 4 63 false (invNttAfterStage2 dot)).1

theorem invNttAfterStage2_size {dot : Poly16} (h : dot.size = 256) :
    (invNttAfterStage2 dot).size = 256 := by
  rw [invNttAfterStage2, neonInvNttStage16_eq_butterfly]; dsimp only
  exact butterflyStage_size (len := 2) (invStagePairFn 127 true) 0#16 h (by omega) ⟨64, rfl⟩

theorem lowerInvNtt16_size {dot : Poly16} (h : dot.size = 256) :
    (lowerInvNtt16 dot).size = 256 := by
  rw [lowerInvNtt16, neonInvNttStage16_eq_butterfly]; dsimp only
  exact butterflyStage_size (len := 4) (invStagePairFn 63 false) 0#16
    (invNttAfterStage2_size h) (by omega) ⟨32, rfl⟩

theorem upperInvNtt16_lowerInvNtt16 (dot : Poly16) :
    upperInvNtt16 (lowerInvNtt16 dot) = neonInvNttMontgomery16 dot := by
  have h1 := neonInvNttStage16_eq_butterfly 2 127 true dot
  have h2 := neonInvNttStage16_eq_butterfly 4 63 false (invNttAfterStage2 dot)
  unfold upperInvNtt16 lowerInvNtt16 invNttAfterStage2 neonInvNttMontgomery16 at *
  rw [h1] at h2 ⊢
  dsimp only at h2 ⊢
  rw [h2]

@[expose] def buildZetaLayer2 (w0 w2 w1 w3 : BitVec 64) : BitVec 128 :=
  setSimdLane (setSimdLane (setSimdLane (setSimdLane (setSimdLane (setSimdLane (setSimdLane
    ((w0.truncate 32).zeroExtend 128)
    16 1 ((w0.truncate 16).zeroExtend 128))
    16 2 ((w2.truncate 16).zeroExtend 128))
    16 3 ((w2.truncate 16).zeroExtend 128))
    16 4 ((w1.truncate 16).zeroExtend 128))
    16 5 ((w1.truncate 16).zeroExtend 128))
    16 6 ((w3.truncate 16).zeroExtend 128))
    16 7 ((w3.truncate 16).zeroExtend 128)

@[expose] def layer2RawPair (vLo vHi c1024 cf2ff c20159 c62209 c3329 z2 : BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let a := simdTrn1_4s vLo vHi
  let b := simdTrn2_4s vLo vHi
  let diff := simdSub8h b a
  let sum := simdAdd8h b a
  let kVec := simdMul8h (simdMul8h diff c62209) z2
  let a' := simdMla8h sum (simdSshr8h (simdAdd8h (simdSqdmulh8h sum c20159) c1024) 11) cf2ff
  let b' := simdSub8h (simdSshr8h (simdSqdmulh8h diff z2) 1)
    (simdSshr8h (simdSqdmulh8h kVec c3329) 1)
  (simdTrn1_4s a' b', simdTrn2_4s a' b')

theorem layer2RawPair_eq_polyVecNat {p : Poly16} (hp : p.size = 256) (r : Nat) (hr : r < 16) :
    let k := 127 - 4 * r
    let z2 := buildZetaLayer2
      ((zetaTableAt k).zeroExtend 64)
      ((zetaTableAt (k - 2)).zeroExtend 64)
      ((zetaTableAt (k - 1)).zeroExtend 64)
      ((zetaTableAt (k - 3)).zeroExtend 64)
    let pair := layer2RawPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1))
      (dup8x16 1024#16) (dup8x16 0xf2ff#16)
      (dup8x16 20159#16) (dup8x16 62209#16) (dup8x16 3329#16) z2
    pair.1 = polyVecNat (invNttAfterStage2 p) (2 * r) ∧
    pair.2 = polyVecNat (invNttAfterStage2 p) (2 * r + 1) := by
  intro k z2 pair
  have htr : ∀ x : BitVec 16, ((x.zeroExtend 128 : BitVec 128)).truncate 16 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]
  have htr64 : ∀ x : BitVec 16, ((x.zeroExtend 64 : BitVec 64)).truncate 16 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]
  have htr0 : ∀ x : BitVec 16, lane16 (x.zeroExtend 128) 0 = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h128 : b < 128 := by omega
    simp [lane16, hb, h128]
  have hz2 : z2 = pack8x16 (fun i =>
      if i.val / 2 = 0 then zetaTableAt k
      else if i.val / 2 = 1 then zetaTableAt (k - 2)
      else if i.val / 2 = 2 then zetaTableAt (k - 1)
      else zetaTableAt (k - 3)) := by
    apply ext_lane16
    refine fin8_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [z2, buildZetaLayer2,
        (lane16_setSimdLane_16 _ _ ⟨1, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨2, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨3, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨4, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨5, by omega⟩), (lane16_setSimdLane_16 _ _ ⟨6, by omega⟩),
        (lane16_setSimdLane_16 _ _ ⟨7, by omega⟩),
        htr, htr64, htr0, lane16_pack8x16]
  have hpair : pair = invNttLayer2VecPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) k := by
    have hcomm : simdAdd8h (simdTrn2_4s (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)))
        (simdTrn1_4s (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1))) =
      simdAdd8h (simdTrn1_4s (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)))
        (simdTrn2_4s (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1))) := by
      apply ext_lane16; intro i; simp [lane16_simdAdd8h, BitVec.add_comm]
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
    dsimp only [pair, layer2RawPair, invNttLayer2VecPair]
    rw [hz2, hcomm, simdBarrett8h_eq_mla, hmont]
  rw [hpair]
  constructor
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_invNttLayer2VecPair (k := k) (by omega) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).1,
        invNttAfterStage2, neonInvNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 2) (idx := 8 * (2 * r) + i.val)
          (invStagePairFn 127 true) 0#16 hp (by omega) ⟨64, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r) + i.val) / (2 * 2) = 4 * r + i.val / 4 := by omega
    have hmod : (8 * (2 * r) + i.val) % (2 * 2) = i.val % 4 := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val % 4 < 2
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val + 2) = 8 * (2 * r) + i.val + 2 by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val - 2) = 8 * (2 * r) + i.val - 2 by omega,
        show k - i.val / 4 = 127 - (4 * r + i.val / 4) by omega]
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_invNttLayer2VecPair (k := k) (by omega) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).2,
        invNttAfterStage2, neonInvNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 2) (idx := 8 * (2 * r + 1) + i.val)
          (invStagePairFn 127 true) 0#16 hp (by omega) ⟨64, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r + 1) + i.val) / (2 * 2) = 4 * r + 2 + i.val / 4 := by omega
    have hmod : (8 * (2 * r + 1) + i.val) % (2 * 2) = i.val % 4 := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val % 4 < 2
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val + 2) = 8 * (2 * r + 1) + i.val + 2 by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val - 2) = 8 * (2 * r + 1) + i.val - 2 by omega,
        show k - (2 + i.val / 4) = 127 - (4 * r + 2 + i.val / 4) by omega]

@[expose] def layer4RawPair (vLo vHi c62209 c3329 zLo zHi : BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let z2 := pack2x64 fun c => if c.val = 0 then lane64 zLo 0 else lane64 zHi 0
  let a := pack2x64 fun c => if c.val = 0 then lane64 vLo 0 else lane64 vHi 0
  let b := pack2x64 fun c => if c.val = 0 then lane64 vLo 1 else lane64 vHi 1
  let diff := simdSub8h b a
  let a' := simdAdd8h b a
  let kVec := simdMul8h diff (simdMul8h z2 c62209)
  let b' := simdSub8h (simdSshr8h (simdSqdmulh8h diff z2) 1)
    (simdSshr8h (simdSqdmulh8h kVec c3329) 1)
  (pack2x64 (fun c => if c.val = 0 then lane64 a' 0 else lane64 b' 0),
   pack2x64 (fun c => if c.val = 0 then lane64 a' 1 else lane64 b' 1))

theorem layer4RawPair_eq_polyVecNat {p : Poly16} (hp : p.size = 256) (r : Nat) (hr : r < 16) :
    let k := 63 - 2 * r
    let pair := layer4RawPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1))
      (dup8x16 62209#16) (dup8x16 3329#16)
      (dup4hLow (zetaTableAt k)) (dup4hLow (zetaTableAt (k - 1)))
    pair.1 = polyVecNat (neonInvNttStage16 4 63 false p).1 (2 * r) ∧
    pair.2 = polyVecNat (neonInvNttStage16 4 63 false p).1 (2 * r + 1) := by
  intro k pair
  have hdup4 : ∀ (x : BitVec 16) (n : Nat) (h8 : n < 8) (h4 : n < 4),
      lane16 (dup4hLow x) ⟨n, h8⟩ = x := fun x n h8 h4 => lane16_dup4hLow_lt4 x ⟨n, h8⟩ h4
  have hz2 : (pack2x64 fun c =>
      if c.val = 0 then lane64 (dup4hLow (zetaTableAt k)) 0
      else lane64 (dup4hLow (zetaTableAt (k - 1))) 0) =
      pack8x16 (fun i => if i.val < 4 then zetaTableAt k else zetaTableAt (k - 1)) := by
    apply ext_lane16; intro i
    rw [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt.lane16_pack2x64_sel,
        lane16_pack8x16]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte]
      exact hdup4 _ _ _ (by dsimp; omega)
    · simp only [hc, ↓reduceDIte, ↓reduceIte]
      exact hdup4 _ _ _ (by have := i.isLt; dsimp; omega)
  have hpair : pair = invNttLayer4VecPair (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) k := by
    have hcomm : ∀ x y : BitVec 128, simdAdd8h y x = simdAdd8h x y := by
      intro x y; apply ext_lane16; intro i; simp [lane16_simdAdd8h, BitVec.add_comm]
    have hmont : ∀ d z : BitVec 128,
        simdSub8h (simdSshr8h (simdSqdmulh8h d z) 1)
          (simdSshr8h (simdSqdmulh8h (simdMul8h d (simdMul8h z (dup8x16 62209#16))) (dup8x16 3329#16)) 1) =
        simdMontMul8h d z := by
      intro d z; apply ext_lane16; intro i
      simp [simdMontMul8h, neonMontgomeryMul16, neonMontgomeryReduce16,
        lane16_simdSub8h, lane16_simdSshr8h, lane16_simdSqdmulh8h, lane16_simdMul8h,
        lane16_dup8x16, lane16_pack8x16, BitVec.mul_assoc]
    dsimp only [pair, layer4RawPair, invNttLayer4VecPair]
    rw [hz2, hcomm, hmont]
  rw [hpair]
  constructor
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_invNttLayer4VecPair (k := k) (by omega) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).1,
        neonInvNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 4) (idx := 8 * (2 * r) + i.val)
          (invStagePairFn 63 false) 0#16 hp (by omega) ⟨32, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r) + i.val) / (2 * 4) = 2 * r := by omega
    have hmod : (8 * (2 * r) + i.val) % (2 * 4) = i.val := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val + 4) = 8 * (2 * r) + i.val + 4 by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r) + (i.val - 4) = 8 * (2 * r) + i.val - 4 by omega,
        show k = 63 - 2 * r from rfl]
  · apply ext_lane16; intro i; have hi := i.isLt
    rw [lane16_polyVecNat,
        (lane16_invNttLayer4VecPair (k := k) (by omega) (by omega)
          (polyVecNat p (2 * r)) (polyVecNat p (2 * r + 1)) i).2,
        neonInvNttStage16_eq_butterfly]
    dsimp only
    rw [butterflyStage_getD (len := 4) (idx := 8 * (2 * r + 1) + i.val)
          (invStagePairFn 63 false) 0#16 hp (by omega) ⟨32, rfl⟩ (by omega)]
    have hdiv : (8 * (2 * r + 1) + i.val) / (2 * 4) = 2 * r + 1 := by omega
    have hmod : (8 * (2 * r + 1) + i.val) % (2 * 4) = i.val := by omega
    dsimp only; rw [hdiv, hmod]
    by_cases hc : i.val < 4
    · simp only [hc, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val + 4) = 8 * (2 * r + 1) + i.val + 4 by omega]
    · simp only [hc, ↓reduceDIte, ↓reduceIte, invStagePairFn, lane16_polyVecNat,
        show 8 * (2 * r + 1) + (i.val - 4) = 8 * (2 * r + 1) + i.val - 4 by omega,
        show k - 1 = 63 - (2 * r + 1) by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
