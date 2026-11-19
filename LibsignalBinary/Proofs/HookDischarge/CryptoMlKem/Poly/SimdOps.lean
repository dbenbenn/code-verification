/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import

/-!
# AdvSIMD `8H` / `4S` / `2D` / `16B` Primitives and Lane Distributivity (`Poly.SimdOps`)

Explicit 128-bit NEON vector operations (`simdAdd8h`, `simdSub8h`, `simdMul8h`, `simdMla8h`,
`simdMls8h`, `simdSqdmulh8h`, `simdSqdmulh4s`, `simdSshr8h`, `simdUshr8h`, `simdShl8h`,
`simdSshl8h`, `simdUshl8h`, `simdSli4s`, `simdSli2d`, `simdCmhs8h`, `simdCmge8h`,
`simdCmeqZero8h`, `simdCmltZero8h`, `simdTbl16b`, `simdExt16b`, `simdRev64_8h`, `simdTrn1_8h`,
`simdTrn2_8h`, `simdTrn1_4s`, `simdTrn2_4s`, `simdUzp1_8h`, `simdUzp2_8h`, `simdZip1_8h`,
`simdZip2_8h`, `simdSmull4s`, `simdSmlal4s`, `simdUmull4s`, `simdUminv8h`) and `@[simp]`
lane-wise distributivity lemmas.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sqdmulh16 sqdmulh32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane8 lane16 lane32 lane64 pack16x8 pack8x16 pack4x32 pack2x64 fin8_cases
)

/-! ## 1. Vector Primitive Definitions -/

@[expose] def simdAdd8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vn i + lane16 vm i
@[expose] def simdSub8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vn i - lane16 vm i
@[expose] def simdMul8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vn i * lane16 vm i
@[expose] def simdMla8h (vd vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vd i + lane16 vn i * lane16 vm i
@[expose] def simdMls8h (vd vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vd i - lane16 vn i * lane16 vm i
@[expose] def simdSqdmulh8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => sqdmulh16 (lane16 vn i) (lane16 vm i)
@[expose] def simdSqdmulh4s (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i => sqdmulh32 (lane32 vn i) (lane32 vm i)
@[expose] def simdSshr8h (vn : BitVec 128) (shift : Nat) : BitVec 128 :=
  pack8x16 fun i => (lane16 vn i).sshiftRight shift
@[expose] def simdUshr8h (vn : BitVec 128) (shift : Nat) : BitVec 128 :=
  pack8x16 fun i => lane16 vn i >>> shift
@[expose] def simdShl8h (vn : BitVec 128) (shift : Nat) : BitVec 128 :=
  pack8x16 fun i => lane16 vn i <<< shift

@[expose] def simdSshlElem16 (x sh : BitVec 16) : BitVec 16 :=
  let s := (sh.truncate 8).toInt
  if s ≥ 0 then x <<< s.toNat else x.sshiftRight (-s).toNat
@[expose] def simdSshl8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => simdSshlElem16 (lane16 vn i) (lane16 vm i)

@[expose] def simdUshlElem16 (x sh : BitVec 16) : BitVec 16 :=
  let s := (sh.truncate 8).toInt
  if s ≥ 0 then x <<< s.toNat else x >>> (-s).toNat
@[expose] def simdUshl8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => simdUshlElem16 (lane16 vn i) (lane16 vm i)

@[expose] def simdSli4s (vd vn : BitVec 128) (shift : Nat) : BitVec 128 :=
  let mask : BitVec 32 := (1#32 <<< shift) - 1#32
  pack4x32 fun i => (lane32 vd i &&& mask) ||| (lane32 vn i <<< shift)
@[expose] def simdSli2d (vd vn : BitVec 128) (shift : Nat) : BitVec 128 :=
  let mask : BitVec 64 := (1#64 <<< shift) - 1#64
  pack2x64 fun i => (lane64 vd i &&& mask) ||| (lane64 vn i <<< shift)

@[expose] def simdCmhs8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if (lane16 vm i).toNat ≤ (lane16 vn i).toNat then 0xffff#16 else 0#16
@[expose] def simdCmge8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if (lane16 vm i).toInt ≤ (lane16 vn i).toInt then 0xffff#16 else 0#16
@[expose] def simdCmeqZero8h (vn : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if lane16 vn i == 0#16 then 0xffff#16 else 0#16
@[expose] def simdCmltZero8h (vn : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if (lane16 vn i).toInt < 0 then 0xffff#16 else 0#16

@[expose] def simdTbl16b (vn vm : BitVec 128) : BitVec 128 :=
  pack16x8 fun i => let idx := (lane8 vm i).toNat; if h : idx < 16 then lane8 vn ⟨idx, h⟩ else 0#8
@[expose] def simdExt16b (vn vm : BitVec 128) (imm : Nat) : BitVec 128 :=
  pack16x8 fun i =>
    let k := i.val + imm
    if h : k < 16 then lane8 vn ⟨k, h⟩
    else if h2 : k - 16 < 16 then lane8 vm ⟨k - 16, h2⟩ else 0#8

@[expose] def simdRev64_8h (vn : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => lane16 vn ⟨(i.val / 4) * 4 + (3 - i.val % 4), by omega⟩
@[expose] def simdTrn1_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    let b : Fin 8 := ⟨(i.val / 2) * 2, by omega⟩
    if i.val % 2 == 0 then lane16 vn b else lane16 vm b
@[expose] def simdTrn2_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    let b : Fin 8 := ⟨(i.val / 2) * 2 + 1, by omega⟩
    if i.val % 2 == 0 then lane16 vn b else lane16 vm b
@[expose] def simdTrn1_4s (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    let b : Fin 4 := ⟨(i.val / 2) * 2, by omega⟩
    if i.val % 2 == 0 then lane32 vn b else lane32 vm b
@[expose] def simdTrn2_4s (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    let b : Fin 4 := ⟨(i.val / 2) * 2 + 1, by omega⟩
    if i.val % 2 == 0 then lane32 vn b else lane32 vm b
@[expose] def simdUzp1_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    if h : i.val < 4 then lane16 vn ⟨2 * i.val, by omega⟩
    else lane16 vm ⟨2 * (i.val - 4), by omega⟩
@[expose] def simdUzp2_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    if h : i.val < 4 then lane16 vn ⟨2 * i.val + 1, by omega⟩
    else lane16 vm ⟨2 * (i.val - 4) + 1, by omega⟩
@[expose] def simdZip1_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    let k : Fin 8 := ⟨i.val / 2, by omega⟩
    if i.val % 2 == 0 then lane16 vn k else lane16 vm k
@[expose] def simdZip2_8h (vn vm : BitVec 128) : BitVec 128 :=
  pack8x16 fun i =>
    let k : Fin 8 := ⟨4 + i.val / 2, by omega⟩
    if i.val % 2 == 0 then lane16 vn k else lane16 vm k

@[expose] def simdSmull4s (q : Bool) (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
    (lane16 vn idx).signExtend 32 * (lane16 vm idx).signExtend 32
@[expose] def simdSmlal4s (q : Bool) (vd vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
    lane32 vd i + (lane16 vn idx).signExtend 32 * (lane16 vm idx).signExtend 32
@[expose] def simdUmull4s (q : Bool) (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
    (lane16 vn idx).zeroExtend 32 * (lane16 vm idx).zeroExtend 32

@[expose] def umin16 (a b : BitVec 16) : BitVec 16 := if a.toNat ≤ b.toNat then a else b
@[expose] def simdUminv8h (vn : BitVec 128) : BitVec 16 :=
  umin16 (umin16 (umin16 (lane16 vn 0) (lane16 vn 1)) (umin16 (lane16 vn 2) (lane16 vn 3)))
         (umin16 (umin16 (lane16 vn 4) (lane16 vn 5)) (umin16 (lane16 vn 6) (lane16 vn 7)))

/-! ## 2. `@[simp]` Lane-Wise Distributivity & Reduction Lemmas -/

@[simp] theorem lane16_and (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (vn &&& vm) i = lane16 vn i &&& lane16 vm i := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [lane16, hb]
@[simp] theorem lane16_orr (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (vn ||| vm) i = lane16 vn i ||| lane16 vm i := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [lane16, hb]
@[simp] theorem lane16_eor (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (vn ^^^ vm) i = lane16 vn i ^^^ lane16 vm i := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [lane16, hb]
@[simp] theorem lane16_not (vn : BitVec 128) (i : Fin 8) :
    lane16 (~~~vn) i = ~~~(lane16 vn i) := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hlt : 16 * i.val + b < 128 := by omega
  simp [lane16, hb, hlt]

@[simp] theorem lane16_simdAdd8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdAdd8h vn vm) i = lane16 vn i + lane16 vm i := by simp [simdAdd8h]
@[simp] theorem lane16_simdSub8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdSub8h vn vm) i = lane16 vn i - lane16 vm i := by simp [simdSub8h]
@[simp] theorem lane16_simdMul8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdMul8h vn vm) i = lane16 vn i * lane16 vm i := by simp [simdMul8h]
@[simp] theorem lane16_simdMla8h (vd vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdMla8h vd vn vm) i = lane16 vd i + lane16 vn i * lane16 vm i := by simp [simdMla8h]
@[simp] theorem lane16_simdMls8h (vd vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdMls8h vd vn vm) i = lane16 vd i - lane16 vn i * lane16 vm i := by simp [simdMls8h]
@[simp] theorem lane16_simdSqdmulh8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdSqdmulh8h vn vm) i = sqdmulh16 (lane16 vn i) (lane16 vm i) := by
  simp [simdSqdmulh8h]
@[simp] theorem lane32_simdSqdmulh4s (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdSqdmulh4s vn vm) i = sqdmulh32 (lane32 vn i) (lane32 vm i) := by
  simp [simdSqdmulh4s]
@[simp] theorem lane16_simdSshr8h (vn : BitVec 128) (shift : Nat) (i : Fin 8) :
    lane16 (simdSshr8h vn shift) i = (lane16 vn i).sshiftRight shift := by simp [simdSshr8h]
@[simp] theorem lane16_simdUshr8h (vn : BitVec 128) (shift : Nat) (i : Fin 8) :
    lane16 (simdUshr8h vn shift) i = lane16 vn i >>> shift := by simp [simdUshr8h]
@[simp] theorem lane16_simdShl8h (vn : BitVec 128) (shift : Nat) (i : Fin 8) :
    lane16 (simdShl8h vn shift) i = lane16 vn i <<< shift := by simp [simdShl8h]
@[simp] theorem lane16_simdSshl8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdSshl8h vn vm) i = simdSshlElem16 (lane16 vn i) (lane16 vm i) := by
  simp [simdSshl8h]
@[simp] theorem lane16_simdUshl8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdUshl8h vn vm) i = simdUshlElem16 (lane16 vn i) (lane16 vm i) := by
  simp [simdUshl8h]

@[simp] theorem lane32_simdSli4s (vd vn : BitVec 128) (shift : Nat) (i : Fin 4) :
    lane32 (simdSli4s vd vn shift) i =
      (lane32 vd i &&& ((1#32 <<< shift) - 1#32)) ||| (lane32 vn i <<< shift) := by
  simp [simdSli4s]
@[simp] theorem lane64_simdSli2d (vd vn : BitVec 128) (shift : Nat) (i : Fin 2) :
    lane64 (simdSli2d vd vn shift) i =
      (lane64 vd i &&& ((1#64 <<< shift) - 1#64)) ||| (lane64 vn i <<< shift) := by
  simp [simdSli2d]

@[simp] theorem lane16_simdCmhs8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdCmhs8h vn vm) i =
      if (lane16 vm i).toNat ≤ (lane16 vn i).toNat then 0xffff#16 else 0#16 := by
  simp [simdCmhs8h]
@[simp] theorem lane16_simdCmge8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdCmge8h vn vm) i =
      if (lane16 vm i).toInt ≤ (lane16 vn i).toInt then 0xffff#16 else 0#16 := by
  simp [simdCmge8h]
@[simp] theorem lane16_simdCmeqZero8h (vn : BitVec 128) (i : Fin 8) :
    lane16 (simdCmeqZero8h vn) i = if lane16 vn i == 0#16 then 0xffff#16 else 0#16 := by
  simp [simdCmeqZero8h]
@[simp] theorem lane16_simdCmltZero8h (vn : BitVec 128) (i : Fin 8) :
    lane16 (simdCmltZero8h vn) i = if (lane16 vn i).toInt < 0 then 0xffff#16 else 0#16 := by
  simp [simdCmltZero8h]

@[simp] theorem lane16_simdRev64_8h (vn : BitVec 128) (i : Fin 8) :
    lane16 (simdRev64_8h vn) i = lane16 vn ⟨(i.val / 4) * 4 + (3 - i.val % 4), by omega⟩ := by
  simp [simdRev64_8h]
@[simp] theorem lane16_simdTrn1_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdTrn1_8h vn vm) i =
      if i.val % 2 == 0 then lane16 vn ⟨(i.val / 2) * 2, by omega⟩
      else lane16 vm ⟨(i.val / 2) * 2, by omega⟩ := by simp [simdTrn1_8h]
@[simp] theorem lane16_simdTrn2_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdTrn2_8h vn vm) i =
      if i.val % 2 == 0 then lane16 vn ⟨(i.val / 2) * 2 + 1, by omega⟩
      else lane16 vm ⟨(i.val / 2) * 2 + 1, by omega⟩ := by simp [simdTrn2_8h]
@[simp] theorem lane32_simdTrn1_4s (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdTrn1_4s vn vm) i =
      if i.val % 2 == 0 then lane32 vn ⟨(i.val / 2) * 2, by omega⟩
      else lane32 vm ⟨(i.val / 2) * 2, by omega⟩ := by simp [simdTrn1_4s]
@[simp] theorem lane32_simdTrn2_4s (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdTrn2_4s vn vm) i =
      if i.val % 2 == 0 then lane32 vn ⟨(i.val / 2) * 2 + 1, by omega⟩
      else lane32 vm ⟨(i.val / 2) * 2 + 1, by omega⟩ := by simp [simdTrn2_4s]
@[simp] theorem lane16_simdUzp1_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdUzp1_8h vn vm) i =
      if h : i.val < 4 then lane16 vn ⟨2 * i.val, by omega⟩
      else lane16 vm ⟨2 * (i.val - 4), by omega⟩ := by simp [simdUzp1_8h]
@[simp] theorem lane16_simdUzp2_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdUzp2_8h vn vm) i =
      if h : i.val < 4 then lane16 vn ⟨2 * i.val + 1, by omega⟩
      else lane16 vm ⟨2 * (i.val - 4) + 1, by omega⟩ := by simp [simdUzp2_8h]
@[simp] theorem lane16_simdZip1_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdZip1_8h vn vm) i =
      if i.val % 2 == 0 then lane16 vn ⟨i.val / 2, by omega⟩
      else lane16 vm ⟨i.val / 2, by omega⟩ := by simp [simdZip1_8h]
@[simp] theorem lane16_simdZip2_8h (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdZip2_8h vn vm) i =
      if i.val % 2 == 0 then lane16 vn ⟨4 + i.val / 2, by omega⟩
      else lane16 vm ⟨4 + i.val / 2, by omega⟩ := by simp [simdZip2_8h]

@[simp] theorem lane32_simdSmull4s (q : Bool) (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdSmull4s q vn vm) i =
      let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
      (lane16 vn idx).signExtend 32 * (lane16 vm idx).signExtend 32 := by simp [simdSmull4s]
@[simp] theorem lane32_simdSmlal4s (q : Bool) (vd vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdSmlal4s q vd vn vm) i =
      let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
      lane32 vd i + (lane16 vn idx).signExtend 32 * (lane16 vm idx).signExtend 32 := by
  simp [simdSmlal4s]
@[simp] theorem lane32_simdUmull4s (q : Bool) (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdUmull4s q vn vm) i =
      let idx : Fin 8 := if q then ⟨4 + i.val, by omega⟩ else ⟨i.val, by omega⟩
      (lane16 vn idx).zeroExtend 32 * (lane16 vm idx).zeroExtend 32 := by simp [simdUmull4s]

/-- `CMLT Vd.8H, Vn.8H, #0` equals lane-wise arithmetic right shift by `15`. -/
theorem lane16_simdCmltZero8h_eq_sshiftRight15 (vn : BitVec 128) (i : Fin 8) :
    lane16 (simdCmltZero8h vn) i = (lane16 vn i).sshiftRight 15 := by
  rw [lane16_simdCmltZero8h]
  let x := lane16 vn i
  change (if x.toInt < 0 then 0xffff#16 else 0#16) = x.sshiftRight 15
  have hneg : x.toInt < 0 ↔ x.msb = true := by
    have := x.isLt
    rw [BitVec.toInt_eq_msb_cond]
    (cases x.msb <;> simp); omega
  have hall1 : ∀ b (hb : b < 16), (0xffff#16)[b]'hb = true := by decide
  have hmsb15 : x[15] = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem]
  ext b hb
  by_cases hm : x.msb = true
  · simp only [hneg.mpr hm, ↓reduceIte, hall1 b hb, BitVec.getElem_sshiftRight]
    by_cases h0 : b = 0
    · subst h0; simp [hmsb15, hm]
    · have hge : ¬ (15 + b < 16) := by omega
      simp [hge, hm]
  · have hf : ¬ (x.toInt < 0) := fun h => hm (hneg.mp h)
    have hmf : x.msb = false := Bool.eq_false_iff.mpr hm
    simp only [hf, ↓reduceIte, BitVec.getElem_zero, BitVec.getElem_sshiftRight]
    by_cases h0 : b = 0
    · subst h0; simp [hmsb15, hmf]
    · have hge : ¬ (15 + b < 16) := by omega
      simp [hge, hmf]

private theorem umin16_eq_allOnes_iff (a b : BitVec 16) :
    umin16 a b = 0xffff#16 ↔ a = 0xffff#16 ∧ b = 0xffff#16 := by
  unfold umin16
  constructor
  · intro h
    have ha := a.isLt; have hb := b.isLt
    by_cases hle : a.toNat ≤ b.toNat
    · rw [ite_eq_left_iff.mpr (fun hn => absurd hle hn)] at h
      subst h
      refine ⟨rfl, BitVec.eq_of_toNat_eq ?_⟩
      simp only [BitVec.toNat_ofNat] at hle ⊢; omega
    · rw [ite_eq_right_iff.mpr (fun hy => absurd hy hle)] at h
      subst h
      simp only [BitVec.toNat_ofNat] at hle; omega
  · rintro ⟨rfl, rfl⟩; simp

theorem simdUminv8h_eq_allOnes_iff (vn : BitVec 128) :
    simdUminv8h vn = 0xffff#16 ↔ ∀ i : Fin 8, lane16 vn i = 0xffff#16 := by
  simp only [simdUminv8h, umin16_eq_allOnes_iff]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨h4, h5⟩, ⟨h6, h7⟩⟩⟩ i
    exact fin8_cases (P := fun j => lane16 vn j = 0xffff#16) h0 h1 h2 h3 h4 h5 h6 h7 i
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, ⟨h 2, h 3⟩⟩, ⟨⟨h 4, h 5⟩, ⟨h 6, h 7⟩⟩⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
