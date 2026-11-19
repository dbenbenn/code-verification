/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Main Loop

**Checked by Lean.**

Proves the evaluation and interpolation loop (`0x6bda4..0x6c0fc`, `+548..+1404`) of
`decoded_message` (`decodedMessageLoop_wpp`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName LagrangePrepareArgs lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack lagrangePrepare_placed_ok polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AddChunkNorm.sp_setPC_pre AddChunkNorm.sp_setMem_setPC_pre
  AddChunkNorm.readReg64_setPC_pre AddChunkNorm.readReg64_setMem_setPC_pre
  AddChunkNorm.readReg32_setPC_pre AddChunkNorm.readReg32_setMem_setPC_pre
  AddChunkNorm.readReg_setPC_pre AddChunkNorm.readReg_setMem_setPC_pre

/-! ## Pure Characterizations of `decodedMessageLoopTotal` Steps -/

theorem collectedSlices_getD_eq_take (self : PolyDecoder) (hpts : self.pts.length = 16)
    {k : Nat} (hk : k < 16) :
    (collectedSlices self 0 16)[k]?.getD [] =
      (self.pts[k]'(by omega)).vec.take (self.necessaryPoints k) := by
  have hk_len : k < (collectedSlices self 0 16).length := by
    rw [collectedSlices_length]; exact hk
  have hk_pts : k < self.pts.length := by omega
  rw [List.getElem?_eq_getElem hk_len, Option.getD_some,
    collectedSlices_getElem self 16 0 k hk, Nat.zero_add,
    List.getElem?_eq_getElem hk_pts, Option.getD_some]

theorem decodedMessageLoopTotal_step_found (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)} {out : List (BitVec 8)}
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hfound : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = true) :
    decodedMessageLoopTotal self (collectedSlices self 0 16) i (rem + 1) polys out =
      decodedMessageLoopTotal self (collectedSlices self 0 16) (i + 1) rem polys
        (out ++ u16ToBeBytes
          ((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).y.value) := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16) then _ else _) at hbs
  simp only [hfound, ite_true] at hbs
  have hget_b : (self.pts[i % 16]'hpoly_pts).vec[bIdx]?.getD { x := GF16.ZERO, y := GF16.ZERO } =
      (self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  conv_lhs => rw [decodedMessageLoopTotal]
  simp only [hget_pts, hbs, hget_b]

theorem decodedMessageLoopTotal_step_not_found (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)} {out : List (BitVec 8)}
    (hpolys : polys.length = 16)
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hnot_found : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = false) :
    let poly := i % 16
    let hpoly_pts : poly < self.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let hpoly_p : poly < polys.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let ptsSlice := (self.pts[poly]'hpoly_pts).vec.take (self.necessaryPoints poly)
    let p := (polys[poly]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
    let y := computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))
    decodedMessageLoopTotal self (collectedSlices self 0 16) i (rem + 1) polys out =
      decodedMessageLoopTotal self (collectedSlices self 0 16) (i + 1) rem
        (polys.set poly (some p)) (out ++ u16ToBeBytes y.value) := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hpoly_p : i % 16 < polys.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16) then _ else _) at hbs
  simp only [hnot_found, Bool.false_eq_true, ite_false] at hbs
  have hget_p : polys[i % 16]?.getD none = polys[i % 16]'hpoly_p := by
    rw [List.getElem?_eq_getElem hpoly_p, Option.getD_some]
  have hget_slice := collectedSlices_getD_eq_take self hpts hpoly_lt
  dsimp only
  conv_lhs => rw [decodedMessageLoopTotal]
  simp only [hget_pts, hbs, hget_p, hget_slice]
  cases hopt : polys[i % 16]'hpoly_p with
  | some p0 =>
    have hset_self : polys.set (i % 16) (some p0) = polys := by
      rw [← hopt, List.set_getElem_self]
    simp only [Option.getD_some, hset_self]
  | none =>
    simp only [Option.getD_none]

/-! ## Bitvector and Separation-Logic Helpers for the Main Loop -/

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub120 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551496#64 = sp0 - 216#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub112 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551504#64 = sp0 - 208#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub104 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551512#64 = sp0 - 200#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_and15_ofNat (i : Nat) :
    (BitVec.ofNat 64 i) &&& 15#64 = BitVec.ofNat 64 (i % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (i % 18446744073709551616) &&& 15 = (i % 16) % 18446744073709551616
  have h1 : (i % 18446744073709551616) &&& 15 = (i % 18446744073709551616) % 16 :=
    Nat.and_two_pow_sub_one_eq_mod _ 4
  have h2 : (i % 18446744073709551616) % 16 = i % 16 :=
    Nat.mod_mod_of_dvd i (by decide)
  have h3 : (i % 16) % 18446744073709551616 = i % 16 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt i (by decide : 0 < 16); omega)
  rw [h1, h2, h3]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_umaddl24_mod16 (base : BitVec 64) (i : Nat) :
    base + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (i % 16))) * 24#64 =
      base + BitVec.ofNat 64 (24 * (i % 16)) := by
  have hlt : i % 16 < 16 := Nat.mod_lt i (by decide)
  generalize i % 16 = m at hlt ⊢
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m)) = BitVec.ofNat 64 m := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [h1, bv64_madd24_norm]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_ofNat_mul2_comm (n : Nat) :
    BitVec.ofNat 64 (n * 2) = BitVec.ofNat 64 (2 * n) := by
  rw [Nat.mul_comm]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_ofNat_one_add_mul2 (n : Nat) :
    BitVec.ofNat 64 (1 + 2 * n) = BitVec.ofNat 64 (2 * n + 1) := by
  rw [Nat.add_comm]

theorem bv64_lsr4_ofNat {i : Nat} (hi : i < 2 ^ 64) :
    (BitVec.ofNat 64 i) >>> 4 = BitVec.ofNat 64 (i / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv32_lsr4_zeroExtend_ofNat {i : Nat} (hi : i < 16 * 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 i) >>> 4)) =
      BitVec.setWidth 64 (BitVec.ofNat 16 (i / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem bv64_lsr4_truncate16_ofNat {i : Nat} (hi : i < 16 * 65536) :
    BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) = BitVec.ofNat 16 (i / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv16_bne_zeroExtend32 (a b : BitVec 16) :
    (BitVec.zeroExtend 32 a != BitVec.zeroExtend 32 b) = !(a == b) := by
  by_cases h : a = b
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, Bool.not_false, bne_iff_ne]
    intro heq
    apply h
    apply BitVec.eq_of_toNat_eq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_setWidth] at h1
    have ha := a.isLt
    have hb := b.isLt
    omega

theorem bv16_lsr8_zeroExtend64_truncate8 (y : BitVec 16) :
    BitVec.setWidth 8 (BitVec.setWidth 64 y >>> 8) =
      BitVec.setWidth 8 (y >>> 8) := by
  bv_bits

theorem bv16_zeroExtend64_truncate8 (y : BitVec 16) :
    BitVec.truncate 8 (BitVec.setWidth 64 y) = BitVec.truncate 8 y := by
  bv_bits

theorem bv64_ubfx_8_8_truncate8 {x0 : BitVec 64} {y : BitVec 16}
    (hy : BitVec.truncate 16 x0 = y) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) >>> 8 &&& 255#64) =
      BitVec.truncate 8 (y >>> 8) := by
  subst hy
  bv_bits

theorem bv64_orr_w0_truncate8 {x0 : BitVec 64} {y : BitVec 16}
    (hy : BitVec.truncate 16 x0 = y) :
    BitVec.zeroExtend 8 x0 = BitVec.truncate 8 y := by
  subst hy
  bv_bits

theorem bv64_bne_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ne_eq, not_false_eq_true, decide_true, bne_iff_ne]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hto
    exact h hto

theorem bv64_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hto
    exact h hto

theorem stackAt_computeAt_eq_prepare (sp : BitVec 64) :
    stackAt sp computeAtStack =
      stackAt sp lagrangePrepareStack ∗ memRegion (sp - 4352#64) 48 := by
  unfold stackAt computeAtStack growOneStack finishGrowStack lagrangePrepareStack allocHookStack
  rw [show (144 + ((4128 + 16) + 64) : Nat) = 48 + (208 + 4096) from rfl,
    memRegion_split (sp - BitVec.ofNat 64 (48 + (208 + 4096))) 48 (208 + 4096) (by decide)]
  have haddr : sp - 4352#64 + 48#64 = sp - 4304#64 := by bv_omega
  rw [haddr, sepConj_comm]

theorem memRegion_two_eq_exists_bytes (a : BitVec 64) :
    memRegion a 2 =
      (∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, memRegion_split a 1 1 (by decide),
    ProofLib.memRegion_one a, ProofLib.memRegion_one (a + 1#64)]
  apply sepProp_eq_of_entails
  · rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro b1
    exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.refl _))
  · apply Entails.sepExists_elim; intro b0
    apply Entails.sepExists_elim; intro b1
    exact sepConj_mono (Entails.sepExists_right b0 (Entails.refl _))
      (Entails.sepExists_right b1 (Entails.refl _))

theorem memRegion_out_split2 (out_ptr : BitVec 64) {i ptsNeeded : Nat}
    (hlt : i < ptsNeeded) (hbound : 2 * ptsNeeded < 2 ^ 64) :
    memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (ptsNeeded - i)) =
      (∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1)) ∗
      memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) := by
  have hlen : 2 * (ptsNeeded - i) = 2 + 2 * (ptsNeeded - (i + 1)) := by omega
  have haddr1 : out_ptr + BitVec.ofNat 64 (2 * i) + 1#64 = out_ptr + BitVec.ofNat 64 (2 * i + 1) := by
    rw [BitVec.add_assoc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i2 : 2 * i + 2 = 2 * (i + 1) := by omega
  have haddr2 : out_ptr + BitVec.ofNat 64 (2 * i) + 2#64 = out_ptr + BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h2i2]
  rw [hlen, memRegion_split (out_ptr + BitVec.ofNat 64 (2 * i)) 2 (2 * (ptsNeeded - (i + 1))) (by omega),
    haddr2, memRegion_two_eq_exists_bytes (out_ptr + BitVec.ofNat 64 (2 * i))]
  simp only [haddr1]

/-! ## Sub-Steps of One Iteration of `decodedMessageLoop` -/

end CryptoVerification.SpqrV1.Poly.DecodedMessage
