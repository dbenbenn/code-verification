/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Shared `FieldElement51` Packing, Canonicalization, and Stack-Table Helpers

Shared helper lemmas and tactics for `FieldElement51` packing, canonicalization, and stack-table
framing used across `Field51*`, `PointCompress*`, `MontToEdwards`, `LookupTableProj*`,
`NafLookupTable*`, `VariableBaseMul`, and `BasepointTable`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpNeg fpSq fpInv fpPow EdPoint EdExtPoint encodeEd
  edExtToAffine leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes fe51EdwardsDBytes fe51EdwardsD2Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  fe51EdwardsDBytes_length fe51EdwardsD_readLE_0 fe51EdwardsD_readLE_8
  fe51EdwardsD_readLE_16 fe51EdwardsD_readLE_24 fe51EdwardsD_readLE_32
  fe51EdwardsD2Bytes_length fe51EdwardsD2_readLE_0 fe51EdwardsD2_readLE_8
  fe51EdwardsD2_readLE_16 fe51EdwardsD2_readLE_24 fe51EdwardsD2_readLE_32)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edPointEq
  edExtToProjNiels projNielsTableStep projNielsTablePoints fe51ProjNielsTable8Bounded
  edAsExtended readLE_slice_eq readLE_congr_off)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe HasExactLen sub_ofNat64_add sepWP_norm_stackFrame
  write_length_eq write64_length_eq readLE_write64_self' readLE_write64_ne
  readLE_write_inside readLE_write_ne fe51LimbsBounded_slice_of_at fe51ValOfBytes_slice
  readLE_append_left readLE_append_right pointsToBytes40_eq_cells
  pointsToBytes32_eq_cells64 pointsTo64_eq_cells8 fe51_canonical_mod2
  sepWP_callee_shrink sepWP_callee_grow fpPow_eq_pow_mod fpPow_mod_eq_pow_mod
  mul_mod_eq_fpMul completed_split4_props_54 edAsExtended_of_append4)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (
  p25519_pos fpMul_fpInv_cancel)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp)

/-! ## 1. Shared Proof-State Hygiene and Limb-Unpacking Tactics -/

open Lean Meta Elab Tactic in
elab "clean_prev_sf" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut stateDecls : Array LocalDecl := #[]
  for decl in lctx do
    if !decl.isImplementationDetail then
      if decl.type.isConstOf ``Arm64.State && decl.userName != `s0 then
        stateDecls := stateDecls.push decl
  if stateDecls.size ≥ 2 then
    let prevSf := stateDecls[0]!
    let currSf := stateDecls[stateDecls.size - 1]!
    let mut prevEqs : Array FVarId := #[]
    let mut prevHyps : Array FVarId := #[]
    let mut currHyps : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && decl.fvarId != prevSf.fvarId && decl.fvarId != currSf.fvarId then
        let ty ← instantiateMVars decl.type
        if ty.containsFVar prevSf.fvarId then
          prevHyps := prevHyps.push decl.fvarId
          if !ty.containsFVar currSf.fvarId then
            if let some (_, lhs, _) := ty.eq? then
              if lhs.containsFVar prevSf.fvarId then
                prevEqs := prevEqs.push decl.fvarId
          else
            currHyps := currHyps.push decl.fvarId
    for cId in currHyps do
      let cIdent := mkIdent (← cId.getUserName)
      for pId in prevEqs do
        let pIdent := mkIdent (← pId.getUserName)
        try evalTactic (← `(tactic| rw [$pIdent:term] at $cIdent:ident))
        catch _ => pure ()
    let mut toClear : Array Ident := #[]
    for pId in prevHyps do
      if !currHyps.contains pId then
        toClear := toClear.push (mkIdent (← pId.getUserName))
    toClear := toClear.push (mkIdent prevSf.userName)
    for id in toClear do
      try evalTactic (← `(tactic| clear $id:ident))
      catch _ => pure ()

open Lean Meta Elab Tactic in
elab "norm_sf " n:num : tactic => withMainContext do
  let lctx ← getLCtx
  let mut stateDecls : Array LocalDecl := #[]
  for decl in lctx do
    if !decl.isImplementationDetail then
      if decl.type.isConstOf ``Arm64.State && decl.userName != `s0 then
        stateDecls := stateDecls.push decl
  if h : stateDecls.size > 0 then
    let currSf := stateDecls[stateDecls.size - 1]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, _) := ty.eq? then
          if lhs.isAppOfArity ``Arm64.State.sp 1 && lhs.containsFVar currSf.fvarId then
            let hIdent := mkIdent decl.userName
            evalTactic (← `(tactic| apply sepWP_norm_stackFrame $n $hIdent))
            return
  throwError "norm_sf: could not find `sf.sp = ...` hypothesis"

open Lean Meta Elab Tactic in
elab "clear_dead_vars " "[" ids:ident,* "]" : tactic => withMainContext do
  for id in ids.getElems do
    let lctx ← getLCtx
    if let some decl := lctx.findFromUserName? id.getId then
      let fvarId := decl.fvarId
      let mut hyps : Array Ident := #[]
      for d in lctx do
        if !d.isImplementationDetail && d.fvarId != fvarId then
          let ty ← instantiateMVars d.type
          if ty.containsFVar fvarId then
            hyps := hyps.push (mkIdent d.userName)
      for h in hyps do
        try evalTactic (← `(tactic| clear $h:ident))
        catch _ => pure ()

macro "unpack_fe51 " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _⟩ := $h)

macro "unpack_fe51_at " h:ident : tactic =>
  `(tactic| (dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd] at $h:ident; obtain ⟨_, _, _, _, _⟩ := $h))


/-- Unpack five 64-bit limbs into a 40-byte little-endian buffer. -/
@[expose] def packFe51Bytes (w0 w1 w2 w3 w4 : BitVec 64) : List (BitVec 8) :=
  unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack64 w4

@[simp] theorem packFe51Bytes_length (w0 w1 w2 w3 w4 : BitVec 64) :
    (packFe51Bytes w0 w1 w2 w3 w4).length = 40 := rfl

theorem pointsToBytes_packFe51Bytes (a : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦ₛ packFe51Bytes w0 w1 w2 w3 w4) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) := by
  unfold packFe51Bytes
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc]; rfl

theorem readLE_unpack64 (w : BitVec 64) : ByteSlice.readLE (unpack64 w) 0 8 = w := ByteSlice.readLE_unpackLE_64 8 w

private theorem readLE_append_left_f51 (xs ys : List (BitVec 8)) :
    ∀ (n : Nat), n ≤ xs.length → ByteSlice.readLE (xs ++ ys) 0 n = ByteSlice.readLE xs 0 n
  | 0, _ => rfl
  | n + 1, hn => by
    have hn' : n < xs.length := by omega
    simp only [ByteSlice.readLE, readLE_append_left_f51 xs ys n (by omega), Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hn']

private theorem readLE_append_right_f51 (xs ys : List (BitVec 8)) (off : Nat) :
    ∀ (n : Nat), ByteSlice.readLE (xs ++ ys) (xs.length + off) n = ByteSlice.readLE ys off n
  | 0 => rfl
  | n + 1 => by
    simp only [ByteSlice.readLE, readLE_append_right_f51 xs ys off n, List.getD_eq_getElem?_getD]
    rw [show xs.length + off + n = xs.length + (off + n) by omega, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem readLE_append_right8 (w : BitVec 64) (ys : List (BitVec 8)) (off off' : Nat) (h : 8 + off = off') :
    ByteSlice.readLE (unpack64 w ++ ys) off' 8 = ByteSlice.readLE ys off 8 := by
  subst h; exact readLE_append_right_f51 (unpack64 w) ys off 8
@[simp] theorem readLE_packFe51Bytes_0 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 0 8 = w0 := by
  unfold packFe51Bytes; simp only [List.append_assoc]; rw [readLE_append_left_f51 (unpack64 w0) _ 8 (by simp), readLE_unpack64]
@[simp] theorem readLE_packFe51Bytes_8 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 8 8 = w1 := by
  unfold packFe51Bytes; simp only [List.append_assoc]; rw [readLE_append_right8 w0 _ 0 8 rfl, readLE_append_left_f51 (unpack64 w1) _ 8 (by simp), readLE_unpack64]
@[simp] theorem readLE_packFe51Bytes_16 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 16 8 = w2 := by
  unfold packFe51Bytes; simp only [List.append_assoc]; rw [readLE_append_right8 w0 _ 8 16 rfl, readLE_append_right8 w1 _ 0 8 rfl, readLE_append_left_f51 (unpack64 w2) _ 8 (by simp), readLE_unpack64]
@[simp] theorem readLE_packFe51Bytes_24 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 24 8 = w3 := by
  unfold packFe51Bytes; simp only [List.append_assoc]; rw [readLE_append_right8 w0 _ 16 24 rfl, readLE_append_right8 w1 _ 8 16 rfl, readLE_append_right8 w2 _ 0 8 rfl, readLE_append_left_f51 (unpack64 w3) _ 8 (by simp), readLE_unpack64]
@[simp] theorem readLE_packFe51Bytes_32 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 32 8 = w4 := by
  unfold packFe51Bytes; simp only [List.append_assoc]; rw [readLE_append_right8 w0 _ 24 32 rfl, readLE_append_right8 w1 _ 16 24 rfl, readLE_append_right8 w2 _ 8 16 rfl, readLE_append_right8 w3 _ 0 8 rfl, readLE_unpack64]
@[simp] theorem fe51ValOfBytes_packFe51Bytes (w0 w1 w2 w3 w4 : BitVec 64) :
    fe51ValOfBytes (packFe51Bytes w0 w1 w2 w3 w4) = fe51Val w0 w1 w2 w3 w4 := by simp [fe51ValOfBytes]

theorem fe51LimbsBounded_packFe51Bytes (w0 w1 w2 w3 w4 : BitVec 64) (bound : Nat)
    (h0 : w0.toNat < bound) (h1 : w1.toNat < bound) (h2 : w2.toNat < bound)
    (h3 : w3.toNat < bound) (h4 : w4.toNat < bound) :
    fe51LimbsBounded (packFe51Bytes w0 w1 w2 w3 w4) bound := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h0, h1, h2, h3, h4]


theorem pointsToBytes_list32 (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
      ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
      ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
      ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
      ((a + 16#64) ↦₈ b16) ∗ ((a + 17#64) ↦₈ b17) ∗ ((a + 18#64) ↦₈ b18) ∗ ((a + 19#64) ↦₈ b19) ∗
      ((a + 20#64) ↦₈ b20) ∗ ((a + 21#64) ↦₈ b21) ∗ ((a + 22#64) ↦₈ b22) ∗ ((a + 23#64) ↦₈ b23) ∗
      ((a + 24#64) ↦₈ b24) ∗ ((a + 25#64) ↦₈ b25) ∗ ((a + 26#64) ↦₈ b26) ∗ ((a + 27#64) ↦₈ b27) ∗
      ((a + 28#64) ↦₈ b28) ∗ ((a + 29#64) ↦₈ b29) ∗ ((a + 30#64) ↦₈ b30) ∗ ((a + 31#64) ↦₈ b31) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc]; rfl

theorem pointsToBytes32_eq_cells8 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ (ByteSlice.readLE bs 0 8).extractLsb' 56 8) ∗
      ((a + 8#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 0 8) ∗ ((a + 9#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 8 8) ∗
      ((a + 10#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 16 8) ∗ ((a + 11#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 24 8) ∗
      ((a + 12#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 32 8) ∗ ((a + 13#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 40 8) ∗
      ((a + 14#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 48 8) ∗ ((a + 15#64) ↦₈ (ByteSlice.readLE bs 8 8).extractLsb' 56 8) ∗
      ((a + 16#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 0 8) ∗ ((a + 17#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 8 8) ∗
      ((a + 18#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 16 8) ∗ ((a + 19#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 24 8) ∗
      ((a + 20#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 32 8) ∗ ((a + 21#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 40 8) ∗
      ((a + 22#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 48 8) ∗ ((a + 23#64) ↦₈ (ByteSlice.readLE bs 16 8).extractLsb' 56 8) ∗
      ((a + 24#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 0 8) ∗ ((a + 25#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 8 8) ∗
      ((a + 26#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 16 8) ∗ ((a + 27#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 24 8) ∗
      ((a + 28#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 32 8) ∗ ((a + 29#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 40 8) ∗
      ((a + 30#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 48 8) ∗ ((a + 31#64) ↦₈ (ByteSlice.readLE bs 24 8).extractLsb' 56 8) := by
  rw [pointsToBytes32_eq_cells64 a bs h, pointsTo64_eq_cells8 a, pointsTo64_eq_cells8 (a + 8#64),
      pointsTo64_eq_cells8 (a + 16#64), pointsTo64_eq_cells8 (a + 24#64)]
  simp only [sepConj_assoc, BitVec.add_assoc]; rfl

@[expose] def packCanonical51Bytes (u0 u1 u2 u3 u4 : BitVec 64) : List (BitVec 8) :=
  [BitVec.zeroExtend 8 u0, BitVec.zeroExtend 8 (u0 >>> 8), BitVec.zeroExtend 8 (u0 >>> 16),
   BitVec.zeroExtend 8 (u0 >>> 24), BitVec.zeroExtend 8 (u0 >>> 32), BitVec.zeroExtend 8 (u0 >>> 40),
   BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
     (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3),
   BitVec.zeroExtend 8 (u1 >>> 5), BitVec.zeroExtend 8 (u1 >>> 13), BitVec.zeroExtend 8 (u1 >>> 21),
   BitVec.zeroExtend 8 (u1 >>> 29), BitVec.zeroExtend 8 (u1 >>> 37),
   BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6),
   BitVec.zeroExtend 8 (u2 >>> 2), BitVec.zeroExtend 8 (u2 >>> 10), BitVec.zeroExtend 8 (u2 >>> 18),
   BitVec.zeroExtend 8 (u2 >>> 26), BitVec.zeroExtend 8 (u2 >>> 34), BitVec.zeroExtend 8 (u2 >>> 42),
   BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1),
   BitVec.zeroExtend 8 (u3 >>> 7), BitVec.zeroExtend 8 (u3 >>> 15), BitVec.zeroExtend 8 (u3 >>> 23),
   BitVec.zeroExtend 8 (u3 >>> 31), BitVec.zeroExtend 8 (u3 >>> 39),
   BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4),
   BitVec.zeroExtend 8 (u4 >>> 4), BitVec.zeroExtend 8 (u4 >>> 12), BitVec.zeroExtend 8 (u4 >>> 20),
   BitVec.zeroExtend 8 (u4 >>> 28), BitVec.zeroExtend 8 (u4 >>> 36), BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64)]

theorem bv64_and_mask51_toNat (x : BitVec 64) : (x &&& 2251799813685247#64).toNat = x.toNat % 2 ^ 51 := by bv_bits
theorem bv64_ushr51_toNat (x : BitVec 64) : (x >>> 51).toNat = x.toNat / 2 ^ 51 := by bv_bits
theorem bv64_zext32_mul19_toNat (x : BitVec 64) (hx : x.toNat < 8) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x) * 19#64).toNat = x.toNat * 19 := by bv_bits
theorem bv64_add_toNat_of_lt (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]
theorem bv64_add_ushr51_toNat (a b : BitVec 64) (h : a.toNat + b.toNat / 2 ^ 51 < 2 ^ 64) :
    (a + b >>> 51).toNat = a.toNat + b.toNat / 2 ^ 51 := by
  rw [bv64_add_toNat_of_lt, bv64_ushr51_toNat]; rw [bv64_ushr51_toNat]; exact h

theorem fe51_carry1_nat (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 : Nat)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51) :
    l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204 =
      (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + (l4 / 2 ^ 51) * p25519 := by
  unfold p25519; omega

theorem fe51_carry_chain (a0 a1 a2 a3 a4 u1 u2 u3 u4 : Nat)
    (hu1 : u1 = a1 + a0 / 2 ^ 51) (hu2 : u2 = a2 + u1 / 2 ^ 51)
    (hu3 : u3 = a3 + u2 / 2 ^ 51) (hu4 : u4 = a4 + u3 / 2 ^ 51) :
    (a0 + a1 * 2 ^ 51 + a2 * 2 ^ 102 + a3 * 2 ^ 153 + a4 * 2 ^ 204 =
      (a0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 + (u4 / 2 ^ 51) * 2 ^ 255) ∧
    (a0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 < 2 ^ 255 := by omega

theorem fe51_q_le_one (h0 h1 h2 h3 h4 q0 q1 q2 q3 q : Nat)
    (bh0 : h0 < 2 ^ 51 + 152) (bh1 : h1 < 2 ^ 51 + 8)
    (bh2 : h2 < 2 ^ 51 + 8) (bh3 : h3 < 2 ^ 51 + 8) (bh4 : h4 < 2 ^ 51 + 8)
    (nq0 : q0 = (h0 + 19) / 2 ^ 51) (nq1 : q1 = (h1 + q0) / 2 ^ 51)
    (nq2 : q2 = (h2 + q1) / 2 ^ 51) (nq3 : q3 = (h3 + q2) / 2 ^ 51)
    (nq : q = (h4 + q3) / 2 ^ 51) : q ≤ 1 := by omega

theorem fe51_mod_of_carry_chains (H q Rq qu Ru : Nat)
    (hH : H < 2 ^ 255 + 2 ^ 208) (hq : q ≤ 1) (hRq_lt : Rq < 2 ^ 255) (hRu_lt : Ru < 2 ^ 255)
    (hc1 : H + 19 = Rq + q * 2 ^ 255) (hc2 : H + q * 19 = Ru + qu * 2 ^ 255) :
    H % p25519 = Ru := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · rw [Nat.mod_eq_of_lt (by unfold p25519; omega)]; omega
  · have h_eq : H = Ru + p25519 := by unfold p25519; omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold p25519 at h_eq ⊢; omega)]

theorem fe51_h_bounds (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 : Nat)
    (hl0 : l0 < 2 ^ 54) (hl1 : l1 < 2 ^ 54) (hl2 : l2 < 2 ^ 54) (hl3 : l3 < 2 ^ 54) (hl4 : l4 < 2 ^ 54)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51) :
    h0 < 2 ^ 51 + 152 ∧ h1 < 2 ^ 51 + 8 ∧ h2 < 2 ^ 51 + 8 ∧ h3 < 2 ^ 51 + 8 ∧ h4 < 2 ^ 51 + 8 ∧
    h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204 < 2 ^ 255 + 2 ^ 208 := by omega

theorem fe51_add19_comm (h0 h1 h2 h3 h4 x : Nat) :
    (h0 + x) + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204 =
      (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + x := by omega

theorem fe51_canonicalize_nat
    (l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 q0 q1 q2 q3 q u0 u1 u2 u3 u4 : Nat)
    (hl0 : l0 < 2 ^ 54) (hl1 : l1 < 2 ^ 54) (hl2 : l2 < 2 ^ 54) (hl3 : l3 < 2 ^ 54) (hl4 : l4 < 2 ^ 54)
    (nh0 : h0 = l0 % 2 ^ 51 + (l4 / 2 ^ 51) * 19) (nh1 : h1 = l1 % 2 ^ 51 + l0 / 2 ^ 51)
    (nh2 : h2 = l2 % 2 ^ 51 + l1 / 2 ^ 51) (nh3 : h3 = l3 % 2 ^ 51 + l2 / 2 ^ 51)
    (nh4 : h4 = l4 % 2 ^ 51 + l3 / 2 ^ 51)
    (nq0 : q0 = (h0 + 19) / 2 ^ 51) (nq1 : q1 = (h1 + q0) / 2 ^ 51)
    (nq2 : q2 = (h2 + q1) / 2 ^ 51) (nq3 : q3 = (h3 + q2) / 2 ^ 51) (nq : q = (h4 + q3) / 2 ^ 51)
    (nu0 : u0 = h0 + q * 19) (nu1 : u1 = h1 + u0 / 2 ^ 51) (nu2 : u2 = h2 + u1 / 2 ^ 51)
    (nu3 : u3 = h3 + u2 / 2 ^ 51) (nu4 : u4 = h4 + u3 / 2 ^ 51) :
    (l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204) % p25519 =
      (u0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
      (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204 := by
  rw [fe51_carry1_nat l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 nh0 nh1 nh2 nh3 nh4, Nat.add_mul_mod_self_right]
  obtain ⟨bh0, bh1, bh2, bh3, bh4, bhH⟩ :=
    fe51_h_bounds l0 l1 l2 l3 l4 h0 h1 h2 h3 h4 hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4
  have hq_le := fe51_q_le_one h0 h1 h2 h3 h4 q0 q1 q2 q3 q bh0 bh1 bh2 bh3 bh4 nq0 nq1 nq2 nq3 nq
  obtain ⟨hc_q, hlt_q⟩ := fe51_carry_chain (h0 + 19) h1 h2 h3 h4 (h1 + q0) (h2 + q1) (h3 + q2) (h4 + q3)
    (congrArg (h1 + ·) nq0) (congrArg (h2 + ·) nq1) (congrArg (h3 + ·) nq2) (congrArg (h4 + ·) nq3)
  rw [← nq, fe51_add19_comm] at hc_q
  obtain ⟨hc_u, hlt_u⟩ := fe51_carry_chain u0 h1 h2 h3 h4 u1 u2 u3 u4 nu1 nu2 nu3 nu4
  have hc_u' : (h0 + h1 * 2 ^ 51 + h2 * 2 ^ 102 + h3 * 2 ^ 153 + h4 * 2 ^ 204) + q * 19 =
      ((u0 % 2 ^ 51) + (u1 % 2 ^ 51) * 2 ^ 51 + (u2 % 2 ^ 51) * 2 ^ 102 +
        (u3 % 2 ^ 51) * 2 ^ 153 + (u4 % 2 ^ 51) * 2 ^ 204) + (u4 / 2 ^ 51) * 2 ^ 255 := by
    rw [← fe51_add19_comm, ← nu0, hc_u]
  exact fe51_mod_of_carry_chains _ q _ (u4 / 2 ^ 51) _ bhH hq_le hlt_q hlt_u hc_q hc_u'
theorem bv64_mask51_add_ushr51_toNat (a b : BitVec 64) :
    ((a &&& 2251799813685247#64) + b >>> 51).toNat = a.toNat % 2 ^ 51 + b.toNat / 2 ^ 51 := by bv_bits
theorem bv64_mask51_add_mul19_toNat (a b : BitVec 64) (hb : b.toNat < 2 ^ 54) :
    ((a &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (b >>> 51)) * 19#64).toNat =
      a.toNat % 2 ^ 51 + (b.toNat / 2 ^ 51) * 19 := by
  rw [BitVec.toNat_add, bv64_and_mask51_toNat, bv64_zext32_mul19_toNat, bv64_ushr51_toNat]; · omega
  · rw [bv64_ushr51_toNat]; omega
theorem bv64_add19_ushr51_toNat (a : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    ((a + 19#64) >>> 51).toNat = (a.toNat + 19) / 2 ^ 51 := by bv_bits
theorem bv64_add_ushr51_toNat_of_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    (a + b >>> 51).toNat = a.toNat + b.toNat / 2 ^ 51 := by bv_bits
theorem bv64_add_ushr51_ushr51_toNat_of_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 52) :
    ((a + b >>> 51) >>> 51).toNat = (a.toNat + (b >>> 51).toNat) / 2 ^ 51 := by bv_bits
theorem bv64_add_mul19_toNat_of_lt (a q : BitVec 64) (ha : a.toNat < 2 ^ 52) (hq : q.toNat ≤ 1) :
    (a + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64).toNat = a.toNat + q.toNat * 19 := by
  rw [BitVec.toNat_add, bv64_zext32_mul19_toNat] <;> omega

theorem fe51_to_bytes_canonical_val (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54)
    (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51)
    (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51)
    (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51)
    (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    fe51Val l0 l1 l2 l3 l4 % p25519 =
      (u0.toNat % 2 ^ 51) + (u1.toNat % 2 ^ 51) * 2 ^ 51 +
      (u2.toNat % 2 ^ 51) * 2 ^ 102 + (u3.toNat % 2 ^ 51) * 2 ^ 153 + (u4.toNat % 2 ^ 51) * 2 ^ 204 := by
  have nh0 : h0.toNat = l0.toNat % 2 ^ 51 + (l4.toNat / 2 ^ 51) * 19 := hh0 ▸ bv64_mask51_add_mul19_toNat l0 l4 hl4
  have nh1 : h1.toNat = l1.toNat % 2 ^ 51 + l0.toNat / 2 ^ 51 := hh1 ▸ bv64_mask51_add_ushr51_toNat l1 l0
  have nh2 : h2.toNat = l2.toNat % 2 ^ 51 + l1.toNat / 2 ^ 51 := hh2 ▸ bv64_mask51_add_ushr51_toNat l2 l1
  have nh3 : h3.toNat = l3.toNat % 2 ^ 51 + l2.toNat / 2 ^ 51 := hh3 ▸ bv64_mask51_add_ushr51_toNat l3 l2
  have nh4 : h4.toNat = l4.toNat % 2 ^ 51 + l3.toNat / 2 ^ 51 := hh4 ▸ bv64_mask51_add_ushr51_toNat l4 l3
  obtain ⟨bh0, bh1, bh2, bh3, bh4, _⟩ :=
    fe51_h_bounds l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat
      hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4
  have bh0' : h0.toNat < 2 ^ 52 := Nat.lt_trans bh0 (by decide)
  have bh1' : h1.toNat < 2 ^ 52 := Nat.lt_trans bh1 (by decide)
  have bh2' : h2.toNat < 2 ^ 52 := Nat.lt_trans bh2 (by decide)
  have bh3' : h3.toNat < 2 ^ 52 := Nat.lt_trans bh3 (by decide)
  have bh4' : h4.toNat < 2 ^ 52 := Nat.lt_trans bh4 (by decide)
  have e0 := bv64_add19_ushr51_toNat h0 bh0'
  have e1 := bv64_add_ushr51_ushr51_toNat_of_lt h1 (h0 + 19#64) bh1'
  have e2 := bv64_add_ushr51_ushr51_toNat_of_lt h2 (h1 + (h0 + 19#64) >>> 51) bh2'
  have e3 := bv64_add_ushr51_ushr51_toNat_of_lt h3 (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) bh3'
  have nq : q.toNat = (h4.toNat + ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat) / 2 ^ 51 :=
    hq ▸ bv64_add_ushr51_ushr51_toNat_of_lt h4 (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) bh4'
  have hq_le := fe51_q_le_one h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat
    ((h0 + 19#64) >>> 51).toNat ((h1 + (h0 + 19#64) >>> 51) >>> 51).toNat
    ((h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51).toNat
    ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat
    q.toNat bh0 bh1 bh2 bh3 bh4 e0 e1 e2 e3 nq
  have nu0 : u0.toNat = h0.toNat + q.toNat * 19 := hu0 ▸ bv64_add_mul19_toNat_of_lt h0 q bh0' hq_le
  have nu1 : u1.toNat = h1.toNat + u0.toNat / 2 ^ 51 := hu1 ▸ bv64_add_ushr51_toNat_of_lt h1 u0 bh1'
  have nu2 : u2.toNat = h2.toNat + u1.toNat / 2 ^ 51 := hu2 ▸ bv64_add_ushr51_toNat_of_lt h2 u1 bh2'
  have nu3 : u3.toNat = h3.toNat + u2.toNat / 2 ^ 51 := hu3 ▸ bv64_add_ushr51_toNat_of_lt h3 u2 bh3'
  have nu4 : u4.toNat = h4.toNat + u3.toNat / 2 ^ 51 := hu4 ▸ bv64_add_ushr51_toNat_of_lt h4 u3 bh4'
  exact fe51_canonicalize_nat l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat
    h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat ((h0 + 19#64) >>> 51).toNat
    ((h1 + (h0 + 19#64) >>> 51) >>> 51).toNat ((h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51).toNat
    ((h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat
    q.toNat u0.toNat u1.toNat u2.toNat u3.toNat u4.toNat
    hl0 hl1 hl2 hl3 hl4 nh0 nh1 nh2 nh3 nh4 e0 e1 e2 e3 nq nu0 nu1 nu2 nu3 nu4

theorem fe51_byte6_eq (u0 u1 : BitVec 64) :
    BitVec.zeroExtend 8
      (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3) =
      BitVec.ofNat 8 (((u0.toNat % 2 ^ 51 + (u1.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 48) % 256) := by
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, BitVec.setWidth_and]
  bv_bits

theorem fe51_byte12_eq (u1 u2 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6) =
      BitVec.ofNat 8 (((u1.toNat % 2 ^ 51 + (u2.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 45) % 256) := by bv_bits

theorem fe51_byte19_eq (u2 u3 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1) =
      BitVec.ofNat 8 (((u2.toNat % 2 ^ 51 + (u3.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 50) % 256) := by bv_bits

theorem fe51_byte25_eq (u3 u4 : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4) =
      BitVec.ofNat 8 (((u3.toNat % 2 ^ 51 + (u4.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ 47) % 256) := by bv_bits

theorem fe51_byte31_eq (u4 : BitVec 64) :
    BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64) =
      BitVec.ofNat 8 (((u4.toNat % 2 ^ 51) / 2 ^ 44) % 256) := by bv_bits

theorem limb_div_step (c R n m : Nat) (hc : c < 2 ^ 51) (hm : n = 2 ^ 51 * m) :
    (c + R * 2 ^ 51) / n = R / m := by
  have hd : (c + R * 2 ^ 51) / 2 ^ 51 = R := by omega
  rw [hm, ← Nat.div_div_eq_div_mul, hd]

theorem limb_byte_interior (u : BitVec 64) (R s k : Nat) (hk : 2 ^ 51 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + R * 2 ^ 51) / 2 ^ s) % 256) =
      BitVec.zeroExtend 8 (u >>> s) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (((u.toNat % 2 ^ 51 + R * 2 ^ 51) / 2 ^ s) % 256) % 256 = (u.toNat / 2 ^ s) % 256
  rw [Nat.mod_mod]
  have h1 : u.toNat % 2 ^ 51 + R * 2 ^ 51 = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * R)) := by
    rw [hk, Nat.mul_comm R, Nat.mul_assoc, Nat.mul_assoc]
  have h2 : u.toNat = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * (u.toNat / 2 ^ 51))) := by
    calc u.toNat = u.toNat % 2 ^ 51 + 2 ^ 51 * (u.toNat / 2 ^ 51) := by rw [Nat.add_comm, Nat.div_add_mod]
      _ = u.toNat % 2 ^ 51 + 2 ^ s * (256 * (k * (u.toNat / 2 ^ 51))) := by rw [hk, Nat.mul_assoc, Nat.mul_assoc]
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  rw [h1, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  conv => rhs; rw [h2, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem limb_byte_last (u : BitVec 64) (s k : Nat) (hk : 2 ^ 51 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 (((u.toNat % 2 ^ 51) / 2 ^ s) % 256) = BitVec.zeroExtend 8 (u >>> s) := by
  simpa using limb_byte_interior u 0 s k hk

theorem limb_byte_boundary (c d R s k : Nat) (hk : 2 ^ 102 = 2 ^ s * (256 * k)) :
    ((c + (d + R * 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256 = ((c + d * 2 ^ 51) / 2 ^ s) % 256 := by
  have h1 : c + (d + R * 2 ^ 51) * 2 ^ 51 = (c + d * 2 ^ 51) + 2 ^ s * (256 * (k * R)) := by
    have hpow : (2 ^ 51 : Nat) * 2 ^ 51 = 2 ^ 102 := by decide
    rw [Nat.add_mul, ← Nat.add_assoc, Nat.mul_assoc R, hpow, hk, Nat.mul_comm R, Nat.mul_assoc, Nat.mul_assoc]
  rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.add_mul_mod_self_left]

theorem limb_byte_boundary_bv (u v : BitVec 64) (R s k : Nat) (hk : 2 ^ 102 = 2 ^ s * (256 * k)) :
    BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + ((v.toNat % 2 ^ 51) + R * 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256) =
      BitVec.ofNat 8 ((((u.toNat % 2 ^ 51) + (v.toNat % 2 ^ 51) * 2 ^ 51) / 2 ^ s) % 256) := by
  rw [limb_byte_boundary (u.toNat % 2 ^ 51) (v.toNat % 2 ^ 51) R s k hk]

theorem natToLeBytes_32_eq (n : Nat) :
    natToLeBytes 32 n =
      [BitVec.ofNat 8 ((n / 2 ^ 0) % 256), BitVec.ofNat 8 ((n / 2 ^ 8) % 256), BitVec.ofNat 8 ((n / 2 ^ 16) % 256), BitVec.ofNat 8 ((n / 2 ^ 24) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 32) % 256), BitVec.ofNat 8 ((n / 2 ^ 40) % 256), BitVec.ofNat 8 ((n / 2 ^ 48) % 256), BitVec.ofNat 8 ((n / 2 ^ 56) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 64) % 256), BitVec.ofNat 8 ((n / 2 ^ 72) % 256), BitVec.ofNat 8 ((n / 2 ^ 80) % 256), BitVec.ofNat 8 ((n / 2 ^ 88) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 96) % 256), BitVec.ofNat 8 ((n / 2 ^ 104) % 256), BitVec.ofNat 8 ((n / 2 ^ 112) % 256), BitVec.ofNat 8 ((n / 2 ^ 120) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 128) % 256), BitVec.ofNat 8 ((n / 2 ^ 136) % 256), BitVec.ofNat 8 ((n / 2 ^ 144) % 256), BitVec.ofNat 8 ((n / 2 ^ 152) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 160) % 256), BitVec.ofNat 8 ((n / 2 ^ 168) % 256), BitVec.ofNat 8 ((n / 2 ^ 176) % 256), BitVec.ofNat 8 ((n / 2 ^ 184) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 192) % 256), BitVec.ofNat 8 ((n / 2 ^ 200) % 256), BitVec.ofNat 8 ((n / 2 ^ 208) % 256), BitVec.ofNat 8 ((n / 2 ^ 216) % 256),
       BitVec.ofNat 8 ((n / 2 ^ 224) % 256), BitVec.ofNat 8 ((n / 2 ^ 232) % 256), BitVec.ofNat 8 ((n / 2 ^ 240) % 256), BitVec.ofNat 8 ((n / 2 ^ 248) % 256)] := rfl

theorem packCanonical51Bytes_eq_natToLeBytes (u0 u1 u2 u3 u4 : BitVec 64) :
    packCanonical51Bytes u0 u1 u2 u3 u4 =
      natToLeBytes 32 ((u0.toNat % 2 ^ 51) + ((u1.toNat % 2 ^ 51) + ((u2.toNat % 2 ^ 51) +
        ((u3.toNat % 2 ^ 51) + (u4.toNat % 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) := by
  let V4 := u4.toNat % 2 ^ 51; let V3 := (u3.toNat % 2 ^ 51) + V4 * 2 ^ 51
  let V2 := (u2.toNat % 2 ^ 51) + V3 * 2 ^ 51; let V1 := (u1.toNat % 2 ^ 51) + V2 * 2 ^ 51
  let V0 := (u0.toNat % 2 ^ 51) + V1 * 2 ^ 51
  change packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 V0; rw [natToLeBytes_32_eq]
  have d0 (n m : Nat) (h : n = 2 ^ 51 * m) : V0 / n = V1 / m := limb_div_step (u0.toNat % 2 ^ 51) V1 n m (Nat.mod_lt _ (by decide)) h
  have d1 (n m : Nat) (h : n = 2 ^ 51 * m) : V1 / n = V2 / m := limb_div_step (u1.toNat % 2 ^ 51) V2 n m (Nat.mod_lt _ (by decide)) h
  have d2 (n m : Nat) (h : n = 2 ^ 51 * m) : V2 / n = V3 / m := limb_div_step (u2.toNat % 2 ^ 51) V3 n m (Nat.mod_lt _ (by decide)) h
  have d3 (n m : Nat) (h : n = 2 ^ 51 * m) : V3 / n = V4 / m := limb_div_step (u3.toNat % 2 ^ 51) V4 n m (Nat.mod_lt _ (by decide)) h
  rw [d0 (2 ^ 56) (2 ^ 5) (by decide), d0 (2 ^ 64) (2 ^ 13) (by decide), d0 (2 ^ 72) (2 ^ 21) (by decide), d0 (2 ^ 80) (2 ^ 29) (by decide),
      d0 (2 ^ 88) (2 ^ 37) (by decide), d0 (2 ^ 96) (2 ^ 45) (by decide), d0 (2 ^ 104) (2 ^ 53) (by decide), d1 (2 ^ 53) (2 ^ 2) (by decide),
      d0 (2 ^ 112) (2 ^ 61) (by decide), d1 (2 ^ 61) (2 ^ 10) (by decide), d0 (2 ^ 120) (2 ^ 69) (by decide), d1 (2 ^ 69) (2 ^ 18) (by decide),
      d0 (2 ^ 128) (2 ^ 77) (by decide), d1 (2 ^ 77) (2 ^ 26) (by decide), d0 (2 ^ 136) (2 ^ 85) (by decide), d1 (2 ^ 85) (2 ^ 34) (by decide),
      d0 (2 ^ 144) (2 ^ 93) (by decide), d1 (2 ^ 93) (2 ^ 42) (by decide), d0 (2 ^ 152) (2 ^ 101) (by decide), d1 (2 ^ 101) (2 ^ 50) (by decide),
      d0 (2 ^ 160) (2 ^ 109) (by decide), d1 (2 ^ 109) (2 ^ 58) (by decide), d2 (2 ^ 58) (2 ^ 7) (by decide),
      d0 (2 ^ 168) (2 ^ 117) (by decide), d1 (2 ^ 117) (2 ^ 66) (by decide), d2 (2 ^ 66) (2 ^ 15) (by decide),
      d0 (2 ^ 176) (2 ^ 125) (by decide), d1 (2 ^ 125) (2 ^ 74) (by decide), d2 (2 ^ 74) (2 ^ 23) (by decide),
      d0 (2 ^ 184) (2 ^ 133) (by decide), d1 (2 ^ 133) (2 ^ 82) (by decide), d2 (2 ^ 82) (2 ^ 31) (by decide),
      d0 (2 ^ 192) (2 ^ 141) (by decide), d1 (2 ^ 141) (2 ^ 90) (by decide), d2 (2 ^ 90) (2 ^ 39) (by decide),
      d0 (2 ^ 200) (2 ^ 149) (by decide), d1 (2 ^ 149) (2 ^ 98) (by decide), d2 (2 ^ 98) (2 ^ 47) (by decide),
      d0 (2 ^ 208) (2 ^ 157) (by decide), d1 (2 ^ 157) (2 ^ 106) (by decide), d2 (2 ^ 106) (2 ^ 55) (by decide), d3 (2 ^ 55) (2 ^ 4) (by decide),
      d0 (2 ^ 216) (2 ^ 165) (by decide), d1 (2 ^ 165) (2 ^ 114) (by decide), d2 (2 ^ 114) (2 ^ 63) (by decide), d3 (2 ^ 63) (2 ^ 12) (by decide),
      d0 (2 ^ 224) (2 ^ 173) (by decide), d1 (2 ^ 173) (2 ^ 122) (by decide), d2 (2 ^ 122) (2 ^ 71) (by decide), d3 (2 ^ 71) (2 ^ 20) (by decide),
      d0 (2 ^ 232) (2 ^ 181) (by decide), d1 (2 ^ 181) (2 ^ 130) (by decide), d2 (2 ^ 130) (2 ^ 79) (by decide), d3 (2 ^ 79) (2 ^ 28) (by decide),
      d0 (2 ^ 240) (2 ^ 189) (by decide), d1 (2 ^ 189) (2 ^ 138) (by decide), d2 (2 ^ 138) (2 ^ 87) (by decide), d3 (2 ^ 87) (2 ^ 36) (by decide),
      d0 (2 ^ 248) (2 ^ 197) (by decide), d1 (2 ^ 197) (2 ^ 146) (by decide), d2 (2 ^ 146) (2 ^ 95) (by decide), d3 (2 ^ 95) (2 ^ 44) (by decide)]
  rw [limb_byte_interior u0 V1 0 (2 ^ 43) (by decide), BitVec.ushiftRight_zero,
      limb_byte_interior u0 V1 8 (2 ^ 35) (by decide), limb_byte_interior u0 V1 16 (2 ^ 27) (by decide),
      limb_byte_interior u0 V1 24 (2 ^ 19) (by decide), limb_byte_interior u0 V1 32 (2 ^ 11) (by decide),
      limb_byte_interior u0 V1 40 (2 ^ 3) (by decide), limb_byte_boundary_bv u0 u1 V2 48 (2 ^ 46) (by decide), ← fe51_byte6_eq u0 u1,
      limb_byte_interior u1 V2 5 (2 ^ 38) (by decide), limb_byte_interior u1 V2 13 (2 ^ 30) (by decide),
      limb_byte_interior u1 V2 21 (2 ^ 22) (by decide), limb_byte_interior u1 V2 29 (2 ^ 14) (by decide),
      limb_byte_interior u1 V2 37 (2 ^ 6) (by decide), limb_byte_boundary_bv u1 u2 V3 45 (2 ^ 49) (by decide), ← fe51_byte12_eq u1 u2,
      limb_byte_interior u2 V3 2 (2 ^ 41) (by decide), limb_byte_interior u2 V3 10 (2 ^ 33) (by decide),
      limb_byte_interior u2 V3 18 (2 ^ 25) (by decide), limb_byte_interior u2 V3 26 (2 ^ 17) (by decide),
      limb_byte_interior u2 V3 34 (2 ^ 9) (by decide), limb_byte_interior u2 V3 42 (2 ^ 1) (by decide),
      limb_byte_boundary_bv u2 u3 V4 50 (2 ^ 44) (by decide), ← fe51_byte19_eq u2 u3,
      limb_byte_interior u3 V4 7 (2 ^ 36) (by decide), limb_byte_interior u3 V4 15 (2 ^ 28) (by decide),
      limb_byte_interior u3 V4 23 (2 ^ 20) (by decide), limb_byte_interior u3 V4 31 (2 ^ 12) (by decide),
      limb_byte_interior u3 V4 39 (2 ^ 4) (by decide), ← fe51_byte25_eq u3 u4,
      limb_byte_last u4 4 (2 ^ 39) (by decide), limb_byte_last u4 12 (2 ^ 31) (by decide),
      limb_byte_last u4 20 (2 ^ 23) (by decide), limb_byte_last u4 28 (2 ^ 15) (by decide),
      limb_byte_last u4 36 (2 ^ 7) (by decide), ← fe51_byte31_eq u4]; rfl

theorem fe51_horner_eq (c0 c1 c2 c3 c4 : Nat) :
    c0 + c1 * 2 ^ 51 + c2 * 2 ^ 102 + c3 * 2 ^ 153 + c4 * 2 ^ 204 =
      c0 + (c1 + (c2 + (c3 + c4 * 2 ^ 51) * 2 ^ 51) * 2 ^ 51) * 2 ^ 51 := by omega

theorem fe51_to_bytes_math (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51) (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  have hval := fe51_to_bytes_canonical_val l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4
    h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4
  rw [hval, fe51_horner_eq, packCanonical51Bytes_eq_natToLeBytes]

theorem sepWP_callee_912_to_512 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 1264#64) 912 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s
      ((memRegion (sp - 1264#64) 400 ∗ memRegion (sp - 864#64) 512) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hsplit : memRegion (sp - 1264#64) 912 =
      memRegion (sp - 1264#64) 400 ∗ memRegion (sp - 864#64) 512 := by
    have h1 := memRegion_split (sp - 1264#64) 400 512 (by decide)
    have haddr : sp - 1264#64 + BitVec.ofNat 64 400 = sp - 864#64 :=
      sub_ofNat64_add sp 1264 400 (by decide)
    rw [haddr] at h1; exact h1
  rw [hf, hsplit]; exact hnext

theorem sepWP_callee_512_to_912 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 1264#64) 400 ∗ memRegion (sp - 864#64) 512) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp - 1264#64) 912 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hsplit : memRegion (sp - 1264#64) 912 =
      memRegion (sp - 1264#64) 400 ∗ memRegion (sp - 864#64) 512 := by
    have h1 := memRegion_split (sp - 1264#64) 400 512 (by decide)
    have haddr : sp - 1264#64 + BitVec.ofNat 64 400 = sp - 864#64 :=
      sub_ofNat64_add sp 1264 400 (by decide)
    rw [haddr] at h1; exact h1
  rw [hf, ← hsplit]; exact hnext

theorem identity_write64_post (s : List (BitVec 8)) (hs : s.length = 160) :
    let buf :=
      ByteSlice.write64
        (ByteSlice.write64
          (ByteSlice.write64
            (ByteSlice.write64
              (ByteSlice.write64
                (ByteSlice.write64
                  (ByteSlice.write64
                    (ByteSlice.write64
                      (ByteSlice.write64
                        (ByteSlice.write64
                          (ByteSlice.write64
                            (ByteSlice.write64
                              (ByteSlice.write64
                                (ByteSlice.write64
                                  (ByteSlice.write64
                                    (ByteSlice.write64
                                      (ByteSlice.write64
                                        (ByteSlice.write64
                                          (ByteSlice.write64
                                            (ByteSlice.write64 s 32 0#64)
                                            72 0#64)
                                          40 1#64)
                                        48 0#64)
                                      0 0#64)
                                    8 0#64)
                                  16 0#64)
                                24 0#64)
                              56 0#64)
                            64 0#64)
                          80 1#64)
                        88 0#64)
                      96 0#64)
                    104 0#64)
                  120 0#64)
                128 0#64)
              136 0#64)
            144 0#64)
          112 0#64)
        152 0#64
    buf.length = 160 ∧ fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = ⟨0, 1, 1, 0⟩ := by
  haveI : HasLenGe s 160 := ⟨by omega⟩
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
    write64_length_eq, hs, Nat.min_eq_left]
  decide +kernel

/-! ## 2. Canonical `FieldElement51::to_bytes` & Negation Helpers -/

theorem bv64_sub_add (x a b : BitVec 64) : (x - a) + b = x - (a - b) := by bv_omega

theorem pointsToBytes_packCanonical51Bytes (p : BitVec 64) (u0 u1 u2 u3 u4 : BitVec 64) :
    ((p ↦₈ BitVec.zeroExtend 8 u0) ∗
     ((p + 1#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 8)) ∗
     ((p + 2#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 16)) ∗
     ((p + 3#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 24)) ∗
     ((p + 4#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 32)) ∗
     ((p + 5#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 40)) ∗
     ((p + 6#64) ↦₈ BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
       (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3)) ∗
     ((p + 7#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 5)) ∗
     ((p + 8#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 13)) ∗
     ((p + 9#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 21)) ∗
     ((p + 10#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 29)) ∗
     ((p + 11#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 37)) ∗
     ((p + 12#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6)) ∗
     ((p + 13#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 2)) ∗
     ((p + 14#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 10)) ∗
     ((p + 15#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 18)) ∗
     ((p + 16#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 26)) ∗
     ((p + 17#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 34)) ∗
     ((p + 18#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 42)) ∗
     ((p + 19#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1)) ∗
     ((p + 20#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 7)) ∗
     ((p + 21#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 15)) ∗
     ((p + 22#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 23)) ∗
     ((p + 23#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 31)) ∗
     ((p + 24#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 39)) ∗
     ((p + 25#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4)) ∗
     ((p + 26#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 4)) ∗
     ((p + 27#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 12)) ∗
     ((p + 28#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 20)) ∗
     ((p + 29#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 28)) ∗
     ((p + 30#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 36)) ∗
     ((p + 31#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64))) =
    (p ↦ₛ packCanonical51Bytes u0 u1 u2 u3 u4) := by
  rw [packCanonical51Bytes, pointsToBytes_list32]

theorem eq_of_div_pow256_mod :
    ∀ (len a b : Nat), a < 256 ^ len → b < 256 ^ len →
      (∀ i < len, (a / 256 ^ i) % 256 = (b / 256 ^ i) % 256) → a = b
  | 0, a, b, ha, hb, _ => by simp [Nat.pow_zero] at ha hb; omega
  | len + 1, a, b, ha, hb, h => by
    have h0 : a % 256 = b % 256 := by simpa using h 0 (by omega)
    have hdiv : a / 256 = b / 256 := by
      apply eq_of_div_pow256_mod len (a / 256) (b / 256)
      · rw [Nat.pow_succ'] at ha; omega
      · rw [Nat.pow_succ'] at hb; omega
      · intro i hi
        have hi' := h (i + 1) (by omega)
        rw [Nat.pow_succ'] at hi'
        rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hi'
        exact hi'
    omega

theorem natToLeBytes_getElem (len n i : Nat) (hi : i < len) :
    ((natToLeBytes len n)[i]'(by simp [natToLeBytes, hi])).toNat = (n / 256 ^ i) % 256 := by
  simp only [natToLeBytes, List.getElem_map, List.getElem_range, BitVec.toNat_ofNat]
  exact Nat.mod_lt _ (by decide) |> Nat.mod_eq_of_lt

theorem natToLeBytes_32_beq_iff (a b : Nat) (ha : a < p25519) (hb : b < p25519) :
    (natToLeBytes 32 a == natToLeBytes 32 b) = (a == b) := by
  have ha' : a < 256 ^ 32 := Nat.lt_trans ha (by unfold p25519; decide)
  have hb' : b < 256 ^ 32 := Nat.lt_trans hb (by unfold p25519; decide)
  by_cases h : a = b
  · subst h; simp
  · have hne : natToLeBytes 32 a ≠ natToLeBytes 32 b := by
      intro heq
      apply h (eq_of_div_pow256_mod 32 a b ha' hb' (fun i hi => ?_))
      rw [← natToLeBytes_getElem 32 a i hi, ← natToLeBytes_getElem 32 b i hi]
      exact congrArg BitVec.toNat (List.getElem_of_eq heq _)
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]


theorem pointsToBytes160_split4 (p : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 160) :
    (p ↦ₛ bs) =
      ((p ↦ₛ bs.take 40) ∗
       ((p + 40#64) ↦ₛ (bs.drop 40).take 40) ∗
       ((p + 80#64) ↦ₛ (bs.drop 80).take 40) ∗
       ((p + 120#64) ↦ₛ bs.drop 120)) := by
  have h1 := pointsToBytes_take_drop p 40 bs (by omega)
  have h2 := pointsToBytes_take_drop (p + 40#64) 40 (bs.drop 40) (by simp [h])
  have h3 := pointsToBytes_take_drop (p + 40#64 + 40#64) 40 ((bs.drop 40).drop 40) (by simp [h])
  simp only [List.drop_drop, BitVec.add_assoc] at h2 h3
  rw [h1, h2, h3]; rfl

theorem sepWP_merge_stack_32_8 (sp off1 off2 : BitVec 64)
    {xs ys : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - off1) ↦ₛ xs ∗ (sp - off2) ↦ₛ ys) ∗ P := by sep_frame)
    (hxs : xs.length = 32 := by assumption)
    (hoff : (sp - off1) + 32#64 = sp - off2 := by bv_omega)
    (hnext : SepWP prog target_pc s (((sp - off1) ↦ₛ (xs ++ ys)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : (sp - off1) ↦ₛ (xs ++ ys) = ((sp - off1) ↦ₛ xs) ∗ ((sp - off2) ↦ₛ ys) := by
    rw [pointsToBytes_append, hxs, hoff]
  rw [hf, ← hm]
  exact hnext

theorem zeroExtend8_and32 (r6 r3 : BitVec 64) (b1 b2 : Bool)
    (h1 : BitVec.zeroExtend 8 r3 = if b1 = true then 1#8 else 0#8)
    (h2 : BitVec.zeroExtend 8 r6 = if b2 = true then 1#8 else 0#8) :
    BitVec.zeroExtend 8 (BitVec.truncate 32 r6 &&& BitVec.truncate 32 r3) =
      if (b1 && b2) = true then 1#8 else 0#8 := by
  have h : BitVec.zeroExtend 8 (BitVec.truncate 32 r6 &&& BitVec.truncate 32 r3) =
      BitVec.zeroExtend 8 r6 &&& BitVec.zeroExtend 8 r3 := by
    simp (disch := decide) only [BitVec.truncate_eq_setWidth,
      BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le]
  rw [h, h1, h2]
  cases b1 <;> cases b2 <;> rfl

theorem sepWP_fold_point160 (p : BitVec 64) (bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((p ↦ₛ bs.take 40) ∗ ((p + 40#64) ↦ₛ (bs.drop 40).take 40) ∗
      ((p + 80#64) ↦ₛ (bs.drop 80).take 40) ∗ ((p + 120#64) ↦ₛ bs.drop 120)) ∗ P := by sep_frame)
    (h : bs.length = 160 := by assumption)
    (hnext : SepWP prog target_pc s ((p ↦ₛ bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, ← pointsToBytes160_split4 p bs h]
  exact hnext

theorem merge_stack_16_496 (s0 sf : State) (hsp : sf.sp = s0.sp) (P : SepProp) :
    stackFrame sf 16 ∗ stackAt (s0.sp - 16#64) 496 ∗ P = stackFrame sf 512 ∗ P := by
  rw [← sepConj_assoc]
  congr 1
  change memRegion (sf.sp - 16#64) 16 ∗ stackAt (s0.sp - 16#64) 496 = stackAt sf.sp (496 + 16)
  rw [hsp, sepConj_comm, ← stackAt_region s0.sp 496 16 (by decide)]

theorem edPointEq_of_muls (a_2 a_rest w w_1 w_2 w_3 : List (BitVec 8))
    (hw : fe51ValOfBytes w % p25519 =
      fe51ValOfBytes (List.take 40 a_2) * fe51ValOfBytes (List.take 40 (List.drop 80 a_rest)) % p25519)
    (hw1 : fe51ValOfBytes w_1 % p25519 =
      fe51ValOfBytes (List.take 40 a_rest) * fe51ValOfBytes (List.take 40 (List.drop 80 a_2)) % p25519)
    (hw2 : fe51ValOfBytes w_2 % p25519 =
      fe51ValOfBytes (List.take 40 (List.drop 40 a_2)) * fe51ValOfBytes (List.take 40 (List.drop 80 a_rest)) % p25519)
    (hw3 : fe51ValOfBytes w_3 % p25519 =
      fe51ValOfBytes (List.take 40 (List.drop 40 a_rest)) * fe51ValOfBytes (List.take 40 (List.drop 80 a_2)) % p25519) :
    ((natToLeBytes 32 (fe51ValOfBytes w % p25519) == natToLeBytes 32 (fe51ValOfBytes w_1 % p25519)) &&
     (natToLeBytes 32 (fe51ValOfBytes w_2 % p25519) == natToLeBytes 32 (fe51ValOfBytes w_3 % p25519))) =
    edPointEq (edExtOfBytes a_2) (edExtOfBytes a_rest) := by
  have hp : 0 < p25519 := by unfold p25519; decide
  rw [natToLeBytes_32_beq_iff _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ hp),
      natToLeBytes_32_beq_iff _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)]
  have hs0 : ∀ bs : List (BitVec 8), fe51ValOfBytes (List.take 40 bs) = fe51ValAt bs 0 :=
    fun bs => fe51ValOfBytes_slice bs 0
  have hs40 : ∀ bs : List (BitVec 8), fe51ValOfBytes (List.take 40 (List.drop 40 bs)) = fe51ValAt bs 40 :=
    fun bs => fe51ValOfBytes_slice bs 40
  have hs80 : ∀ bs : List (BitVec 8), fe51ValOfBytes (List.take 40 (List.drop 80 bs)) = fe51ValAt bs 80 :=
    fun bs => fe51ValOfBytes_slice bs 80
  rw [hs0, hs80] at hw hw1
  rw [hs40, hs80] at hw2 hw3
  unfold edPointEq edExtOfBytes fpMul
  simp only [Nat.mod_mod, ← Nat.mul_mod]
  rw [hw, hw1, hw2, hw3]

theorem fe51LimbsBounded_take40 (bs : List (BitVec 8)) (hlen : bs.length = 160)
    (h : fe51LimbsBoundedAt bs 0 18014398509481984) :
    (bs.take 40).length = 40 ∧
    (ByteSlice.readLE (bs.take 40) 0 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE (bs.take 40) 8 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE (bs.take 40) 16 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE (bs.take 40) 24 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE (bs.take 40) 32 8).toNat < 18014398509481984 := by
  haveI : HasLenGe bs 160 := ⟨Nat.le_of_eq hlen.symm⟩
  exact fe51LimbsBounded_slice_of_at 18014398509481984 h

theorem fe51LimbsBounded_drop40_take40 (bs : List (BitVec 8)) (hlen : bs.length = 160)
    (h : fe51LimbsBoundedAt bs 40 18014398509481984) :
    ((bs.drop 40).take 40).length = 40 ∧
    (ByteSlice.readLE ((bs.drop 40).take 40) 0 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 40).take 40) 8 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 40).take 40) 16 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 40).take 40) 24 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 40).take 40) 32 8).toNat < 18014398509481984 := by
  haveI : HasLenGe bs 160 := ⟨Nat.le_of_eq hlen.symm⟩
  exact fe51LimbsBounded_slice_of_at 18014398509481984 h

theorem fe51LimbsBounded_drop80_take40 (bs : List (BitVec 8)) (hlen : bs.length = 160)
    (h : fe51LimbsBoundedAt bs 80 18014398509481984) :
    ((bs.drop 80).take 40).length = 40 ∧
    (ByteSlice.readLE ((bs.drop 80).take 40) 0 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 80).take 40) 8 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 80).take 40) 16 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 80).take 40) 24 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE ((bs.drop 80).take 40) 32 8).toNat < 18014398509481984 := by
  haveI : HasLenGe bs 160 := ⟨Nat.le_of_eq hlen.symm⟩
  exact fe51LimbsBounded_slice_of_at 18014398509481984 h

theorem fe51_to_bytes_of_bytes (w : List (BitVec 8))
    (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0_eq : ByteSlice.readLE w 0 8 = l0)
    (hl1_eq : ByteSlice.readLE w 8 8 = l1)
    (hl2_eq : ByteSlice.readLE w 16 8 = l2)
    (hl3_eq : ByteSlice.readLE w 24 8 = l3)
    (hl4_eq : ByteSlice.readLE w 32 8 = l4)
    (hl0 : l0.toNat < 4503599627370496) (hl1 : l1.toNat < 4503599627370496)
    (hl2 : l2.toNat < 4503599627370496) (hl3 : l3.toNat < 4503599627370496)
    (hl4 : l4.toNat < 4503599627370496)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0)
    (hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1)
    (hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2)
    (hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3)
    (hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4)
    (hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q)
    (hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0)
    (hu1 : h1 + u0 >>> 51 = u1)
    (hu2 : h2 + u1 >>> 51 = u2)
    (hu3 : h3 + u2 >>> 51 = u3)
    (hu4 : h4 + u3 >>> 51 = u4) :
    packCanonical51Bytes u0 u1 u2 u3 u4 = natToLeBytes 32 (fe51ValOfBytes w % p25519) := by
  have hb : 4503599627370496 < 2 ^ 54 := by decide
  rw [fe51ValOfBytes, hl0_eq, hl1_eq, hl2_eq, hl3_eq, hl4_eq]
  exact fe51_to_bytes_math l0 l1 l2 l3 l4
    (Nat.lt_trans hl0 hb) (Nat.lt_trans hl1 hb) (Nat.lt_trans hl2 hb)
    (Nat.lt_trans hl3 hb) (Nat.lt_trans hl4 hb)
    h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
    hh0.symm hh1.symm hh2.symm hh3.symm hh4.symm hq.symm hu0.symm hu1.symm hu2.symm hu3.symm hu4.symm



theorem compress_recip_eq_fpInv (z t19 t3 t2_5 recip : Nat)
    (ht19 : t19 % p25519 = fpPow (z % p25519) (2 ^ 250 - 1))
    (ht3 : t3 % p25519 = fpPow (z % p25519) 11)
    (ht2_5 : t2_5 % p25519 = fpPow (t19 % p25519) (2 ^ 5))
    (hrecip : recip % p25519 = (t2_5 * t3) % p25519) :
    recip % p25519 = fpInv (z % p25519) := by
  unfold fpInv
  have h1 : 2 ^ 250 - 1 < 2 ^ 256 := by decide +kernel
  have h2 : 11 < 2 ^ 256 := by decide +kernel
  have h3 : 2 ^ 5 < 2 ^ 256 := by decide +kernel
  have h4 : p25519 - 2 < 2 ^ 256 := by decide +kernel
  have heq : (2 ^ 250 - 1) * (2 ^ 5) + 11 = p25519 - 2 := by decide +kernel
  generalize (2 ^ 250 - 1) = e1 at ht19 h1 heq
  generalize (11 : Nat) = e2 at ht3 h2 heq
  generalize (2 ^ 5) = e3 at ht2_5 h3 heq
  generalize (p25519 - 2) = e4 at h4 heq ⊢
  rw [hrecip, Nat.mul_mod, ht2_5, ht3, ht19,
      fpPow_eq_pow_mod _ _ h3, fpPow_mod_eq_pow_mod _ _ h1,
      fpPow_mod_eq_pow_mod _ _ h2, fpPow_mod_eq_pow_mod _ _ h4,
      ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod, ← Nat.pow_add, heq]

/-- Set bit 7 of byte 31 of a 32-byte list via bitwise OR with `(sign <<< 7)`. -/
@[expose] def setByte31Or (bs : List (BitVec 8)) (sign : BitVec 8) : List (BitVec 8) :=
  bs.set 31 (bs.getD 31 0#8 ||| (sign <<< 7))

theorem ux0_and1_eq_hx0_add_qx_and1 (hx0 qx ux0 : BitVec 64)
    (hux0 : hx0 + BitVec.setWidth 64 (BitVec.setWidth 32 qx) * 19#64 = ux0) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.setWidth 32 (hx0 + qx)) &&& 1#64) =
      BitVec.truncate 8 (ux0 &&& 1#64) := by
  subst hux0; bv_bits

theorem bv8_or_shl7_ofNat (a b : Nat) (ha : a < 128) (hb : b < 2) :
    (BitVec.ofNat 8 a ||| (BitVec.ofNat 8 b <<< 7)) = BitVec.ofNat 8 ((a + b * 128) % 256) := by
  have : (a + b * 128) % 256 = a + b * 128 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp
  · have hlt : (BitVec.ofNat 8 a).toNat < 128 := by rw [BitVec.toNat_ofNat]; omega
    have h128 : BitVec.ofNat 8 (a + 1 * 128) = BitVec.ofNat 8 a + 128#8 := by
      rw [BitVec.ofNat_add]
    rw [h128]; bv_bits

theorem natToLeBytes_getElem_eq (len n i : Nat) (hi : i < len) :
    (natToLeBytes len n)[i]'(by simp [natToLeBytes, hi]) = BitVec.ofNat 8 ((n / 256 ^ i) % 256) := by
  simp [natToLeBytes]

theorem natToLeBytes_getD_31 (y : Nat) :
    (natToLeBytes 32 y).getD 31 0#8 = BitVec.ofNat 8 ((y / 256 ^ 31) % 256) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [natToLeBytes]),
      Option.getD_some, natToLeBytes_getElem_eq 32 y 31 (by omega)]

theorem setByte31Or_natToLeBytes_eq (y s : Nat) (hy : y < p25519) (hs : s < 2) :
    setByte31Or (natToLeBytes 32 y) (BitVec.ofNat 8 s) =
      natToLeBytes 32 (y + s * 2 ^ 255) := by
  unfold setByte31Or
  apply List.ext_getElem
  · simp [natToLeBytes]
  · intro i hi1 hi2
    have hi : i < 32 := by simp [natToLeBytes] at hi1; exact hi1
    rw [List.getElem_set]
    by_cases h31 : 31 = i
    · subst h31
      rw [ite_eq_left rfl, natToLeBytes_getD_31,
          natToLeBytes_getElem_eq 32 (y + s * 2 ^ 255) 31 (by omega)]
      have hy_div : y / 256 ^ 31 < 128 := by
        have : p25519 < 128 * 256 ^ 31 := by decide +kernel
        omega
      have hy_mod : (y / 256 ^ 31) % 256 = y / 256 ^ 31 := Nat.mod_eq_of_lt (by omega)
      have h_add_div : (y + s * 2 ^ 255) / 256 ^ 31 = y / 256 ^ 31 + s * 128 := by
        have : s * 2 ^ 255 = (s * 128) * 256 ^ 31 := by
          rw [show (2 : Nat) ^ 255 = 128 * 256 ^ 31 by decide +kernel, Nat.mul_assoc]
        rw [this, Nat.add_mul_div_right _ _ (by decide +kernel)]
      rw [hy_mod, h_add_div, bv8_or_shl7_ofNat _ _ hy_div hs]
    · rw [ite_eq_right h31, natToLeBytes_getElem_eq 32 y i hi,
          natToLeBytes_getElem_eq 32 (y + s * 2 ^ 255) i hi]
      have h_mod : ((y + s * 2 ^ 255) / 256 ^ i) % 256 = (y / 256 ^ i) % 256 := by
        have h_pow : 256 ^ i * (256 * 256 ^ (30 - i)) = 256 ^ 31 := by
          rw [← Nat.pow_succ', ← Nat.pow_add, show i + (30 - i + 1) = 31 by omega]
        have h_mul : s * 2 ^ 255 = (256 * (s * (128 * 256 ^ (30 - i)))) * 256 ^ i := by
          calc s * 2 ^ 255 = s * (128 * 256 ^ 31) := by
                rw [show (2 : Nat) ^ 255 = 128 * 256 ^ 31 by decide +kernel]
            _ = s * (128 * (256 ^ i * (256 * 256 ^ (30 - i)))) := by rw [← h_pow]
            _ = (256 * (s * (128 * 256 ^ (30 - i)))) * 256 ^ i := by
                simp only [Nat.mul_left_comm, Nat.mul_comm]
        have hpos : 0 < 256 ^ i := Nat.pow_pos (by decide)
        rw [h_mul, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_left]
      rw [h_mod]

theorem pointsToBytes_setByte31Or_packCanonical51Bytes
    (p : BitVec 64) (u0 u1 u2 u3 u4 : BitVec 64) (sign : BitVec 8) :
    ((p ↦₈ BitVec.zeroExtend 8 u0) ∗
     ((p + 1#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 8)) ∗
     ((p + 2#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 16)) ∗
     ((p + 3#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 24)) ∗
     ((p + 4#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 32)) ∗
     ((p + 5#64) ↦₈ BitVec.zeroExtend 8 (u0 >>> 40)) ∗
     ((p + 6#64) ↦₈ BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
       (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3)) ∗
     ((p + 7#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 5)) ∗
     ((p + 8#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 13)) ∗
     ((p + 9#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 21)) ∗
     ((p + 10#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 29)) ∗
     ((p + 11#64) ↦₈ BitVec.zeroExtend 8 (u1 >>> 37)) ∗
     ((p + 12#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6)) ∗
     ((p + 13#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 2)) ∗
     ((p + 14#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 10)) ∗
     ((p + 15#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 18)) ∗
     ((p + 16#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 26)) ∗
     ((p + 17#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 34)) ∗
     ((p + 18#64) ↦₈ BitVec.zeroExtend 8 (u2 >>> 42)) ∗
     ((p + 19#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1)) ∗
     ((p + 20#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 7)) ∗
     ((p + 21#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 15)) ∗
     ((p + 22#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 23)) ∗
     ((p + 23#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 31)) ∗
     ((p + 24#64) ↦₈ BitVec.zeroExtend 8 (u3 >>> 39)) ∗
     ((p + 25#64) ↦₈ BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4)) ∗
     ((p + 26#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 4)) ∗
     ((p + 27#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 12)) ∗
     ((p + 28#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 20)) ∗
     ((p + 29#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 28)) ∗
     ((p + 30#64) ↦₈ BitVec.zeroExtend 8 (u4 >>> 36)) ∗
     ((p + 31#64) ↦₈ (BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64) ||| (sign <<< 7)))) =
    (p ↦ₛ setByte31Or (packCanonical51Bytes u0 u1 u2 u3 u4) sign) := by
  rw [setByte31Or, packCanonical51Bytes]
  simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    List.set_cons_succ, List.set_cons_zero]
  rw [pointsToBytes_list32]

theorem truncate8_and1_eq_ofNat_mod2 (u0 : BitVec 64) :
    BitVec.truncate 8 (u0 &&& 1#64) = BitVec.ofNat 8 (u0.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  bv_bits

theorem fe51_sign_of_bytes (bs : List (BitVec 8))
    (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0_eq : ByteSlice.readLE bs 0 8 = l0)
    (hl1_eq : ByteSlice.readLE bs 8 8 = l1)
    (hl2_eq : ByteSlice.readLE bs 16 8 = l2)
    (hl3_eq : ByteSlice.readLE bs 24 8 = l3)
    (hl4_eq : ByteSlice.readLE bs 32 8 = l4)
    (hl0 : l0.toNat < 2 ^ 52) (hl1 : l1.toNat < 2 ^ 52)
    (hl2 : l2.toNat < 2 ^ 52) (hl3 : l3.toNat < 2 ^ 52) (hl4 : l4.toNat < 2 ^ 52)
    (h0 h1 h2 h3 h4 q : BitVec 64)
    (hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0)
    (hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1)
    (hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2)
    (hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3)
    (hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4)
    (hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.setWidth 32 (h0 + q)) &&& 1#64) =
      BitVec.ofNat 8 ((fe51ValOfBytes bs % p25519) % 2) := by
  let u0 := h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64
  let u1 := h1 + u0 >>> 51
  let u2 := h2 + u1 >>> 51
  let u3 := h3 + u2 >>> 51
  let u4 := h4 + u3 >>> 51
  have hval : fe51ValOfBytes bs = fe51Val l0 l1 l2 l3 l4 := by
    rw [fe51ValOfBytes, hl0_eq, hl1_eq, hl2_eq, hl3_eq, hl4_eq]
  have hb : (2 : Nat) ^ 52 < 2 ^ 54 := by decide
  have hcan := fe51_to_bytes_canonical_val l0 l1 l2 l3 l4
    (Nat.lt_trans hl0 hb) (Nat.lt_trans hl1 hb) (Nat.lt_trans hl2 hb) (Nat.lt_trans hl3 hb) (Nat.lt_trans hl4 hb)
    h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
    hh0.symm hh1.symm hh2.symm hh3.symm hh4.symm hq.symm rfl rfl rfl rfl rfl
  rw [ux0_and1_eq_hx0_add_qx_and1 h0 q u0 rfl, truncate8_and1_eq_ofNat_mod2,
      hval, hcan, fe51_canonical_mod2]


theorem fe51LimbsBounded_of_52 (bs : List (BitVec 8))
    (h : fe51LimbsBounded bs (2 ^ 52)) :
    bs.length = 40 ∧
    (ByteSlice.readLE bs 0 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE bs 8 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE bs 16 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE bs 24 8).toNat < 18014398509481984 ∧
    (ByteSlice.readLE bs 32 8).toNat < 18014398509481984 := by
  have hb : 2 ^ 52 < 18014398509481984 := by decide
  exact ⟨h.1, Nat.lt_trans h.2.1 hb, Nat.lt_trans h.2.2.1 hb,
    Nat.lt_trans h.2.2.2.1 hb, Nat.lt_trans h.2.2.2.2.1 hb, Nat.lt_trans h.2.2.2.2.2 hb⟩



theorem compress_byte31_eq (u4 r_bb : BitVec 64) :
    BitVec.truncate 8 (BitVec.setWidth 32 (u4 >>> 44 &&& 127#64) ||| BitVec.setWidth 32 r_bb <<< 7) =
      BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64) ||| (BitVec.zeroExtend 8 r_bb <<< 7) := by
  bv_bits

theorem encodeEd_of_muls (self_bs t19_bs t3_bs t2_5_bs recip_bs x_bs y_bs : List (BitVec 8))
    (ht19 : fe51ValOfBytes t19_bs % p25519 = fpPow (fe51ValOfBytes ((self_bs.drop 80).take 40) % p25519) (2 ^ 250 - 1))
    (ht3 : fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes ((self_bs.drop 80).take 40) % p25519) 11)
    (ht2_5 : fe51ValOfBytes t2_5_bs % p25519 = fpPow (fe51ValOfBytes t19_bs % p25519) (2 ^ (5#32 : BitVec 32).toNat))
    (hrecip : fe51ValOfBytes recip_bs % p25519 = (fe51ValOfBytes t2_5_bs * fe51ValOfBytes t3_bs) % p25519)
    (hx : fe51ValOfBytes x_bs % p25519 = (fe51ValOfBytes (self_bs.take 40) * fe51ValOfBytes recip_bs) % p25519)
    (hy : fe51ValOfBytes y_bs % p25519 = (fe51ValOfBytes ((self_bs.drop 40).take 40) * fe51ValOfBytes recip_bs) % p25519) :
    setByte31Or (natToLeBytes 32 (fe51ValOfBytes y_bs % p25519))
        (BitVec.ofNat 8 ((fe51ValOfBytes x_bs % p25519) % 2)) =
      encodeEd (edExtToAffine (edExtOfBytes self_bs)) := by
  have hp : 0 < p25519 := by decide +kernel
  have hs0 : fe51ValOfBytes (self_bs.take 40) = fe51ValAt self_bs 0 := fe51ValOfBytes_slice self_bs 0
  have hs40 : fe51ValOfBytes ((self_bs.drop 40).take 40) = fe51ValAt self_bs 40 := fe51ValOfBytes_slice self_bs 40
  have hs80 : fe51ValOfBytes ((self_bs.drop 80).take 40) = fe51ValAt self_bs 80 := fe51ValOfBytes_slice self_bs 80
  have h_inv : fe51ValOfBytes recip_bs % p25519 = fpInv ((edExtOfBytes self_bs).Z) := by
    have hz : (edExtOfBytes self_bs).Z = fe51ValOfBytes ((self_bs.drop 80).take 40) % p25519 := by
      unfold edExtOfBytes; rw [hs80]
    rw [hz]
    exact compress_recip_eq_fpInv _ _ _ _ _ ht19 ht3 ht2_5 hrecip
  have hx_eq : fe51ValOfBytes x_bs % p25519 = (edExtToAffine (edExtOfBytes self_bs)).x % p25519 := by
    have hX : (edExtOfBytes self_bs).X = fe51ValOfBytes (self_bs.take 40) % p25519 := by
      unfold edExtOfBytes; rw [hs0]
    dsimp only [edExtToAffine, fpMul]
    rw [hx, Nat.mul_mod (fe51ValOfBytes _), h_inv, ← hX, Nat.mod_mod, ← Nat.mul_mod]
  have hy_eq : fe51ValOfBytes y_bs % p25519 = (edExtToAffine (edExtOfBytes self_bs)).y % p25519 := by
    have hY : (edExtOfBytes self_bs).Y = fe51ValOfBytes ((self_bs.drop 40).take 40) % p25519 := by
      unfold edExtOfBytes; rw [hs40]
    dsimp only [edExtToAffine, fpMul]
    rw [hy, Nat.mul_mod (fe51ValOfBytes _), h_inv, ← hY, Nat.mod_mod, ← Nat.mul_mod]
  unfold encodeEd
  rw [hx_eq, hy_eq, setByte31Or_natToLeBytes_eq _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ (by decide))]

theorem write64_copy5_eq (old src : List (BitVec 8))
    (hold : old.length = 40) (hsrc : src.length = 40) :
    ByteSlice.write64
      (ByteSlice.write64
        (ByteSlice.write64
          (ByteSlice.write64
            (ByteSlice.write64 old 0 (ByteSlice.readLE src 0 8)) 8
            (ByteSlice.readLE src 8 8))
          16 (ByteSlice.readLE src 16 8))
        24 (ByteSlice.readLE src 24 8))
      32 (ByteSlice.readLE src 32 8) = src := by
  conv => lhs; arg 1; arg 1; arg 1; arg 1; arg 1
          rw [← ByteSlice.copyPrefix_zero old src]
  rw [ByteSlice.write64_copyPrefix_readLE old src 0 (by omega),
      ByteSlice.write64_copyPrefix_readLE old src 8 (by omega),
      ByteSlice.write64_copyPrefix_readLE old src 16 (by omega),
      ByteSlice.write64_copyPrefix_readLE old src 24 (by omega),
      ByteSlice.write64_copyPrefix_readLE old src 32 (by omega),
      ByteSlice.copyPrefix_full hold hsrc]

theorem sub_add_eq_sub_sub (sp off k : BitVec 64) :
    (sp - off) + k = sp - (off - k) := by
  bv_bits


theorem pointsToBytes40_sub_eq_cells (sp off o8 o16 o24 o32 : BitVec 64)
    (bs : List (BitVec 8)) (h : bs.length = 40)
    (h8 : off - 8#64 = o8 := by rfl)
    (h16 : off - 16#64 = o16 := by rfl)
    (h24 : off - 24#64 = o24 := by rfl)
    (h32 : off - 32#64 = o32 := by rfl) :
    ((sp - off) ↦ₛ bs) =
      (((sp - off) ↦₆₄ ByteSlice.readLE bs 0 8) ∗
       ((sp - o8) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
       ((sp - o16) ↦₆₄ ByteSlice.readLE bs 16 8) ∗
       ((sp - o24) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
       ((sp - o32) ↦₆₄ ByteSlice.readLE bs 32 8)) := by
  rw [pointsToBytes40_eq_cells (sp - off) bs h,
      sub_add_eq_sub_sub, h8,
      sub_add_eq_sub_sub, h16,
      sub_add_eq_sub_sub, h24,
      sub_add_eq_sub_sub, h32]



theorem sepWP_split32_sub (sp off_lo off_hi : BitVec 64)
    {v : BitVec 64} {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - off_lo) ↦₆₄ v) ∗ P := by sep_frame)
    (hoff : off_lo - 4#64 = off_hi := by rfl)
    (hnext : SepWP prog target_pc s
      (((sp - off_lo) ↦₃₂ v.truncate 32) ∗ ((sp - off_hi) ↦₃₂ v.extractLsb' 32 32) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsTo64_split32_sub sp off_lo off_hi v P hoff]
  exact hnext

theorem sepWP_combine32_sub (sp off_lo off_hi : BitVec 64)
    {lo hi : BitVec 32} {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - off_lo) ↦₃₂ lo) ∗ ((sp - off_hi) ↦₃₂ hi)) ∗ P := by sep_frame)
    (hoff : off_lo - 4#64 = off_hi := by rfl)
    (hnext : SepWP prog target_pc s (((sp - off_lo) ↦₆₄ (hi ++ lo)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, sepConj_assoc, pointsTo32_combine64_sub sp off_lo off_hi lo hi P hoff]
  exact hnext


theorem sepWP_split_bytes_append (sp : BitVec 64) (off k rem : Nat)
    {bs1 bs2 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - BitVec.ofNat 64 off) ↦ₛ (bs1 ++ bs2)) ∗ P := by sep_frame)
    (hbs1 : bs1.length = k)
    (hrem : off - k = rem := by decide)
    (hle : k ≤ off := by decide)
    (hnext : SepWP prog target_pc s
      ((((sp - BitVec.ofNat 64 off) ↦ₛ bs1) ∗
        ((sp - BitVec.ofNat 64 rem) ↦ₛ bs2)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsToBytes_append, hbs1, sub_ofNat64_add sp off k hle, hrem]
  exact hnext

/-- `<curve25519_dalek::edwards::EdwardsPoint>::compress` (`B14`, 204 insns, stack 1552):
    compresses the extended Edwards point at `self` (`x0`) into 32 little-endian bytes at
    `out` (`x8` `sret`). -/
rust_spec edwardsPointCompressSpec (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ fe51Point4Bounded self_bs (2 ^ 54)
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         1552
  ensures       out ↦ₛ encodeEd (edExtToAffine (edExtOfBytes self_bs))

theorem pointsToBytes168_split (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 168) :
    (a ↦ₛ bs) = (a ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) := by
  rw [pointsToBytes_take_drop a 8 bs (by omega),
      show bs.take 8 = (bs.drop 0).take 8 from rfl,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (by omega),
      ByteSlice.pack64_eq_readLE_8]

theorem fe51EdwardsDBytes_bounded : fe51LimbsBounded fe51EdwardsDBytes (2 ^ 54) := by
  unfold fe51LimbsBounded
  decide +kernel



theorem fe51LimbsBoundedAt_mono {bs : List (BitVec 8)} {off b1 b2 : Nat}
    (h : fe51LimbsBoundedAt bs off b1) (hle : decide (b1 ≤ b2) = true := by decide) :
    fe51LimbsBoundedAt bs off b2 := by
  have hb : b1 ≤ b2 := of_decide_eq_true hle
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem sepWP_peel_stack_region (sp : BitVec 64) (off n rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - BitVec.ofNat 64 off) off ∗ P := by sep_frame)
    (hoff : off = n + rem := by decide)
    (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s
      ((memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by
    rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit : memRegion (sp - BitVec.ofNat 64 off) off =
      memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem := by
    have h1 := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb)
    rw [← hoff, haddr] at h1; exact h1
  rw [hf, hsplit]; exact hnext

theorem sepWP_unpeel_stack_region (sp : BitVec 64) (off n rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P := by sep_frame)
    (hoff : off = n + rem := by decide)
    (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - BitVec.ofNat 64 off) off ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by
    rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit : memRegion (sp - BitVec.ofNat 64 off) off =
      memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem := by
    have h1 := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb)
    rw [← hoff, haddr] at h1; exact h1
  rw [hf, ← hsplit]; exact hnext

theorem sepWP_resize_callee_576 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 576 := by decide) (hok : 1904 + k = off_k := by decide)
    (hf : Full = memRegion (sp0 - 2480#64) 576 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp0 - 1904#64 - BitVec.ofNat 64 k) k ∗
      stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 2480#64 = sp0 - 1904#64 - 576#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - 1904#64 - BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 off_k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha0]; change SepWP prog target_pc s (stackAt (sp0 - 1904#64) 576 ∗ P) post oom
  rw [← hsum, stackAt_region (sp0 - 1904#64) low k (by omega), sepConj_comm (stackAt _ _) (memRegion _ _)]
  conv => arg 4; arg 1; arg 2; rw [ha]
  exact hnext

theorem sepWP_unresize_callee_576 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 576 := by decide) (hok : 1904 + k = off_k := by decide)
    (hf : Full = (memRegion (sp0 - 1904#64 - BitVec.ofNat 64 k) k ∗
      stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp0 - 2480#64) 576 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 1904#64 - 576#64 = sp0 - 2480#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - BitVec.ofNat 64 off_k = sp0 - 1904#64 - BitVec.ofNat 64 k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp0 - 1904#64) low k (by omega), hsum]
  change SepWP prog target_pc s (memRegion (sp0 - 1904#64 - 576#64) 576 ∗ P) post oom
  rw [ha0]; exact hnext

private theorem completed_split4_props_54_ltp (bs : List (BitVec 8)) (C : EdExtPoint) (hbs : bs.length = 160)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 54)) (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 54))
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54)) (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 54))
    (hval : edExtOfBytes bs = C) :
    let b0 := bs.take 40; let b1 := (bs.drop 40).take 40
    let b2 := ((bs.drop 40).drop 40).take 40; let b3 := ((bs.drop 40).drop 40).drop 40
    fe51LimbsBounded b0 (2 ^ 54) ∧ fe51LimbsBounded b1 (2 ^ 54) ∧
    fe51LimbsBounded b2 (2 ^ 54) ∧ fe51LimbsBounded b3 (2 ^ 54) ∧
    fe51ValOfBytes b0 % p25519 = C.X ∧ fe51ValOfBytes b1 % p25519 = C.Y ∧
    fe51ValOfBytes b2 % p25519 = C.Z ∧ fe51ValOfBytes b3 % p25519 = C.T := by
  intro b0 b1 b2 b3
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hbs]
  have hb2_l : b2.length = 40 := by simp [b2, hbs]
  have hb3_l : b3.length = 40 := by simp [b3, hbs]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    rw [List.take_append_drop 40 ((bs.drop 40).drop 40), List.take_append_drop 40 (bs.drop 40), List.take_append_drop 40 bs]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, show off - 40 - 40 = off - 80 by omega, readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l, show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51LimbsBoundedAt at h0 h40 h80 h120
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0 h40 h80 h120
  have hval' : edExtOfBytes bs = ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
      fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub]
    rfl
  rw [hval] at hval'; refine ⟨⟨hb0_l, h0⟩, ⟨hb1_l, h40⟩, ⟨hb2_l, h80⟩, ⟨hb3_l, h120⟩, ?_⟩
  rw [hval']; exact ⟨rfl, rfl, rfl, rfl⟩


theorem sepWP_split4_completed_264 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 264#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 54) := by assumption) (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 54) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54) := by assumption) (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 54) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s ((((sp - 264#64) ↦ₛ b0) ∗ ((sp - 224#64) ↦ₛ b1) ∗
        ((sp - 184#64) ↦ₛ b2) ∗ ((sp - 144#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 264#64) ↦ₛ bs) = ((sp - 264#64) ↦ₛ bs.take 40) ∗ ((sp - 224#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 264 40]
  have hs1 : ((sp - 224#64) ↦ₛ d1) = ((sp - 224#64) ↦ₛ d1.take 40) ∗ ((sp - 184#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 224 40]
  have hs2 : ((sp - 184#64) ↦ₛ d2) = ((sp - 184#64) ↦ₛ d2.take 40) ∗ ((sp - 144#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 184 40]
  obtain ⟨hb0, hb1, hb2, hb3, hv0, hv1, hv2, hv3⟩ := completed_split4_props_54_ltp bs C hbs h0 h40 h80 h120 hval
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    hb0.1 hb1.1 hb2.1 hb3.1 hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3

theorem sepWP_merge4_stack_264 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 264#64) ↦ₛ b0) ∗ ((sp - 224#64) ↦ₛ b1) ∗
                  ((sp - 184#64) ↦ₛ b2) ∗ ((sp - 144#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption) (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 →
      SepWP prog target_pc s (((sp - 264#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 184#64 + BitVec.ofNat 64 b2.length = sp - 144#64 := by rw [h2]; exact sub_ofNat64_add sp 184 40
  have ha1 : sp - 224#64 + BitVec.ofNat 64 b1.length = sp - 184#64 := by rw [h1]; exact sub_ofNat64_add sp 224 40
  have ha0 : sp - 264#64 + BitVec.ofNat 64 b0.length = sp - 224#64 := by rw [h0]; exact sub_ofNat64_add sp 264 40
  have hm : ((sp - 264#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 264#64) ↦ₛ b0) ∗ ((sp - 224#64) ↦ₛ b1) ∗ ((sp - 184#64) ↦ₛ b2) ∗ ((sp - 144#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

theorem sepWP_split4_stack (sp : BitVec 64) (off0 off1 off2 off3 : Nat) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (ho0 : off0 = off1 + 40 := by decide) (ho1 : off1 = off2 + 40 := by decide)
    (ho2 : off2 = off3 + 40 := by decide) (hb : off0 ≤ 2 ^ 64 := by decide)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s ((((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) ∗
        ((sp - BitVec.ofNat 64 off2) ↦ₛ b2) ∗ ((sp - BitVec.ofNat 64 off3) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ bs.take 40) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp off0 40 (by omega), show off0 - 40 = off1 by omega]
  have hs1 : ((sp - BitVec.ofNat 64 off1) ↦ₛ d1) =
      ((sp - BitVec.ofNat 64 off1) ↦ₛ d1.take 40) ∗ ((sp - BitVec.ofNat 64 off2) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp off1 40 (by omega), show off1 - 40 = off2 by omega]
  have hs2 : ((sp - BitVec.ofNat 64 off2) ↦ₛ d2) =
      ((sp - BitVec.ofNat 64 off2) ↦ₛ d2.take 40) ∗ ((sp - BitVec.ofNat 64 off3) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide),
        sub_ofNat64_add sp off2 40 (by omega), show off2 - 40 = off3 by omega]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

theorem sepWP_merge4_stack (sp : BitVec 64) (off0 off1 off2 off3 : Nat)
    {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (Q : List (BitVec 8) → Prop)
    (hf : Full = ((((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) ∗
                   ((sp - BitVec.ofNat 64 off2) ↦ₛ b2) ∗ ((sp - BitVec.ofNat 64 off3) ↦ₛ b3)) ∗ P) := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption) (h2 : b2.length = 40 := by assumption)
    (ho0 : off0 = off1 + 40 := by decide) (ho1 : off1 = off2 + 40 := by decide)
    (ho2 : off2 = off3 + 40 := by decide) (hb : off0 ≤ 2 ^ 64 := by decide)
    (hQ : Q (b0 ++ (b1 ++ (b2 ++ b3))))
    (hnext : ∀ res_bs : List (BitVec 8), Q res_bs →
      SepWP prog target_pc s (((sp - BitVec.ofNat 64 off0) ↦ₛ res_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - BitVec.ofNat 64 off2 + BitVec.ofNat 64 b2.length = sp - BitVec.ofNat 64 off3 := by
    rw [h2, sub_ofNat64_add sp off2 40 (by omega), show off2 - 40 = off3 by omega]
  have ha1 : sp - BitVec.ofNat 64 off1 + BitVec.ofNat 64 b1.length = sp - BitVec.ofNat 64 off2 := by
    rw [h1, sub_ofNat64_add sp off1 40 (by omega), show off1 - 40 = off2 by omega]
  have ha0 : sp - BitVec.ofNat 64 off0 + BitVec.ofNat 64 b0.length = sp - BitVec.ofNat 64 off1 := by
    rw [h0, sub_ofNat64_add sp off0 40 (by omega), show off0 - 40 = off1 by omega]
  have hm : ((sp - BitVec.ofNat 64 off0) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) ∗
      ((sp - BitVec.ofNat 64 off2) ↦ₛ b2) ∗ ((sp - BitVec.ofNat 64 off3) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) hQ

theorem write64_5_len {s : List (BitVec 8)} {v0 v1 v2 v3 v4 : BitVec 64} {o0 o1 o2 o3 o4 n : Nat}
    (h : decide (o0 + 8 ≤ n ∧ o1 + 8 ≤ n ∧ o2 + 8 ≤ n ∧ o3 + 8 ≤ n ∧ o4 + 8 ≤ n) = true) (hs : s.length = n) :
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 s o0 v0) o1 v1) o2 v2) o3 v3) o4 v4).length = n := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := of_decide_eq_true h
  have l0 : (ByteSlice.write64 s o0 v0).length = n := by rw [write64_length_eq]; omega
  have l1 : (ByteSlice.write64 (ByteSlice.write64 s o0 v0) o1 v1).length = n := by rw [write64_length_eq, l0]; omega
  have l2 : (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 s o0 v0) o1 v1) o2 v2).length = n := by rw [write64_length_eq, l1]; omega
  have l3 : (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 s o0 v0) o1 v1) o2 v2) o3 v3).length = n := by rw [write64_length_eq, l2]; omega
  rw [write64_length_eq, l3]; omega

theorem write64_1_len {s : List (BitVec 8)} {v0 : BitVec 64} {o0 n : Nat}
    (h : decide (o0 + 8 ≤ n) = true) (hs : s.length = n) : (ByteSlice.write64 s o0 v0).length = n := by
  have hd := of_decide_eq_true h; rw [write64_length_eq]; omega

scoped macro "prove_write64_len" : tactic =>
  `(tactic| ((repeat' ((with_reducible apply write64_5_len); decide));
             (repeat' ((with_reducible apply write64_1_len); decide)); first | assumption | omega))

theorem sepWP_merge2_stack (sp : BitVec 64) (off0 off1 n1 : Nat) {b0 b1 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1)) ∗ P := by sep_frame)
    (h0 : b0.length = 120 := by prove_write64_len) (h1 : b1.length = n1 := by assumption)
    (ho : off0 = off1 + 120 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide)
    (hnext : ∀ m_bs : List (BitVec 8), m_bs.length = 120 + n1 →
      ByteSlice.readLE m_bs 80 8 = ByteSlice.readLE b0 80 8 → ByteSlice.readLE m_bs 88 8 = ByteSlice.readLE b0 88 8 →
      ByteSlice.readLE m_bs 96 8 = ByteSlice.readLE b0 96 8 → ByteSlice.readLE m_bs 104 8 = ByteSlice.readLE b0 104 8 →
      ByteSlice.readLE m_bs 112 8 = ByteSlice.readLE b0 112 8 → ByteSlice.readLE m_bs 120 8 = ByteSlice.readLE b1 0 8 →
      ByteSlice.readLE m_bs 128 8 = ByteSlice.readLE b1 8 8 → ByteSlice.readLE m_bs 136 8 = ByteSlice.readLE b1 16 8 →
      ByteSlice.readLE m_bs 144 8 = ByteSlice.readLE b1 24 8 → ByteSlice.readLE m_bs 152 8 = ByteSlice.readLE b1 32 8 →
      SepWP prog target_pc s (((sp - BitVec.ofNat 64 off0) ↦ₛ m_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp - BitVec.ofNat 64 off0 + BitVec.ofNat 64 b0.length = sp - BitVec.ofNat 64 off1 := by
    rw [h0, sub_ofNat64_add sp off0 120 (by omega), show off0 - 120 = off1 by omega]
  have hm : ((sp - BitVec.ofNat 64 off0) ↦ₛ (b0 ++ b1)) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) := by
    rw [pointsToBytes_append, ha0]
  rw [hf, ← hm]
  refine hnext (b0 ++ b1) (by rw [List.length_append, h0, h1])
    (readLE_append_left b0 b1 80 8 (by omega)) (readLE_append_left b0 b1 88 8 (by omega))
    (readLE_append_left b0 b1 96 8 (by omega)) (readLE_append_left b0 b1 104 8 (by omega))
    (readLE_append_left b0 b1 112 8 (by omega))
    (by rw [readLE_append_right b0 b1 120 8 (by omega), h0]) (by rw [readLE_append_right b0 b1 128 8 (by omega), h0])
    (by rw [readLE_append_right b0 b1 136 8 (by omega), h0]) (by rw [readLE_append_right b0 b1 144 8 (by omega), h0])
    (by rw [readLE_append_right b0 b1 152 8 (by omega), h0])

theorem sepWP_split2_stack (sp : BitVec 64) (off0 n0 off1 n1 : Nat) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = n0 + n1 := by prove_write64_len)
    (ho : off0 = off1 + n0 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide)
    (hnext : ∀ b0 b1 : List (BitVec 8), b0.length = n0 → b1.length = n1 →
      SepWP prog target_pc s ((((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗
        ((sp - BitVec.ofNat 64 off1) ↦ₛ b1)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hs0 : ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ bs.take n0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ bs.drop n0) := by
    conv => lhs; rw [← List.take_append_drop n0 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by omega),
        sub_ofNat64_add sp off0 n0 (by omega), show off0 - n0 = off1 by omega]
  rw [hf, hs0]; exact hnext (bs.take n0) (bs.drop n0) (by simp [hbs]) (by simp [hbs])

theorem fe51_mro_post_props (w src : List (BitVec 8))
    (hb : fe51LimbsBounded w 4503599627370496 := by assumption)
    (hv : fe51ValOfBytes w % p25519 =
      (fe51ValOfBytes (ProofLib.ByteSlice.slice src 120 40) * fe51ValOfBytes fe51EdwardsD2Bytes) % p25519 := by assumption) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 52) ∧
    fe51ValOfBytes w % p25519 =
      (fe51ValOfBytes (ProofLib.ByteSlice.slice src 120 40) * fe51ValOfBytes fe51EdwardsD2Bytes) % p25519 :=
  ⟨hb.1, hb, hv⟩

scoped macro "clean_sf " prev:ident : tactic =>
  `(tactic| (clean_prev_sf; clear_dead_vars [$prev:ident]; try clear $prev:ident))

theorem fe51EdwardsD2Bytes_bounded54 : fe51LimbsBounded fe51EdwardsD2Bytes (2 ^ 54) := by
  refine ⟨fe51EdwardsD2Bytes_length, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fe51EdwardsD2_readLE_0]; decide
  · rw [fe51EdwardsD2_readLE_8]; decide
  · rw [fe51EdwardsD2_readLE_16]; decide
  · rw [fe51EdwardsD2_readLE_24]; decide
  · rw [fe51EdwardsD2_readLE_32]; decide

/-! ## 3. 160-Byte Chunk Splitting and 8-Entry Table Merging Helpers -/

set_option maxHeartbeats 400000 in

theorem slice_append_left (a b : List (BitVec 8)) {n : Nat} (ha : a.length = n) :
    ProofLib.ByteSlice.slice (a ++ b) 0 n = a := by
  unfold ProofLib.ByteSlice.slice; rw [List.drop_zero, ← ha, List.take_left]

theorem slice_append_right (a b : List (BitVec 8)) (m off n : Nat) {k : Nat}
    (ha : a.length = m) (hoff : m + off = k) :
    ProofLib.ByteSlice.slice (a ++ b) k n = ProofLib.ByteSlice.slice b off n := by
  unfold ProofLib.ByteSlice.slice
  rw [← hoff, ← ha, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem slice_zero_len (a : List (BitVec 8)) {n : Nat} (ha : a.length = n) :
    ProofLib.ByteSlice.slice a 0 n = a := by
  unfold ProofLib.ByteSlice.slice; rw [List.drop_zero, ← ha, List.take_length]

theorem projTable8_of_append8 (A : EdExtPoint) (b0 b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8))
    (h0 : fe51Point4Bounded b0 (2 ^ 54) ∧ edExtOfBytes b0 = projNielsTablePoints A 0)
    (h1 : fe51Point4Bounded b1 (2 ^ 54) ∧ edExtOfBytes b1 = projNielsTablePoints A 1)
    (h2 : fe51Point4Bounded b2 (2 ^ 54) ∧ edExtOfBytes b2 = projNielsTablePoints A 2)
    (h3 : fe51Point4Bounded b3 (2 ^ 54) ∧ edExtOfBytes b3 = projNielsTablePoints A 3)
    (h4 : fe51Point4Bounded b4 (2 ^ 54) ∧ edExtOfBytes b4 = projNielsTablePoints A 4)
    (h5 : fe51Point4Bounded b5 (2 ^ 54) ∧ edExtOfBytes b5 = projNielsTablePoints A 5)
    (h6 : fe51Point4Bounded b6 (2 ^ 54) ∧ edExtOfBytes b6 = projNielsTablePoints A 6)
    (h7 : fe51Point4Bounded b7 (2 ^ 54) ∧ edExtOfBytes b7 = projNielsTablePoints A 7) :
    let res := b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))))
    fe51ProjNielsTable8Bounded res (2 ^ 54) ∧
    ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice res (160 * i) 160) = projNielsTablePoints A i := by
  intro res
  have l0 := h0.1.1; have l1 := h1.1.1; have l2 := h2.1.1; have l3 := h3.1.1
  have l4 := h4.1.1; have l5 := h5.1.1; have l6 := h6.1.1; have l7 := h7.1.1
  have l67 : (b6 ++ b7).length = 320 := by rw [List.length_append, l6, l7]
  have l57 : (b5 ++ (b6 ++ b7)).length = 480 := by rw [List.length_append, l5, l67]
  have l47 : (b4 ++ (b5 ++ (b6 ++ b7))).length = 640 := by rw [List.length_append, l4, l57]
  have l37 : (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7)))).length = 800 := by rw [List.length_append, l3, l47]
  have l27 : (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))).length = 960 := by rw [List.length_append, l2, l37]
  have l17 : (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7)))))).length = 1120 := by rw [List.length_append, l1, l27]
  have l07 : res.length = 1280 := by change (b0 ++ _).length = 1280; rw [List.length_append, l0, l17]
  have s0 : ProofLib.ByteSlice.slice res 0 160 = b0 := slice_append_left b0 _ l0
  have s1 : ProofLib.ByteSlice.slice res 160 160 = b1 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 160 160 = b1; rw [slice_append_right b0 _ 160 0 160 l0 rfl, slice_append_left b1 _ l1]
  have s2 : ProofLib.ByteSlice.slice res 320 160 = b2 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 320 160 = b2
    rw [slice_append_right b0 _ 160 160 160 l0 rfl, slice_append_right b1 _ 160 0 160 l1 rfl, slice_append_left b2 _ l2]
  have s3 : ProofLib.ByteSlice.slice res 480 160 = b3 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 480 160 = b3
    rw [slice_append_right b0 _ 160 320 160 l0 rfl, slice_append_right b1 _ 160 160 160 l1 rfl, slice_append_right b2 _ 160 0 160 l2 rfl, slice_append_left b3 _ l3]
  have s4 : ProofLib.ByteSlice.slice res 640 160 = b4 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 640 160 = b4
    rw [slice_append_right b0 _ 160 480 160 l0 rfl, slice_append_right b1 _ 160 320 160 l1 rfl, slice_append_right b2 _ 160 160 160 l2 rfl, slice_append_right b3 _ 160 0 160 l3 rfl, slice_append_left b4 _ l4]
  have s5 : ProofLib.ByteSlice.slice res 800 160 = b5 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 800 160 = b5
    rw [slice_append_right b0 _ 160 640 160 l0 rfl, slice_append_right b1 _ 160 480 160 l1 rfl, slice_append_right b2 _ 160 320 160 l2 rfl, slice_append_right b3 _ 160 160 160 l3 rfl, slice_append_right b4 _ 160 0 160 l4 rfl, slice_append_left b5 _ l5]
  have s6 : ProofLib.ByteSlice.slice res 960 160 = b6 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 960 160 = b6
    rw [slice_append_right b0 _ 160 800 160 l0 rfl, slice_append_right b1 _ 160 640 160 l1 rfl, slice_append_right b2 _ 160 480 160 l2 rfl, slice_append_right b3 _ 160 320 160 l3 rfl, slice_append_right b4 _ 160 160 160 l4 rfl, slice_append_right b5 _ 160 0 160 l5 rfl, slice_append_left b6 _ l6]
  have s7 : ProofLib.ByteSlice.slice res 1120 160 = b7 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 1120 160 = b7
    rw [slice_append_right b0 _ 160 960 160 l0 rfl, slice_append_right b1 _ 160 800 160 l1 rfl, slice_append_right b2 _ 160 640 160 l2 rfl, slice_append_right b3 _ 160 480 160 l3 rfl, slice_append_right b4 _ 160 320 160 l4 rfl, slice_append_right b5 _ 160 160 160 l5 rfl, slice_append_right b6 _ 160 0 160 l6 rfl]
    exact slice_zero_len b7 l7
  refine ⟨⟨l07, ?_⟩, ?_⟩ <;> (
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simp only [Nat.mul_zero]; rw [s0]; exact h0.1
  · simp only [Nat.reduceMul]; rw [s1]; exact h1.1
  · simp only [Nat.reduceMul]; rw [s2]; exact h2.1
  · simp only [Nat.reduceMul]; rw [s3]; exact h3.1
  · simp only [Nat.reduceMul]; rw [s4]; exact h4.1
  · simp only [Nat.reduceMul]; rw [s5]; exact h5.1
  · simp only [Nat.reduceMul]; rw [s6]; exact h6.1
  · simp only [Nat.reduceMul]; rw [s7]; exact h7.1
  · simp only [Nat.mul_zero]; rw [s0]; exact h0.2
  · simp only [Nat.reduceMul]; rw [s1]; exact h1.2
  · simp only [Nat.reduceMul]; rw [s2]; exact h2.2
  · simp only [Nat.reduceMul]; rw [s3]; exact h3.2
  · simp only [Nat.reduceMul]; rw [s4]; exact h4.2
  · simp only [Nat.reduceMul]; rw [s5]; exact h5.2
  · simp only [Nat.reduceMul]; rw [s6]; exact h6.2
  · simp only [Nat.reduceMul]; rw [s7]; exact h7.2

theorem split_chunk_160 (sp : BitVec 64) (off0 off1 rem : Nat) (bs : List (BitVec 8))
    (hbs : bs.length = 160 + rem) (ho : off0 = off1 + 160 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide) :
    ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ bs.take 160) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ bs.drop 160) := by
  conv => lhs; rw [← List.take_append_drop 160 bs]
  rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by omega),
      sub_ofNat64_add sp off0 160 (by omega), show off0 - 160 = off1 by omega]

theorem sepWP_split7_table (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 1712#64) ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = 1120 := by assumption)
    (hnext : ∀ b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8),
      b1.length = 160 → b2.length = 160 → b3.length = 160 → b4.length = 160 →
      b5.length = 160 → b6.length = 160 → b7.length = 160 →
      SepWP prog target_pc s
        ((((sp - 1712#64) ↦ₛ b1) ∗ ((sp - 1552#64) ↦ₛ b2) ∗ ((sp - 1392#64) ↦ₛ b3) ∗
          ((sp - 1232#64) ↦ₛ b4) ∗ ((sp - 1072#64) ↦ₛ b5) ∗ ((sp - 912#64) ↦ₛ b6) ∗
          ((sp - 752#64) ↦ₛ b7)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 160; have hd1 : d1.length = 160 + 800 := by simp [d1, hbs]
  let d2 := d1.drop 160; have hd2 : d2.length = 160 + 640 := by simp [d2, hd1]
  let d3 := d2.drop 160; have hd3 : d3.length = 160 + 480 := by simp [d3, hd2]
  let d4 := d3.drop 160; have hd4 : d4.length = 160 + 320 := by simp [d4, hd3]
  let d5 := d4.drop 160; have hd5 : d5.length = 160 + 160 := by simp [d5, hd4]
  rw [hf, split_chunk_160 sp 1712 1552 960 bs hbs, split_chunk_160 sp 1552 1392 800 d1 hd1,
      split_chunk_160 sp 1392 1232 640 d2 hd2, split_chunk_160 sp 1232 1072 480 d3 hd3,
      split_chunk_160 sp 1072 912 320 d4 hd4, split_chunk_160 sp 912 752 160 d5 hd5]
  exact hnext (bs.take 160) (d1.take 160) (d2.take 160) (d3.take 160)
    (d4.take 160) (d5.take 160) (d5.drop 160)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd3])
    (by simp [hd4]) (by simp [hd5]) (by simp [hd5])

theorem merge_chunk_160 (sp : BitVec 64) (off0 off1 : Nat) (b0 b1 : List (BitVec 8))
    (h0 : b0.length = 160) (ho : off0 = off1 + 160 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide) :
    ((sp - BitVec.ofNat 64 off0) ↦ₛ (b0 ++ b1)) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) := by
  rw [pointsToBytes_append, h0, sub_ofNat64_add sp off0 160 (by omega), show off0 - 160 = off1 by omega]

theorem sepWP_merge8_table (sp : BitVec 64) (A : EdExtPoint)
    {b0 b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((((sp - 1872#64) ↦ₛ b0) ∗ ((sp - 1712#64) ↦ₛ b1) ∗ ((sp - 1552#64) ↦ₛ b2) ∗
                   ((sp - 1392#64) ↦ₛ b3) ∗ ((sp - 1232#64) ↦ₛ b4) ∗ ((sp - 1072#64) ↦ₛ b5) ∗
                   ((sp - 912#64) ↦ₛ b6) ∗ ((sp - 752#64) ↦ₛ b7)) ∗ P) := by sep_frame)
    (h0 : fe51Point4Bounded b0 (2 ^ 54) ∧ edExtOfBytes b0 = projNielsTablePoints A 0)
    (h1 : fe51Point4Bounded b1 (2 ^ 54) ∧ edExtOfBytes b1 = projNielsTablePoints A 1)
    (h2 : fe51Point4Bounded b2 (2 ^ 54) ∧ edExtOfBytes b2 = projNielsTablePoints A 2)
    (h3 : fe51Point4Bounded b3 (2 ^ 54) ∧ edExtOfBytes b3 = projNielsTablePoints A 3)
    (h4 : fe51Point4Bounded b4 (2 ^ 54) ∧ edExtOfBytes b4 = projNielsTablePoints A 4)
    (h5 : fe51Point4Bounded b5 (2 ^ 54) ∧ edExtOfBytes b5 = projNielsTablePoints A 5)
    (h6 : fe51Point4Bounded b6 (2 ^ 54) ∧ edExtOfBytes b6 = projNielsTablePoints A 6)
    (h7 : fe51Point4Bounded b7 (2 ^ 54) ∧ edExtOfBytes b7 = projNielsTablePoints A 7)
    (hnext : ∀ table_bs : List (BitVec 8),
      table_bs.length = 1280 →
      (fe51ProjNielsTable8Bounded table_bs (2 ^ 54) ∧
       ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = projNielsTablePoints A i) →
      SepWP prog target_pc s (((sp - 1872#64) ↦ₛ table_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let res := b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))))
  have hprop := projTable8_of_append8 A b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
  have hm : ((sp - 1872#64) ↦ₛ res) =
      ((sp - 1872#64) ↦ₛ b0) ∗ ((sp - 1712#64) ↦ₛ b1) ∗ ((sp - 1552#64) ↦ₛ b2) ∗
      ((sp - 1392#64) ↦ₛ b3) ∗ ((sp - 1232#64) ↦ₛ b4) ∗ ((sp - 1072#64) ↦ₛ b5) ∗
      ((sp - 912#64) ↦ₛ b6) ∗ ((sp - 752#64) ↦ₛ b7) := by
    dsimp only [res]
    rw [merge_chunk_160 sp 1872 1712 b0 _ h0.1.1, merge_chunk_160 sp 1712 1552 b1 _ h1.1.1,
        merge_chunk_160 sp 1552 1392 b2 _ h2.1.1, merge_chunk_160 sp 1392 1232 b3 _ h3.1.1,
        merge_chunk_160 sp 1232 1072 b4 _ h4.1.1, merge_chunk_160 sp 1072 912 b5 _ h5.1.1,
        merge_chunk_160 sp 912 752 b6 b7 h6.1.1]
  rw [hf, ← hm]
  exact hnext res hprop.1.1 hprop

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
