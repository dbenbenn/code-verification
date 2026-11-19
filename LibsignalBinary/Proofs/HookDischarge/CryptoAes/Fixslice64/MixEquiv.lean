/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxEquiv

/-!
# Fixsliced `MixColumns` and `InvMixColumns` Equivalence (`Fixslice64.MixEquiv`)

Proves `bv_decide`-free equivalence for all four fixslice parities `q ∈ {0, 1, 2, 3}`:
- `addRoundKeyFs` linearity, `subBytesNots` commutation with `mixColumnsQ` and `invMixColumnsQ`
  (using `2 ⊕ 3 ⊕ 1 ⊕ 1 = 1` and `14 ⊕ 11 ⊕ 13 ⊕ 9 = 1` in $\mathrm{GF}(2^8)$, i.e.,
  `mixColumnsQ q notsMask = notsMask` and `invMixColumnsQ q notsMask = notsMask`);
- `mixColumnsQ_bitslice`:
  `mixColumnsQ q (bitslice (bs.map (invShiftRowsPow q))) =
     bitslice (bs.map (fun s => invShiftRowsPow q (mixColumns s)))`;
- `invMixColumnsQ_bitslice`:
  `invMixColumnsQ q (bitslice (bs.map (invShiftRowsPow q))) =
     bitslice (bs.map (fun s => invShiftRowsPow q (invMixColumns s)))`.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixEquiv

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
  (State Word xtime gfMul mixColumn mixColumns invMixColumn invMixColumns addRoundKey xorWord)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (FsState Blocks4 ror64 rorDistance rotateRows1 rotateRows2
   rotateRowsAndColumns11 rotateRowsAndColumns12 rotateRowsAndColumns13 rotateRowsAndColumns22
   bitslice notsMask subBytesNots addRoundKeyFs
   mixColumnsGen mixColumns0 mixColumns1 mixColumns2 mixColumns3 mixColumnsQ
   invMixColumnsGen invMixColumns0 invMixColumns1 invMixColumns2 invMixColumns3 invMixColumnsQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing
  (getLsbD_bitslice eq_bitslice_of_getLsbD shiftRowsPow invShiftRowsPow
   getD_shiftRowsPow shiftRowsPow_mod)

/-! ## `addRoundKeyFs`, `subBytesNots`, and Linearity / Fixed-Point Laws -/

theorem addRoundKeyFs_comm (a b : FsState) : addRoundKeyFs a b = addRoundKeyFs b a := by
  ext1 <;> simp [addRoundKeyFs, FsState.zipWith, BitVec.xor_comm]

theorem addRoundKeyFs_assoc (a b c : FsState) :
    addRoundKeyFs (addRoundKeyFs a b) c = addRoundKeyFs a (addRoundKeyFs b c) := by
  ext1 <;> simp [addRoundKeyFs, FsState.zipWith, BitVec.xor_assoc]

@[simp] theorem addRoundKeyFs_self (a : FsState) : addRoundKeyFs a a = FsState.zero := by
  ext1 <;> simp [addRoundKeyFs, FsState.zipWith, FsState.zero]

@[simp] theorem addRoundKeyFs_zero (a : FsState) : addRoundKeyFs a FsState.zero = a := by
  ext1 <;> simp [addRoundKeyFs, FsState.zipWith, FsState.zero]

@[simp] theorem zero_addRoundKeyFs (a : FsState) : addRoundKeyFs FsState.zero a = a := by
  ext1 <;> simp [addRoundKeyFs, FsState.zipWith, FsState.zero]

theorem subBytesNots_eq_addRoundKeyFs (st : FsState) :
    subBytesNots st = addRoundKeyFs st notsMask := rfl

@[simp] theorem subBytesNots_subBytesNots (st : FsState) :
    subBytesNots (subBytesNots st) = st := by
  rw [subBytesNots_eq_addRoundKeyFs, subBytesNots_eq_addRoundKeyFs,
    addRoundKeyFs_assoc, addRoundKeyFs_self, addRoundKeyFs_zero]

theorem addRoundKeyFs_bitslice (x y : Blocks4) :
    addRoundKeyFs (bitslice x) (bitslice y) = bitslice (x.zipWith addRoundKey y) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  have hslice : ((addRoundKeyFs (bitslice x) (bitslice y)).getSlice p) =
      (bitslice x).getSlice p ^^^ (bitslice y).getSlice p := by
    match p, hp with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | _ + 8, hp => omega
  have hlane : (x.zipWith addRoundKey y).getLane lane =
      addRoundKey (x.getLane lane) (y.getLane lane) := by
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
    | _ + 4, hl => omega
  have hark : ∀ (a b : State) (j : Nat), j < 16 →
      (addRoundKey a b).getD j 0#8 = a.getD j 0#8 ^^^ b.getD j 0#8 := by
    intro a b j hj
    have hlen : j < (addRoundKey a b).length := by simp [addRoundKey]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp only [addRoundKey, List.getElem_ofFn, Option.getD_some]
  rw [hslice, BitVec.getLsbD_xor, getLsbD_bitslice x p r c lane hp hr hc hl,
    getLsbD_bitslice y p r c lane hp hr hc hl, hlane, hark _ _ (r + 4 * c) (by omega),
    BitVec.getLsbD_xor]

private theorem ror64_xor (x y : BitVec 64) (d : Nat) :
    ror64 (x ^^^ y) d = ror64 x d ^^^ ror64 y d := by
  ext k hk
  simp only [ror64, BitVec.getElem_xor, BitVec.getElem_rotateRight]
  split <;> rfl

private theorem mask_or_xor (a1 a2 b1 b2 m1 m2 : BitVec 64)
    (hdisj : m1 &&& m2 = 0#64) :
    ((a1 &&& m1) ||| (b1 &&& m2)) ^^^ ((a2 &&& m1) ||| (b2 &&& m2)) =
      (((a1 ^^^ a2) &&& m1) ||| ((b1 ^^^ b2) &&& m2)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hd : (m1.getLsbD k && m2.getLsbD k) = false := by
    have h := congrArg (fun v => v.getLsbD k) hdisj
    simpa [BitVec.getLsbD_and] using h
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases hm1 : m1.getLsbD k <;> cases hm2 : m2.getLsbD k
  · simp
  · simp
  · simp
  · simp [hm1, hm2] at hd

private theorem rot_linear_all :
    (∀ x y, rotateRows1 (x ^^^ y) = rotateRows1 x ^^^ rotateRows1 y) ∧
    (∀ x y, rotateRows2 (x ^^^ y) = rotateRows2 x ^^^ rotateRows2 y) ∧
    (∀ x y, rotateRowsAndColumns11 (x ^^^ y) =
      rotateRowsAndColumns11 x ^^^ rotateRowsAndColumns11 y) ∧
    (∀ x y, rotateRowsAndColumns12 (x ^^^ y) =
      rotateRowsAndColumns12 x ^^^ rotateRowsAndColumns12 y) ∧
    (∀ x y, rotateRowsAndColumns13 (x ^^^ y) =
      rotateRowsAndColumns13 x ^^^ rotateRowsAndColumns13 y) ∧
    (∀ x y, rotateRowsAndColumns22 (x ^^^ y) =
      rotateRowsAndColumns22 x ^^^ rotateRowsAndColumns22 y) := by
  refine ⟨fun x y => ror64_xor x y _, fun x y => ror64_xor x y _,
    fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · dsimp only [rotateRowsAndColumns11]
    rw [ror64_xor, ror64_xor]
    exact (mask_or_xor _ _ _ _ 0x0fff0fff0fff0fff#64 0xf000f000f000f000#64 (by decide)).symm
  · dsimp only [rotateRowsAndColumns12]
    rw [ror64_xor, ror64_xor]
    exact (mask_or_xor _ _ _ _ 0x00ff00ff00ff00ff#64 0xff00ff00ff00ff00#64 (by decide)).symm
  · dsimp only [rotateRowsAndColumns13]
    rw [ror64_xor, ror64_xor]
    exact (mask_or_xor _ _ _ _ 0x000f000f000f000f#64 0xfff0fff0fff0fff0#64 (by decide)).symm
  · dsimp only [rotateRowsAndColumns22]
    rw [ror64_xor, ror64_xor]
    exact (mask_or_xor _ _ _ _ 0x00ff00ff00ff00ff#64 0xff00ff00ff00ff00#64 (by decide)).symm

private theorem xor64_pair (u1 u2 v1 v2 : BitVec 64) :
    (u1 ^^^ u2) ^^^ (v1 ^^^ v2) = (u1 ^^^ v1) ^^^ (u2 ^^^ v2) := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc u2 v1 v2, BitVec.xor_comm u2 v1,
    BitVec.xor_assoc v1 u2 v2, ← BitVec.xor_assoc]

private theorem xor64_triple (u1 u2 v1 v2 w1 w2 : BitVec 64) :
    (u1 ^^^ u2) ^^^ (v1 ^^^ v2) ^^^ (w1 ^^^ w2) = (u1 ^^^ v1 ^^^ w1) ^^^ (u2 ^^^ v2 ^^^ w2) := by
  rw [xor64_pair u1 u2 v1 v2, xor64_pair (u1 ^^^ v1) (u2 ^^^ v2) w1 w2]

private theorem xor64_quad (u1 u2 v1 v2 w1 w2 z1 z2 : BitVec 64) :
    (u1 ^^^ u2) ^^^ (v1 ^^^ v2) ^^^ (w1 ^^^ w2) ^^^ (z1 ^^^ z2) =
      (u1 ^^^ v1 ^^^ w1 ^^^ z1) ^^^ (u2 ^^^ v2 ^^^ w2 ^^^ z2) := by
  rw [xor64_triple u1 u2 v1 v2 w1 w2, xor64_pair _ _ z1 z2]

private theorem mixColumnsGen_xor (rot1 rot2 : BitVec 64 → BitVec 64)
    (hr1 : ∀ x y, rot1 (x ^^^ y) = rot1 x ^^^ rot1 y)
    (hr2 : ∀ x y, rot2 (x ^^^ y) = rot2 x ^^^ rot2 y) (a b : FsState) :
    mixColumnsGen rot1 rot2 (addRoundKeyFs a b) =
      addRoundKeyFs (mixColumnsGen rot1 rot2 a) (mixColumnsGen rot1 rot2 b) := by
  have hc : ∀ x y : BitVec 64, (x ^^^ y) ^^^ rot1 (x ^^^ y) = (x ^^^ rot1 x) ^^^ (y ^^^ rot1 y) := by
    intro x y; rw [hr1, xor64_pair]
  dsimp only [mixColumnsGen, addRoundKeyFs, FsState.zipWith]
  rw [hc a.s0 b.s0, hc a.s1 b.s1, hc a.s2 b.s2, hc a.s3 b.s3,
      hc a.s4 b.s4, hc a.s5 b.s5, hc a.s6 b.s6, hc a.s7 b.s7]
  ext1 <;> dsimp only
  · rw [hr1, hr2, xor64_triple]
  · rw [hr1, hr2, xor64_quad]
  · rw [hr1, hr2, xor64_triple]
  · rw [hr1, hr2, xor64_quad]
  · rw [hr1, hr2, xor64_quad]
  · rw [hr1, hr2, xor64_triple]
  · rw [hr1, hr2, xor64_triple]
  · rw [hr1, hr2, xor64_triple]

private theorem invMixColumnsGen_xor (rot1 rot2 : BitVec 64 → BitVec 64)
    (hr1 : ∀ x y, rot1 (x ^^^ y) = rot1 x ^^^ rot1 y)
    (hr2 : ∀ x y, rot2 (x ^^^ y) = rot2 x ^^^ rot2 y) (a b : FsState) :
    invMixColumnsGen rot1 rot2 (addRoundKeyFs a b) =
      addRoundKeyFs (invMixColumnsGen rot1 rot2 a) (invMixColumnsGen rot1 rot2 b) := by
  have hc : ∀ x y : BitVec 64, (x ^^^ y) ^^^ rot1 (x ^^^ y) = (x ^^^ rot1 x) ^^^ (y ^^^ rot1 y) := by
    intro x y; rw [hr1, xor64_pair]
  dsimp only [invMixColumnsGen, addRoundKeyFs, FsState.zipWith]
  rw [hc a.s0 b.s0, hc a.s1 b.s1, hc a.s2 b.s2, hc a.s3 b.s3,
      hc a.s4 b.s4, hc a.s5 b.s5, hc a.s6 b.s6, hc a.s7 b.s7]
  have hd0 := xor64_pair a.s0 b.s0 (a.s7 ^^^ rot1 a.s7) (b.s7 ^^^ rot1 b.s7)
  have hd1 := xor64_triple a.s1 b.s1 (a.s0 ^^^ rot1 a.s0) (b.s0 ^^^ rot1 b.s0)
    (a.s7 ^^^ rot1 a.s7) (b.s7 ^^^ rot1 b.s7)
  have hd2 := xor64_pair a.s2 b.s2 (a.s1 ^^^ rot1 a.s1) (b.s1 ^^^ rot1 b.s1)
  have hd3 := xor64_triple a.s3 b.s3 (a.s2 ^^^ rot1 a.s2) (b.s2 ^^^ rot1 b.s2)
    (a.s7 ^^^ rot1 a.s7) (b.s7 ^^^ rot1 b.s7)
  have hd4 := xor64_triple a.s4 b.s4 (a.s3 ^^^ rot1 a.s3) (b.s3 ^^^ rot1 b.s3)
    (a.s7 ^^^ rot1 a.s7) (b.s7 ^^^ rot1 b.s7)
  have hd5 := xor64_pair a.s5 b.s5 (a.s4 ^^^ rot1 a.s4) (b.s4 ^^^ rot1 b.s4)
  have hd6 := xor64_pair a.s6 b.s6 (a.s5 ^^^ rot1 a.s5) (b.s5 ^^^ rot1 b.s5)
  have hd7 := xor64_pair a.s7 b.s7 (a.s6 ^^^ rot1 a.s6) (b.s6 ^^^ rot1 b.s6)
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7]
  let d0a := a.s0 ^^^ (a.s7 ^^^ rot1 a.s7); let d0b := b.s0 ^^^ (b.s7 ^^^ rot1 b.s7)
  let d1a := a.s1 ^^^ (a.s0 ^^^ rot1 a.s0) ^^^ (a.s7 ^^^ rot1 a.s7)
  let d1b := b.s1 ^^^ (b.s0 ^^^ rot1 b.s0) ^^^ (b.s7 ^^^ rot1 b.s7)
  let d2a := a.s2 ^^^ (a.s1 ^^^ rot1 a.s1); let d2b := b.s2 ^^^ (b.s1 ^^^ rot1 b.s1)
  let d3a := a.s3 ^^^ (a.s2 ^^^ rot1 a.s2) ^^^ (a.s7 ^^^ rot1 a.s7)
  let d3b := b.s3 ^^^ (b.s2 ^^^ rot1 b.s2) ^^^ (b.s7 ^^^ rot1 b.s7)
  let d4a := a.s4 ^^^ (a.s3 ^^^ rot1 a.s3) ^^^ (a.s7 ^^^ rot1 a.s7)
  let d4b := b.s4 ^^^ (b.s3 ^^^ rot1 b.s3) ^^^ (b.s7 ^^^ rot1 b.s7)
  let d5a := a.s5 ^^^ (a.s4 ^^^ rot1 a.s4); let d5b := b.s5 ^^^ (b.s4 ^^^ rot1 b.s4)
  let d6a := a.s6 ^^^ (a.s5 ^^^ rot1 a.s5); let d6b := b.s6 ^^^ (b.s5 ^^^ rot1 b.s5)
  let d7a := a.s7 ^^^ (a.s6 ^^^ rot1 a.s6); let d7b := b.s7 ^^^ (b.s6 ^^^ rot1 b.s6)
  have he0 := xor64_pair (a.s0 ^^^ rot1 a.s0) (b.s0 ^^^ rot1 b.s0) d6a d6b
  have he1 := xor64_triple (a.s1 ^^^ rot1 a.s1) (b.s1 ^^^ rot1 b.s1) d6a d6b d7a d7b
  have he2 := xor64_triple (a.s2 ^^^ rot1 a.s2) (b.s2 ^^^ rot1 b.s2) d0a d0b d7a d7b
  have he3 := xor64_triple (a.s3 ^^^ rot1 a.s3) (b.s3 ^^^ rot1 b.s3) d1a d1b d6a d6b
  have he4 := xor64_quad (a.s4 ^^^ rot1 a.s4) (b.s4 ^^^ rot1 b.s4) d2a d2b d6a d6b d7a d7b
  have he5 := xor64_triple (a.s5 ^^^ rot1 a.s5) (b.s5 ^^^ rot1 b.s5) d3a d3b d7a d7b
  have he6 := xor64_pair (a.s6 ^^^ rot1 a.s6) (b.s6 ^^^ rot1 b.s6) d4a d4b
  have he7 := xor64_pair (a.s7 ^^^ rot1 a.s7) (b.s7 ^^^ rot1 b.s7) d5a d5b
  rw [he0, he1, he2, he3, he4, he5, he6, he7]
  ext1 <;> dsimp only <;> rw [hr2, xor64_triple]

theorem mixColumnsQ_addRoundKeyFs (q : Nat) (a b : FsState) :
    mixColumnsQ q (addRoundKeyFs a b) = addRoundKeyFs (mixColumnsQ q a) (mixColumnsQ q b) := by
  obtain ⟨h1, h2, h11, h12, h13, h22⟩ := rot_linear_all
  match q with
  | 0 => exact mixColumnsGen_xor _ _ h1 h2 a b
  | 1 => exact mixColumnsGen_xor _ _ h11 h22 a b
  | 2 => exact mixColumnsGen_xor _ _ h12 h2 a b
  | _ + 3 => exact mixColumnsGen_xor _ _ h13 h22 a b

theorem invMixColumnsQ_addRoundKeyFs (q : Nat) (a b : FsState) :
    invMixColumnsQ q (addRoundKeyFs a b) =
      addRoundKeyFs (invMixColumnsQ q a) (invMixColumnsQ q b) := by
  obtain ⟨h1, h2, h11, h12, h13, h22⟩ := rot_linear_all
  match q with
  | 0 => exact invMixColumnsGen_xor _ _ h1 h2 a b
  | 1 => exact invMixColumnsGen_xor _ _ h11 h22 a b
  | 2 => exact invMixColumnsGen_xor _ _ h12 h2 a b
  | _ + 3 => exact invMixColumnsGen_xor _ _ h13 h22 a b

theorem mixColumnsQ_notsMask (q : Nat) : mixColumnsQ q notsMask = notsMask := by
  match q with
  | 0 => change mixColumns0 notsMask = notsMask; ext1 <;> decide
  | 1 => change mixColumns1 notsMask = notsMask; ext1 <;> decide
  | 2 => change mixColumns2 notsMask = notsMask; ext1 <;> decide
  | _ + 3 => change mixColumns3 notsMask = notsMask; ext1 <;> decide

theorem invMixColumnsQ_notsMask (q : Nat) : invMixColumnsQ q notsMask = notsMask := by
  match q with
  | 0 => change invMixColumns0 notsMask = notsMask; ext1 <;> decide
  | 1 => change invMixColumns1 notsMask = notsMask; ext1 <;> decide
  | 2 => change invMixColumns2 notsMask = notsMask; ext1 <;> decide
  | _ + 3 => change invMixColumns3 notsMask = notsMask; ext1 <;> decide

theorem mixColumnsQ_subBytesNots (q : Nat) (st : FsState) :
    mixColumnsQ q (subBytesNots st) = subBytesNots (mixColumnsQ q st) := by
  rw [subBytesNots_eq_addRoundKeyFs, mixColumnsQ_addRoundKeyFs, mixColumnsQ_notsMask,
    ← subBytesNots_eq_addRoundKeyFs]

theorem invMixColumnsQ_subBytesNots (q : Nat) (st : FsState) :
    invMixColumnsQ q (subBytesNots st) = subBytesNots (invMixColumnsQ q st) := by
  rw [subBytesNots_eq_addRoundKeyFs, invMixColumnsQ_addRoundKeyFs, invMixColumnsQ_notsMask,
    ← subBytesNots_eq_addRoundKeyFs]

/-! ## Rotation Bit-Index Routing Under `invShiftRowsPow q` -/

private def rot1Fn : Fin 4 → BitVec 64 → BitVec 64
  | ⟨0, _⟩ => rotateRows1
  | ⟨1, _⟩ => rotateRowsAndColumns11
  | ⟨2, _⟩ => rotateRowsAndColumns12
  | ⟨3, _⟩ => rotateRowsAndColumns13
  | ⟨_ + 4, h⟩ => absurd h (by omega)

private def rot2Fn : Fin 4 → BitVec 64 → BitVec 64
  | ⟨0, _⟩ => rotateRows2
  | ⟨1, _⟩ => rotateRowsAndColumns22
  | ⟨2, _⟩ => rotateRows2
  | ⟨3, _⟩ => rotateRowsAndColumns22
  | ⟨_ + 4, h⟩ => absurd h (by omega)

private def rot1Route (q : Fin 4) (k : Fin 64) : Fin 64 :=
  match q with
  | ⟨0, _⟩ => ⟨(k.val + 16) % 64, by omega⟩
  | ⟨1, _⟩ =>
    if (0x0fff0fff0fff0fff#64).getLsbD k.val then ⟨(k.val + 20) % 64, by omega⟩
    else ⟨(k.val + 4) % 64, by omega⟩
  | ⟨2, _⟩ =>
    if (0x00ff00ff00ff00ff#64).getLsbD k.val then ⟨(k.val + 24) % 64, by omega⟩
    else ⟨(k.val + 8) % 64, by omega⟩
  | ⟨3, _⟩ =>
    if (0x000f000f000f000f#64).getLsbD k.val then ⟨(k.val + 28) % 64, by omega⟩
    else ⟨(k.val + 12) % 64, by omega⟩
  | ⟨_ + 4, h⟩ => absurd h (by omega)

private def rot2Route (q : Fin 4) (k : Fin 64) : Fin 64 :=
  match q with
  | ⟨0, _⟩ | ⟨2, _⟩ => ⟨(k.val + 32) % 64, by omega⟩
  | ⟨1, _⟩ | ⟨3, _⟩ =>
    if (0x00ff00ff00ff00ff#64).getLsbD k.val then ⟨(k.val + 40) % 64, by omega⟩
    else ⟨(k.val + 24) % 64, by omega⟩
  | ⟨_ + 4, h⟩ => absurd h (by omega)

private theorem getLsbD_ror64 (x : BitVec 64) (d : Nat) (hd : d < 64) (k : Fin 64) :
    (ror64 x d).getLsbD k.val = x.getLsbD ((k.val + d) % 64) := by
  simp only [ror64, BitVec.getLsbD_rotateRight, k.isLt, decide_true, Bool.true_and,
    Nat.mod_eq_of_lt hd]
  split
  · have h : d + k.val = (k.val + d) % 64 := by omega
    rw [h]
  · have h : k.val - (64 - d) = (k.val + d) % 64 := by omega
    rw [h]

private theorem getLsbD_mask_ror_pair (x m1 m2 : BitVec 64) (d1 d2 : Nat)
    (hd1 : d1 < 64) (hd2 : d2 < 64) (k : Fin 64)
    (hcompl : ∀ i : Fin 64, m2.getLsbD i.val = !m1.getLsbD i.val) :
    ((ror64 x d1 &&& m1) ||| (ror64 x d2 &&& m2)).getLsbD k.val =
      x.getLsbD (if m1.getLsbD k.val then (k.val + d1) % 64 else (k.val + d2) % 64) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, getLsbD_ror64 x d1 hd1 k,
    getLsbD_ror64 x d2 hd2 k, hcompl k]
  cases m1.getLsbD k.val <;> simp

private theorem getLsbD_rot1Fn (q : Fin 4) (x : BitVec 64) (k : Fin 64) :
    (rot1Fn q x).getLsbD k.val = x.getLsbD (rot1Route q k).val := by
  rcases q with ⟨qv, hq⟩
  match qv, hq with
  | 0, hq =>
    dsimp only [rot1Fn, rot1Route, rotateRows1, rorDistance]
    exact getLsbD_ror64 x 16 (by omega) k
  | 1, hq =>
    rw [show rot1Fn ⟨1, hq⟩ x = rotateRowsAndColumns11 x from rfl, rotateRowsAndColumns11,
      getLsbD_mask_ror_pair _ _ _ _ _ (by decide) (by decide) k (by decide)]
    dsimp [rot1Route, rorDistance]
    cases (0x0fff0fff0fff0fff#64).getLsbD k.val <;> rfl
  | 2, hq =>
    rw [show rot1Fn ⟨2, hq⟩ x = rotateRowsAndColumns12 x from rfl, rotateRowsAndColumns12,
      getLsbD_mask_ror_pair _ _ _ _ _ (by decide) (by decide) k (by decide)]
    dsimp [rot1Route, rorDistance]
    cases (0x00ff00ff00ff00ff#64).getLsbD k.val <;> rfl
  | 3, hq =>
    rw [show rot1Fn ⟨3, hq⟩ x = rotateRowsAndColumns13 x from rfl, rotateRowsAndColumns13,
      getLsbD_mask_ror_pair _ _ _ _ _ (by decide) (by decide) k (by decide)]
    dsimp [rot1Route, rorDistance]
    cases (0x000f000f000f000f#64).getLsbD k.val <;> rfl
  | _ + 4, hq => omega

private theorem getLsbD_rot2Fn (q : Fin 4) (x : BitVec 64) (k : Fin 64) :
    (rot2Fn q x).getLsbD k.val = x.getLsbD (rot2Route q k).val := by
  rcases q with ⟨qv, hq⟩
  match qv, hq with
  | 0, hq =>
    dsimp only [rot2Fn, rot2Route, rotateRows2, rorDistance]
    exact getLsbD_ror64 x 32 (by omega) k
  | 1, hq =>
    rw [show rot2Fn ⟨1, hq⟩ x = rotateRowsAndColumns22 x from rfl, rotateRowsAndColumns22,
      getLsbD_mask_ror_pair _ _ _ _ _ (by decide) (by decide) k (by decide)]
    dsimp [rot2Route, rorDistance]
    cases (0x00ff00ff00ff00ff#64).getLsbD k.val <;> rfl
  | 2, hq =>
    dsimp only [rot2Fn, rot2Route, rotateRows2, rorDistance]
    exact getLsbD_ror64 x 32 (by omega) k
  | 3, hq =>
    rw [show rot2Fn ⟨3, hq⟩ x = rotateRowsAndColumns22 x from rfl, rotateRowsAndColumns22,
      getLsbD_mask_ror_pair _ _ _ _ _ (by decide) (by decide) k (by decide)]
    dsimp [rot2Route, rorDistance]
    cases (0x00ff00ff00ff00ff#64).getLsbD k.val <;> rfl
  | _ + 4, hq => omega

private theorem rot1Route_invShiftIdx :
    ∀ (q r c lane : Fin 4),
      let col := (c.val + (4 - q.val) * r.val) % 4
      let r1 := (r.val + 1) % 4
      let c1 := (col + q.val * r1) % 4
      (rot1Route q ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩).val =
        16 * r1 + 4 * c1 + lane.val := by decide

private theorem rot2Route_invShiftIdx :
    ∀ (q r c lane : Fin 4),
      let col := (c.val + (4 - q.val) * r.val) % 4
      let r2 := (r.val + 2) % 4
      let c2 := (col + q.val * r2) % 4
      (rot2Route q ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩).val =
        16 * r2 + 4 * c2 + lane.val := by decide

/-! ## Scalar 1-Column Equivalence via 32-Bit $\mathbb{F}_2$ Basis (`by decide`) -/

private def packByteBits (f : Nat → Bool) : BitVec 8 :=
  (if f 0 then 0x01#8 else 0#8) ^^^ (if f 1 then 0x02#8 else 0#8) ^^^
  (if f 2 then 0x04#8 else 0#8) ^^^ (if f 3 then 0x08#8 else 0#8) ^^^
  (if f 4 then 0x10#8 else 0#8) ^^^ (if f 5 then 0x20#8 else 0#8) ^^^
  (if f 6 then 0x40#8 else 0#8) ^^^ (if f 7 then 0x80#8 else 0#8)

private theorem getLsbD_packByteBits (f : Nat → Bool) (p : Nat) (hp : p < 8) :
    (packByteBits f).getLsbD p = f p := by
  unfold packByteBits
  simp only [BitVec.getLsbD_xor]
  have hite : ∀ (c : Bool) (v : BitVec 8), (if c then v else 0#8).getLsbD p = (c && v.getLsbD p) := by
    intro c v; cases c <;> simp
  simp only [hite]
  match p, hp with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp
  | _ + 8, hp => omega

private theorem flatten_cols4 (g : Fin 4 → BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)
    (r col : Fin 4) :
    ((List.ofFn fun c : Fin 4 =>
      [(g c).1, (g c).2.1, (g c).2.2.1, (g c).2.2.2]).flatten).getD (r.val + 4 * col.val) 0#8 =
      [(g col).1, (g col).2.1, (g col).2.2.1, (g col).2.2.2].getD r.val 0#8 := by
  rcases col with ⟨col, hcol⟩
  rcases r with ⟨r, hr⟩
  match col, hcol, r, hr with
  | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _
  | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ => rfl
  | _ + 4, hcol, _, _ => omega
  | _, _, _ + 4, hr => omega

private theorem open_mixColumns (s : State) (r col : Fin 4) :
    (mixColumns s).getD (r.val + 4 * col.val) 0#8 =
      (mixColumn (s.getD (0 + 4 * col.val) 0#8) (s.getD (1 + 4 * col.val) 0#8)
        (s.getD (2 + 4 * col.val) 0#8) (s.getD (3 + 4 * col.val) 0#8)).getD r.val 0#8 := by
  have h := flatten_cols4 (fun c : Fin 4 =>
    (gfMul 0x02#8 (s.getD (4 * c.val) 0#8) ^^^ gfMul 0x03#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       s.getD (4 * c.val + 2) 0#8 ^^^ s.getD (4 * c.val + 3) 0#8,
     s.getD (4 * c.val) 0#8 ^^^ gfMul 0x02#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       gfMul 0x03#8 (s.getD (4 * c.val + 2) 0#8) ^^^ s.getD (4 * c.val + 3) 0#8,
     s.getD (4 * c.val) 0#8 ^^^ s.getD (4 * c.val + 1) 0#8 ^^^
       gfMul 0x02#8 (s.getD (4 * c.val + 2) 0#8) ^^^ gfMul 0x03#8 (s.getD (4 * c.val + 3) 0#8),
     gfMul 0x03#8 (s.getD (4 * c.val) 0#8) ^^^ s.getD (4 * c.val + 1) 0#8 ^^^
       s.getD (4 * c.val + 2) 0#8 ^^^ gfMul 0x02#8 (s.getD (4 * c.val + 3) 0#8))) r col
  rw [Nat.zero_add, Nat.add_comm 1 (4 * col.val), Nat.add_comm 2 (4 * col.val),
    Nat.add_comm 3 (4 * col.val)]
  exact h

private theorem open_invMixColumns (s : State) (r col : Fin 4) :
    (invMixColumns s).getD (r.val + 4 * col.val) 0#8 =
      (invMixColumn (s.getD (0 + 4 * col.val) 0#8) (s.getD (1 + 4 * col.val) 0#8)
        (s.getD (2 + 4 * col.val) 0#8) (s.getD (3 + 4 * col.val) 0#8)).getD r.val 0#8 := by
  have h := flatten_cols4 (fun c : Fin 4 =>
    (gfMul 0x0e#8 (s.getD (4 * c.val) 0#8) ^^^ gfMul 0x0b#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       gfMul 0x0d#8 (s.getD (4 * c.val + 2) 0#8) ^^^ gfMul 0x09#8 (s.getD (4 * c.val + 3) 0#8),
     gfMul 0x09#8 (s.getD (4 * c.val) 0#8) ^^^ gfMul 0x0e#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       gfMul 0x0b#8 (s.getD (4 * c.val + 2) 0#8) ^^^ gfMul 0x0d#8 (s.getD (4 * c.val + 3) 0#8),
     gfMul 0x0d#8 (s.getD (4 * c.val) 0#8) ^^^ gfMul 0x09#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       gfMul 0x0e#8 (s.getD (4 * c.val + 2) 0#8) ^^^ gfMul 0x0b#8 (s.getD (4 * c.val + 3) 0#8),
     gfMul 0x0b#8 (s.getD (4 * c.val) 0#8) ^^^ gfMul 0x0d#8 (s.getD (4 * c.val + 1) 0#8) ^^^
       gfMul 0x09#8 (s.getD (4 * c.val + 2) 0#8) ^^^ gfMul 0x0e#8 (s.getD (4 * c.val + 3) 0#8))) r col
  rw [Nat.zero_add, Nat.add_comm 1 (4 * col.val), Nat.add_comm 2 (4 * col.val),
    Nat.add_comm 3 (4 * col.val)]
  exact h

private def xtimeBits (c : BitVec 8) : BitVec 8 :=
  packByteBits fun p =>
    match p with
    | 0 => c.getLsbD 7
    | 1 => c.getLsbD 0 ^^ c.getLsbD 7
    | 2 => c.getLsbD 1
    | 3 => c.getLsbD 2 ^^ c.getLsbD 7
    | 4 => c.getLsbD 3 ^^ c.getLsbD 7
    | 5 => c.getLsbD 4
    | 6 => c.getLsbD 5
    | _ => c.getLsbD 6

private def mul4Bits (d : BitVec 8) : BitVec 8 :=
  packByteBits fun p =>
    match p with
    | 0 => d.getLsbD 6
    | 1 => d.getLsbD 6 ^^ d.getLsbD 7
    | 2 => d.getLsbD 0 ^^ d.getLsbD 7
    | 3 => d.getLsbD 1 ^^ d.getLsbD 6
    | 4 => d.getLsbD 2 ^^ d.getLsbD 6 ^^ d.getLsbD 7
    | 5 => d.getLsbD 3 ^^ d.getLsbD 7
    | 6 => d.getLsbD 4
    | _ => d.getLsbD 5

private theorem xtimeBits_xor (u v : BitVec 8) :
    xtimeBits (u ^^^ v) = xtimeBits u ^^^ xtimeBits v := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_xor, xtimeBits, xtimeBits, xtimeBits,
    getLsbD_packByteBits _ p hp, getLsbD_packByteBits _ p hp, getLsbD_packByteBits _ p hp]
  match p, hp with
  | 0, _ => simp
  | 1, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 0 <;> cases v.getLsbD 0 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 2, _ => simp
  | 3, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 2 <;> cases v.getLsbD 2 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 4, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 3 <;> cases v.getLsbD 3 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 5, _ => simp
  | 6, _ => simp
  | 7, _ => simp
  | _ + 8, hp => omega

private theorem mul4Bits_xor (u v : BitVec 8) :
    mul4Bits (u ^^^ v) = mul4Bits u ^^^ mul4Bits v := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_xor, mul4Bits, mul4Bits, mul4Bits,
    getLsbD_packByteBits _ p hp, getLsbD_packByteBits _ p hp, getLsbD_packByteBits _ p hp]
  match p, hp with
  | 0, _ => simp
  | 1, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 6 <;> cases v.getLsbD 6 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 2, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 0 <;> cases v.getLsbD 0 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 3, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 1 <;> cases v.getLsbD 1 <;> cases u.getLsbD 6 <;> cases v.getLsbD 6 <;> rfl
  | 4, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 2 <;> cases v.getLsbD 2 <;> cases u.getLsbD 6 <;> cases v.getLsbD 6 <;>
      cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 5, _ =>
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD 3 <;> cases v.getLsbD 3 <;> cases u.getLsbD 7 <;> cases v.getLsbD 7 <;> rfl
  | 6, _ => simp
  | 7, _ => simp
  | _ + 8, hp => omega

private theorem coeff_02 : ∀ x : BitVec 8, xtimeBits x = gfMul 0x02#8 x := by decide
private theorem coeff_03 : ∀ x : BitVec 8, x ^^^ xtimeBits x = gfMul 0x03#8 x := by decide
private theorem coeff_0e :
    ∀ x : BitVec 8,
      (x ^^^ xtimeBits x) ^^^ (x ^^^ mul4Bits (x ^^^ xtimeBits x)) = gfMul 0x0e#8 x := by decide
private theorem coeff_0b :
    ∀ x : BitVec 8, xtimeBits x ^^^ (x ^^^ mul4Bits (xtimeBits x)) = gfMul 0x0b#8 x := by decide
private theorem coeff_0d :
    ∀ x : BitVec 8, x ^^^ mul4Bits (x ^^^ xtimeBits x) = gfMul 0x0d#8 x := by decide
private theorem coeff_09 :
    ∀ x : BitVec 8, x ^^^ mul4Bits (xtimeBits x) = gfMul 0x09#8 x := by decide

private def mixFsByte (a0 a1 a2 a3 : BitVec 8) : BitVec 8 :=
  a1 ^^^ xtimeBits (a0 ^^^ a1) ^^^ (a2 ^^^ a3)

private theorem mixFsByte_eq (a0 a1 a2 a3 : BitVec 8) :
    mixFsByte a0 a1 a2 a3 = gfMul 0x02#8 a0 ^^^ gfMul 0x03#8 a1 ^^^ a2 ^^^ a3 := by
  dsimp only [mixFsByte]
  rw [xtimeBits_xor, ← coeff_02 a0, ← coeff_03 a1]
  apply BitVec.eq_of_getLsbD_eq; intro bit _; simp only [BitVec.getLsbD_xor]
  cases a1.getLsbD bit <;> cases (xtimeBits a0).getLsbD bit <;>
    cases (xtimeBits a1).getLsbD bit <;> cases a2.getLsbD bit <;> cases a3.getLsbD bit <;> rfl

private def dPair (a0 a1 : BitVec 8) : BitVec 8 := a0 ^^^ xtimeBits (a0 ^^^ a1)
private def ePair (a0 a1 : BitVec 8) : BitVec 8 := (a0 ^^^ a1) ^^^ mul4Bits (dPair a0 a1)

private def invMixFsByte (a0 a1 a2 a3 : BitVec 8) : BitVec 8 :=
  dPair a0 a1 ^^^ ePair a0 a1 ^^^ ePair a2 a3

private theorem xor8_pair (u1 u2 v1 v2 : BitVec 8) :
    (u1 ^^^ u2) ^^^ (v1 ^^^ v2) = (u1 ^^^ v1) ^^^ (u2 ^^^ v2) := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc u2 v1 v2, BitVec.xor_comm u2 v1,
    BitVec.xor_assoc v1 u2 v2, ← BitVec.xor_assoc]

private theorem invMixFsByte_eq (a0 a1 a2 a3 : BitVec 8) :
    invMixFsByte a0 a1 a2 a3 =
      gfMul 0x0e#8 a0 ^^^ gfMul 0x0b#8 a1 ^^^ gfMul 0x0d#8 a2 ^^^ gfMul 0x09#8 a3 := by
  have hd : ∀ x y : BitVec 8, dPair x y = (x ^^^ xtimeBits x) ^^^ xtimeBits y := by
    intro x y; dsimp only [dPair]; rw [xtimeBits_xor, ← BitVec.xor_assoc]
  have he : ∀ x y : BitVec 8,
      ePair x y = (x ^^^ mul4Bits (x ^^^ xtimeBits x)) ^^^ (y ^^^ mul4Bits (xtimeBits y)) := by
    intro x y; dsimp only [ePair]; rw [hd x y, mul4Bits_xor, xor8_pair]
  dsimp only [invMixFsByte]
  rw [hd a0 a1, he a0 a1, xor8_pair, coeff_0e a0, coeff_0b a1,
    he a2 a3, coeff_0d a2, coeff_09 a3, ← BitVec.xor_assoc]

private theorem xor4_rot (x0 x1 x2 x3 : BitVec 8) :
    (x1 ^^^ x2 ^^^ x3 ^^^ x0 = x0 ^^^ x1 ^^^ x2 ^^^ x3) ∧
    (x2 ^^^ x3 ^^^ x0 ^^^ x1 = x0 ^^^ x1 ^^^ x2 ^^^ x3) ∧
    (x3 ^^^ x0 ^^^ x1 ^^^ x2 = x0 ^^^ x1 ^^^ x2 ^^^ x3) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_getLsbD_eq; intro bit _; simp only [BitVec.getLsbD_xor];
     cases x0.getLsbD bit <;> cases x1.getLsbD bit <;>
       cases x2.getLsbD bit <;> cases x3.getLsbD bit <;> rfl)

private theorem mixFsByte_eq_mixColumns (s : State) (r col : Fin 4) :
    mixFsByte (s.getD (r.val + 4 * col.val) 0#8)
      (s.getD (((r.val + 1) % 4) + 4 * col.val) 0#8)
      (s.getD (((r.val + 2) % 4) + 4 * col.val) 0#8)
      (s.getD (((r.val + 3) % 4) + 4 * col.val) 0#8) =
      (mixColumns s).getD (r.val + 4 * col.val) 0#8 := by
  rw [open_mixColumns s r col, mixFsByte_eq]
  rcases r with ⟨r, hr⟩
  match r, hr with
  | 0, _ => rfl
  | 1, _ => dsimp [mixColumn]; exact (xor4_rot _ _ _ _).1
  | 2, _ => dsimp [mixColumn]; exact (xor4_rot _ _ _ _).2.1
  | 3, _ => dsimp [mixColumn]; exact (xor4_rot _ _ _ _).2.2
  | _ + 4, hr => omega

private theorem invMixFsByte_eq_invMixColumns (s : State) (r col : Fin 4) :
    invMixFsByte (s.getD (r.val + 4 * col.val) 0#8)
      (s.getD (((r.val + 1) % 4) + 4 * col.val) 0#8)
      (s.getD (((r.val + 2) % 4) + 4 * col.val) 0#8)
      (s.getD (((r.val + 3) % 4) + 4 * col.val) 0#8) =
      (invMixColumns s).getD (r.val + 4 * col.val) 0#8 := by
  rw [open_invMixColumns s r col, invMixFsByte_eq]
  rcases r with ⟨r, hr⟩
  match r, hr with
  | 0, _ => rfl
  | 1, _ => dsimp [invMixColumn]; exact (xor4_rot _ _ _ _).1
  | 2, _ => dsimp [invMixColumn]; exact (xor4_rot _ _ _ _).2.1
  | 3, _ => dsimp [invMixColumn]; exact (xor4_rot _ _ _ _).2.2
  | _ + 4, hr => omega

/-! ## Lifting Scalar Equivalence Across All 4 Lanes & Parities `q ∈ {0, 1, 2, 3}` -/

private theorem invShiftCol_eq :
    ∀ (q r c : Fin 4),
      (c.val + ((4 - q.val % 4) % 4) * r.val) % 4 = (c.val + (4 - q.val) * r.val) % 4 := by
  decide

private theorem col_cancel_eq :
    ∀ (q col r' : Fin 4),
      (((col.val + q.val * r'.val) % 4) + (4 - q.val) * r'.val) % 4 = col.val := by
  decide

private theorem getLane_map (f : State → State) (bs : Blocks4) (lane : Nat) (hl : lane < 4) :
    (bs.map f).getLane lane = f (bs.getLane lane) := by
  match lane, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hl => omega

theorem getD_invShiftRowsPow (q r c : Nat) (hq : q < 4) (hr : r < 4) (hc : c < 4) (s : State) :
    (invShiftRowsPow q s).getD (r + 4 * c) 0#8 =
      s.getD (r + 4 * ((c + (4 - q) * r) % 4)) 0#8 := by
  rw [invShiftRowsPow, getD_shiftRowsPow _ s r c hr hc, invShiftCol_eq ⟨q, hq⟩ ⟨r, hr⟩ ⟨c, hc⟩]

private theorem rot1_eval (q lane : Fin 4) (w : BitVec 64) (g : Nat → Nat → Bool)
    (hw : ∀ (r c : Fin 4),
      w.getLsbD (16 * r.val + 4 * c.val + lane.val) =
        g r.val ((c.val + (4 - q.val) * r.val) % 4))
    (r c : Fin 4) :
    (rot1Fn q w).getLsbD (16 * r.val + 4 * c.val + lane.val) =
      g ((r.val + 1) % 4) ((c.val + (4 - q.val) * r.val) % 4) := by
  let col : Fin 4 := ⟨(c.val + (4 - q.val) * r.val) % 4, by omega⟩
  let r1 : Fin 4 := ⟨(r.val + 1) % 4, by omega⟩
  let c1 : Fin 4 := ⟨(col.val + q.val * r1.val) % 4, by omega⟩
  rw [getLsbD_rot1Fn q w ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩]
  have hidx := rot1Route_invShiftIdx q r c lane
  dsimp only at hidx
  rw [hidx, hw r1 c1, col_cancel_eq q col r1]

private theorem rot2_eval (q lane : Fin 4) (w : BitVec 64) (g : Nat → Nat → Bool)
    (hw : ∀ (r c : Fin 4),
      w.getLsbD (16 * r.val + 4 * c.val + lane.val) =
        g r.val ((c.val + (4 - q.val) * r.val) % 4))
    (r c : Fin 4) :
    (rot2Fn q w).getLsbD (16 * r.val + 4 * c.val + lane.val) =
      g ((r.val + 2) % 4) ((c.val + (4 - q.val) * r.val) % 4) := by
  let col : Fin 4 := ⟨(c.val + (4 - q.val) * r.val) % 4, by omega⟩
  let r2 : Fin 4 := ⟨(r.val + 2) % 4, by omega⟩
  let c2 : Fin 4 := ⟨(col.val + q.val * r2.val) % 4, by omega⟩
  rw [getLsbD_rot2Fn q w ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩]
  have hidx := rot2Route_invShiftIdx q r c lane
  dsimp only at hidx
  rw [hidx, hw r2 c2, col_cancel_eq q col r2]

private theorem mixColumnsQ_eq_gen (q : Nat) (hq : q < 4) (st : FsState) :
    mixColumnsQ q st = mixColumnsGen (rot1Fn ⟨q, hq⟩) (rot2Fn ⟨q, hq⟩) st := by
  match q, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hq => omega

private theorem invMixColumnsQ_eq_gen (q : Nat) (hq : q < 4) (st : FsState) :
    invMixColumnsQ q st = invMixColumnsGen (rot1Fn ⟨q, hq⟩) (rot2Fn ⟨q, hq⟩) st := by
  match q, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hq => omega

/-- `mixColumnsQ q` on `invShiftRowsPow q`-fixsliced 4-block state equals `mixColumns` on all 4 lanes. -/
theorem mixColumnsQ_bitslice (q : Nat) (hq : q < 4) (bs : Blocks4) :
    mixColumnsQ q (bitslice (bs.map (invShiftRowsPow q))) =
      bitslice (bs.map (fun s => invShiftRowsPow q (mixColumns s))) := by
  rw [mixColumnsQ_eq_gen q hq]
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  let qf : Fin 4 := ⟨q, hq⟩
  let lf : Fin 4 := ⟨lane, hl⟩
  let st := bitslice (bs.map (invShiftRowsPow q))
  let s := bs.getLane lane
  have hst : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (st.getSlice p'.val).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8).getLsbD p'.val := by
    intro p' r' c'
    rw [getLsbD_bitslice _ p'.val r'.val c'.val lane p'.isLt r'.isLt c'.isLt hl,
      getLane_map _ bs lane hl, getD_invShiftRowsPow q r'.val c'.val hq r'.isLt c'.isLt s]
  have hb : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (rot1Fn qf (st.getSlice p'.val)).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8).getLsbD p'.val :=
    fun p' r' c' => rot1_eval qf lf (st.getSlice p'.val)
      (fun rr cc => (s.getD (rr + 4 * cc) 0#8).getLsbD p'.val) (hst p') r' c'
  let cWord : Fin 8 → BitVec 64 := fun p' => st.getSlice p'.val ^^^ rot1Fn qf (st.getSlice p'.val)
  have hcSlice : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (cWord p').getLsbD (16 * r'.val + 4 * c'.val + lane) =
        ((s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8) ^^^
         (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro p' r' c'
    rw [BitVec.getLsbD_xor, hst p' r' c', hb p' r' c', BitVec.getLsbD_xor]
  have hrc : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (rot2Fn qf (cWord p')).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        ((s.getD (((r'.val + 2) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8) ^^^
         (s.getD (((r'.val + 3) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro p' r' c'
    have h := rot2_eval qf lf (cWord p')
      (fun rr cc => ((s.getD (rr + 4 * cc) 0#8) ^^^ (s.getD (((rr + 1) % 4) + 4 * cc) 0#8)).getLsbD p'.val)
      (hcSlice p') r' c'
    have hr3 : ((r'.val + 2) % 4 + 1) % 4 = (r'.val + 3) % 4 := by omega
    simpa only [hr3] using h
  let xWord : Fin 8 → BitVec 64
    | ⟨0, _⟩ => cWord ⟨7, by omega⟩
    | ⟨1, _⟩ => cWord ⟨0, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨2, _⟩ => cWord ⟨1, by omega⟩
    | ⟨3, _⟩ => cWord ⟨2, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨4, _⟩ => cWord ⟨3, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨5, _⟩ => cWord ⟨4, by omega⟩
    | ⟨6, _⟩ => cWord ⟨5, by omega⟩
    | ⟨7, _⟩ => cWord ⟨6, by omega⟩
    | ⟨_ + 8, h⟩ => absurd h (by omega)
  have hxSlice : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (xWord p').getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (xtimeBits ((s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8) ^^^
          (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8))).getLsbD p'.val := by
    intro ⟨p', hp'⟩ r' c'
    rw [xtimeBits]
    change (xWord ⟨p', hp'⟩).getLsbD _ = (packByteBits _).getLsbD p'
    rw [getLsbD_packByteBits _ p' hp']
    match p', hp' with
    | 0, _ => exact hcSlice ⟨7, by omega⟩ r' c'
    | 1, _ =>
      dsimp only [xWord]
      rw [BitVec.getLsbD_xor, hcSlice ⟨0, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']; rfl
    | 2, _ => exact hcSlice ⟨1, by omega⟩ r' c'
    | 3, _ =>
      dsimp only [xWord]
      rw [BitVec.getLsbD_xor, hcSlice ⟨2, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']; rfl
    | 4, _ =>
      dsimp only [xWord]
      rw [BitVec.getLsbD_xor, hcSlice ⟨3, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']; rfl
    | 5, _ => exact hcSlice ⟨4, by omega⟩ r' c'
    | 6, _ => exact hcSlice ⟨5, by omega⟩ r' c'
    | 7, _ => exact hcSlice ⟨6, by omega⟩ r' c'
    | _ + 8, hp' => omega
  let col : Fin 4 := ⟨(c + (4 - q) * r) % 4, by omega⟩
  rw [getLane_map _ bs lane hl, getD_invShiftRowsPow q r c hq hr hc (mixColumns s),
    ← mixFsByte_eq_mixColumns s ⟨r, hr⟩ col]
  have hout : (mixColumnsGen (rot1Fn qf) (rot2Fn qf) st).getSlice p =
      rot1Fn qf (st.getSlice p) ^^^ xWord ⟨p, hp⟩ ^^^ rot2Fn qf (cWord ⟨p, hp⟩) := by
    match p, hp with
    | 0, _ | 2, _ | 5, _ | 6, _ | 7, _ => rfl
    | 1, _ | 3, _ | 4, _ => exact congrArg (· ^^^ _) (BitVec.xor_assoc _ _ _)
    | _ + 8, hp => omega
  have outer_xor : ∀ (u v : BitVec 8) (k : Nat),
      (u ^^^ v).getLsbD k = (u.getLsbD k ^^ v.getLsbD k) := fun _ _ _ => BitVec.getLsbD_xor
  dsimp only [mixFsByte]
  rw [hout, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
    outer_xor (_ ^^^ xtimeBits _) (_ ^^^ _), outer_xor _ (xtimeBits _),
    hb ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩, hxSlice ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩, hrc ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩]

/-- `invMixColumnsQ q` on `invShiftRowsPow q`-fixsliced 4-block state equals `invMixColumns` on all 4 lanes. -/
theorem invMixColumnsQ_bitslice (q : Nat) (hq : q < 4) (bs : Blocks4) :
    invMixColumnsQ q (bitslice (bs.map (invShiftRowsPow q))) =
      bitslice (bs.map (fun s => invShiftRowsPow q (invMixColumns s))) := by
  rw [invMixColumnsQ_eq_gen q hq]
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  let qf : Fin 4 := ⟨q, hq⟩
  let lf : Fin 4 := ⟨lane, hl⟩
  let st := bitslice (bs.map (invShiftRowsPow q))
  let s := bs.getLane lane
  have outer_xor : ∀ (u v : BitVec 8) (k : Nat),
      (u ^^^ v).getLsbD k = (u.getLsbD k ^^ v.getLsbD k) := fun _ _ _ => BitVec.getLsbD_xor
  have hst : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (st.getSlice p'.val).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8).getLsbD p'.val := by
    intro p' r' c'
    rw [getLsbD_bitslice _ p'.val r'.val c'.val lane p'.isLt r'.isLt c'.isLt hl,
      getLane_map _ bs lane hl, getD_invShiftRowsPow q r'.val c'.val hq r'.isLt c'.isLt s]
  have hb : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (rot1Fn qf (st.getSlice p'.val)).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8).getLsbD p'.val :=
    fun p' r' c' => rot1_eval qf lf (st.getSlice p'.val)
      (fun rr cc => (s.getD (rr + 4 * cc) 0#8).getLsbD p'.val) (hst p') r' c'
  let cWord : Fin 8 → BitVec 64 := fun p' => st.getSlice p'.val ^^^ rot1Fn qf (st.getSlice p'.val)
  have hcSlice : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (cWord p').getLsbD (16 * r'.val + 4 * c'.val + lane) =
        ((s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8) ^^^
         (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro p' r' c'
    rw [BitVec.getLsbD_xor, hst p' r' c', hb p' r' c', BitVec.getLsbD_xor]
  let dWord : Fin 8 → BitVec 64
    | ⟨0, _⟩ => st.getSlice 0 ^^^ cWord ⟨7, by omega⟩
    | ⟨1, _⟩ => st.getSlice 1 ^^^ cWord ⟨0, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨2, _⟩ => st.getSlice 2 ^^^ cWord ⟨1, by omega⟩
    | ⟨3, _⟩ => st.getSlice 3 ^^^ cWord ⟨2, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨4, _⟩ => st.getSlice 4 ^^^ cWord ⟨3, by omega⟩ ^^^ cWord ⟨7, by omega⟩
    | ⟨5, _⟩ => st.getSlice 5 ^^^ cWord ⟨4, by omega⟩
    | ⟨6, _⟩ => st.getSlice 6 ^^^ cWord ⟨5, by omega⟩
    | ⟨7, _⟩ => st.getSlice 7 ^^^ cWord ⟨6, by omega⟩
    | ⟨_ + 8, h⟩ => absurd h (by omega)
  have hdSlice : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (dWord p').getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (dPair (s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)
          (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro ⟨p', hp'⟩ r' c'
    dsimp only [dPair]
    rw [outer_xor _ (xtimeBits _), xtimeBits]
    change _ = (_ ^^ (packByteBits _).getLsbD p')
    rw [getLsbD_packByteBits _ p' hp']
    match p', hp' with
    | 0, _ =>
      dsimp only [dWord]; rw [BitVec.getLsbD_xor, hst ⟨0, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']; rfl
    | 1, _ =>
      dsimp only [dWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hst ⟨1, by omega⟩ r' c',
        hcSlice ⟨0, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 2, _ =>
      dsimp only [dWord]; rw [BitVec.getLsbD_xor, hst ⟨2, by omega⟩ r' c', hcSlice ⟨1, by omega⟩ r' c']; rfl
    | 3, _ =>
      dsimp only [dWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hst ⟨3, by omega⟩ r' c',
        hcSlice ⟨2, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 4, _ =>
      dsimp only [dWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hst ⟨4, by omega⟩ r' c',
        hcSlice ⟨3, by omega⟩ r' c', hcSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 5, _ =>
      dsimp only [dWord]; rw [BitVec.getLsbD_xor, hst ⟨5, by omega⟩ r' c', hcSlice ⟨4, by omega⟩ r' c']; rfl
    | 6, _ =>
      dsimp only [dWord]; rw [BitVec.getLsbD_xor, hst ⟨6, by omega⟩ r' c', hcSlice ⟨5, by omega⟩ r' c']; rfl
    | 7, _ =>
      dsimp only [dWord]; rw [BitVec.getLsbD_xor, hst ⟨7, by omega⟩ r' c', hcSlice ⟨6, by omega⟩ r' c']; rfl
    | _ + 8, hp' => omega
  let eWord : Fin 8 → BitVec 64
    | ⟨0, _⟩ => cWord ⟨0, by omega⟩ ^^^ dWord ⟨6, by omega⟩
    | ⟨1, _⟩ => cWord ⟨1, by omega⟩ ^^^ dWord ⟨6, by omega⟩ ^^^ dWord ⟨7, by omega⟩
    | ⟨2, _⟩ => cWord ⟨2, by omega⟩ ^^^ dWord ⟨0, by omega⟩ ^^^ dWord ⟨7, by omega⟩
    | ⟨3, _⟩ => cWord ⟨3, by omega⟩ ^^^ dWord ⟨1, by omega⟩ ^^^ dWord ⟨6, by omega⟩
    | ⟨4, _⟩ => cWord ⟨4, by omega⟩ ^^^ dWord ⟨2, by omega⟩ ^^^ dWord ⟨6, by omega⟩ ^^^ dWord ⟨7, by omega⟩
    | ⟨5, _⟩ => cWord ⟨5, by omega⟩ ^^^ dWord ⟨3, by omega⟩ ^^^ dWord ⟨7, by omega⟩
    | ⟨6, _⟩ => cWord ⟨6, by omega⟩ ^^^ dWord ⟨4, by omega⟩
    | ⟨7, _⟩ => cWord ⟨7, by omega⟩ ^^^ dWord ⟨5, by omega⟩
    | ⟨_ + 8, h⟩ => absurd h (by omega)
  have heSlice : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (eWord p').getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (ePair (s.getD (r'.val + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)
          (s.getD (((r'.val + 1) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro ⟨p', hp'⟩ r' c'
    dsimp only [ePair]
    rw [outer_xor (_ ^^^ _) (mul4Bits _), mul4Bits]
    change _ = (_ ^^ (packByteBits _).getLsbD p')
    rw [getLsbD_packByteBits _ p' hp']
    match p', hp' with
    | 0, _ =>
      dsimp only [eWord]; rw [BitVec.getLsbD_xor, hcSlice ⟨0, by omega⟩ r' c', hdSlice ⟨6, by omega⟩ r' c']; rfl
    | 1, _ =>
      dsimp only [eWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hcSlice ⟨1, by omega⟩ r' c',
        hdSlice ⟨6, by omega⟩ r' c', hdSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 2, _ =>
      dsimp only [eWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hcSlice ⟨2, by omega⟩ r' c',
        hdSlice ⟨0, by omega⟩ r' c', hdSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 3, _ =>
      dsimp only [eWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hcSlice ⟨3, by omega⟩ r' c',
        hdSlice ⟨1, by omega⟩ r' c', hdSlice ⟨6, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 4, _ =>
      dsimp only [eWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_xor, hcSlice ⟨4, by omega⟩ r' c',
        hdSlice ⟨2, by omega⟩ r' c', hdSlice ⟨6, by omega⟩ r' c', hdSlice ⟨7, by omega⟩ r' c']
      simp only [Bool.xor_assoc]
    | 5, _ =>
      dsimp only [eWord]
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, hcSlice ⟨5, by omega⟩ r' c',
        hdSlice ⟨3, by omega⟩ r' c', hdSlice ⟨7, by omega⟩ r' c']
      exact Bool.xor_assoc _ _ _
    | 6, _ =>
      dsimp only [eWord]; rw [BitVec.getLsbD_xor, hcSlice ⟨6, by omega⟩ r' c', hdSlice ⟨4, by omega⟩ r' c']; rfl
    | 7, _ =>
      dsimp only [eWord]; rw [BitVec.getLsbD_xor, hcSlice ⟨7, by omega⟩ r' c', hdSlice ⟨5, by omega⟩ r' c']; rfl
    | _ + 8, hp' => omega
  have hre : ∀ (p' : Fin 8) (r' c' : Fin 4),
      (rot2Fn qf (eWord p')).getLsbD (16 * r'.val + 4 * c'.val + lane) =
        (ePair (s.getD (((r'.val + 2) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)
          (s.getD (((r'.val + 3) % 4) + 4 * ((c'.val + (4 - q) * r'.val) % 4)) 0#8)).getLsbD p'.val := by
    intro p' r' c'
    have h := rot2_eval qf lf (eWord p')
      (fun rr cc => (ePair (s.getD (rr + 4 * cc) 0#8) (s.getD (((rr + 1) % 4) + 4 * cc) 0#8)).getLsbD p'.val)
      (heSlice p') r' c'
    have hr3 : ((r'.val + 2) % 4 + 1) % 4 = (r'.val + 3) % 4 := by omega
    simpa only [hr3] using h
  let col : Fin 4 := ⟨(c + (4 - q) * r) % 4, by omega⟩
  rw [getLane_map _ bs lane hl, getD_invShiftRowsPow q r c hq hr hc (invMixColumns s),
    ← invMixFsByte_eq_invMixColumns s ⟨r, hr⟩ col]
  dsimp only [invMixFsByte]
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor]
  have hout : ((invMixColumnsGen (rot1Fn qf) (rot2Fn qf) st).getSlice p) =
      dWord ⟨p, hp⟩ ^^^ eWord ⟨p, hp⟩ ^^^ rot2Fn qf (eWord ⟨p, hp⟩) := by
    match p, hp with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | _ + 8, hp => omega
  rw [hout, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
    hdSlice ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩, heSlice ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩, hre ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixEquiv
