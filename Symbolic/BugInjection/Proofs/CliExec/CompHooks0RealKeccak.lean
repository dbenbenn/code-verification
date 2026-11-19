/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Hash.Keccak
public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
meta import ProofLib.ProgramReflection

/-!
# Forced-`BitVec 64` FIPS 202 Keccak-f[1600], SHA3, and SHAKE Wrappers for Kernel Evaluation

Provides forced-`Nat` / forced-`BitVec 64` bitwise primitives (`withForcedNat`, `withForcedBV64`,
`leBytesFast`, `xor64Fast`, `and64Fast`, `not64Fast`, `shr64Fast`, `rotr64Fast`, `rotl64Fast`)
using Lean's native C++ kernel `Nat.xor`/`Nat.land`/`Nat.shiftRight` reduction, and eliminates
call-by-name thunk duplication across the 24 rounds of `Keccak-f[1600]` so `rfl_kernel` evaluates
`SHA3-256`, `SHA3-512`, `SHAKE-128`, and `SHAKE-256` with minimal arena memory.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak

open scoped ProofLib.ProgramReflection
open CryptoGames.SHA3 (
  KeccakState keccakAbsorb keccakAbsorbBlock keccakExtractRate keccakF1600
  keccakF1600Round keccakPadBlocks keccakRhoOffset keccakRoundConstants keccakSponge
  keccakSqueezeBlocks keccakZeroState laneGet packLane64 sha3_256List sha3_512List
  shake256List unpackLane64
)

public section
set_option autoImplicit false

@[expose] def withForcedNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) n (k 0) (fun m => k (Nat.add m 1))

theorem withForcedNat_eq {α : Type} (n : Nat) (k : Nat → α) : withForcedNat n k = k n := by
  cases n <;> rfl

@[expose] def withForcedBV64 {α : Type} (x : BitVec 64) (k : BitVec 64 → α) : α :=
  withForcedNat x.toNat (fun n => k (BitVec.ofNat 64 n))

theorem withForcedBV64_eq {α : Type} (x : BitVec 64) (k : BitVec 64 → α) :
    withForcedBV64 x k = k x := by
  unfold withForcedBV64; rw [withForcedNat_eq]
  rw [show BitVec.ofNat 64 x.toNat = x from
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])]

@[expose] def leBytesFast : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | n + 1, w =>
    withForcedNat (Nat.mod w 256) fun b =>
    withForcedNat (Nat.div w 256) fun w' =>
    BitVec.ofNat 8 b :: leBytesFast n w'

theorem leBytesFast_length : ∀ (n w : Nat), (leBytesFast n w).length = n
  | 0, _ => rfl
  | n + 1, w => by
    unfold leBytesFast
    rw [withForcedNat_eq, withForcedNat_eq]
    simp [leBytesFast_length n (Nat.div w 256)]

@[expose] def xor64Fast (x y : BitVec 64) : BitVec 64 :=
  withForcedNat (Nat.xor x.toNat y.toNat) (BitVec.ofNat 64)

@[expose] def and64Fast (x y : BitVec 64) : BitVec 64 :=
  withForcedNat (Nat.land x.toNat y.toNat) (BitVec.ofNat 64)

@[expose] def not64Fast (x : BitVec 64) : BitVec 64 :=
  withForcedNat (Nat.sub 18446744073709551615 x.toNat) (BitVec.ofNat 64)

@[expose] def add64Fast (x y : BitVec 64) : BitVec 64 :=
  withForcedNat (Nat.mod (Nat.add x.toNat y.toNat) 18446744073709551616) (BitVec.ofNat 64)

@[expose] def shr64Fast (x : BitVec 64) (s : Nat) : BitVec 64 :=
  withForcedNat (Nat.shiftRight x.toNat s) (BitVec.ofNat 64)

@[expose] def u64RotrNat (a s : Nat) : Nat :=
  let p := Nat.pow 2 s
  Nat.add (Nat.div a p) (Nat.mul (Nat.mod a p) (Nat.pow 2 (Nat.sub 64 s)))

@[expose] def rotr64Fast (x : BitVec 64) (s : Nat) : BitVec 64 :=
  withForcedNat x.toNat fun a =>
    withForcedNat (u64RotrNat a s) (BitVec.ofNat 64)

@[expose] def rotl64Fast (x : BitVec 64) (s : Nat) : BitVec 64 :=
  let r := Nat.mod s 64
  if r == 0 then withForcedBV64 x id
  else rotr64Fast x (Nat.sub 64 r)

theorem xor64Fast_eq (x y : BitVec 64) : xor64Fast x y = x ^^^ y := by
  unfold xor64Fast; rw [withForcedNat_eq]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (x.toNat ^^^ y.toNat)).toNat = (x ^^^ y).toNat
  rw [BitVec.toNat_ofNat, ← BitVec.toNat_xor]
  exact Nat.mod_eq_of_lt (x ^^^ y).isLt

theorem and64Fast_eq (x y : BitVec 64) : and64Fast x y = x &&& y := by
  unfold and64Fast; rw [withForcedNat_eq]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (x.toNat &&& y.toNat)).toNat = (x &&& y).toNat
  rw [BitVec.toNat_ofNat, ← BitVec.toNat_and]
  exact Nat.mod_eq_of_lt (x &&& y).isLt

theorem not64Fast_eq (x : BitVec 64) : not64Fast x = ~~~x := by
  unfold not64Fast; rw [withForcedNat_eq]
  change BitVec.ofNat 64 (18446744073709551615 - x.toNat) = ~~~x
  bv_omega

theorem add64Fast_eq (x y : BitVec 64) : add64Fast x y = x + y := by
  unfold add64Fast; rw [withForcedNat_eq]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 ((x.toNat + y.toNat) % 2 ^ 64)).toNat = (x + y).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_mod]

theorem shr64Fast_eq (x : BitVec 64) (s : Nat) : shr64Fast x s = x >>> s := by
  unfold shr64Fast; rw [withForcedNat_eq]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (x.toNat >>> s)).toNat = (x >>> s).toNat
  rw [BitVec.toNat_ofNat, ← BitVec.toNat_ushiftRight]
  exact Nat.mod_eq_of_lt (x >>> s).isLt

theorem rotr64Fast_eq (x : BitVec 64) (s : Nat) (hs : 0 < s ∧ s < 64) :
    rotr64Fast x s = x.rotateRight s := by
  unfold rotr64Fast; rw [withForcedNat_eq, withForcedNat_eq]
  change BitVec.ofNat 64 (x.toNat / (2 ^ s) + (x.toNat % (2 ^ s)) * (2 ^ (64 - s))) = x.rotateRight s
  apply BitVec.eq_of_toNat_eq
  have hmod : s % 64 = s := Nat.mod_eq_of_lt hs.2
  rw [BitVec.toNat_ofNat, BitVec.toNat_rotateRight, hmod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hpow : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hs.2)]
  have h1 : x.toNat / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), Nat.mul_comm, ← hpow]; exact x.isLt
  have hlt : x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (64 - s) < 2 ^ 64 := by
    have h2 := Nat.le_sub_one_of_lt (Nat.mod_lt x.toNat (Nat.two_pow_pos s))
    calc x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (64 - s)
      _ < 2 ^ (64 - s) + (2 ^ s - 1) * 2 ^ (64 - s) :=
          Nat.add_lt_add_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
      _ = (1 + (2 ^ s - 1)) * 2 ^ (64 - s) := by rw [Nat.add_mul, Nat.one_mul]
      _ = 2 ^ s * 2 ^ (64 - s) := by rw [Nat.add_sub_cancel' (Nat.two_pow_pos s)]
      _ = 2 ^ 64 := hpow.symm
  have hm2 : (x.toNat * 2 ^ (64 - s)) % 2 ^ 64 = (x.toNat % 2 ^ s) * 2 ^ (64 - s) := by
    have hdiv : x.toNat = 2 ^ s * (x.toNat / 2 ^ s) + x.toNat % 2 ^ s := (Nat.div_add_mod _ _).symm
    conv_lhs => rw [hdiv, Nat.add_mul, Nat.mul_right_comm (2 ^ s), ← hpow, Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt)
  rw [hm2, Nat.mod_eq_of_lt hlt]
  have hdisj : (x.toNat / 2 ^ s) &&& ((x.toNat % 2 ^ s) * 2 ^ (64 - s)) = 0 := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 64 - s
    · have hlow : ((x.toNat % 2 ^ s) * 2 ^ (64 - s)).testBit i = false := by
        rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]; simp [Nat.not_le_of_lt hi]
      rw [hlow, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))),
          Bool.false_and]
  have ha_lt : x.toNat / 2 ^ s < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
  have hb_lt : (x.toNat % 2 ^ s) * 2 ^ (64 - s) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt
  have hand0 : (BitVec.ofNat 64 (x.toNat / 2 ^ s) &&&
      BitVec.ofNat 64 ((x.toNat % 2 ^ s) * 2 ^ (64 - s))) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt, hdisj]; rfl
  have h := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ hand0)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt, Nat.mod_eq_of_lt hlt] at h
  exact h

theorem rotl64Fast_eq (x : BitVec 64) (s : Nat) : rotl64Fast x s = x.rotateLeft s := by
  unfold rotl64Fast
  have hrlt : s % 64 < 64 := Nat.mod_lt s (by omega)
  change (if (s % 64 == 0) = true then withForcedBV64 x id else rotr64Fast x (64 - s % 64)) =
    x.rotateLeft s
  by_cases hr0 : s % 64 = 0
  · simp only [hr0, beq_self_eq_true, ↓reduceIte, withForcedBV64_eq, id_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_rotateLeft, hr0]
    simp only [Nat.sub_zero, Nat.mod_eq_of_lt x.isLt,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt x.isLt, Nat.or_zero,
      Nat.shiftLeft_zero]
  · have hb : (s % 64 == 0) = false := beq_false_of_ne hr0
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [rotr64Fast_eq x (64 - s % 64) (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_rotateRight, BitVec.toNat_rotateLeft,
        Nat.mod_eq_of_lt (show 64 - s % 64 < 64 by omega),
        show 64 - (64 - s % 64) = s % 64 by omega, Nat.or_comm]

@[expose] def forceListNatAux {α : Type} : List Nat → List Nat → (List Nat → α) → α
  | [], acc, k => k acc.reverse
  | x :: xs, acc, k => withForcedNat x fun x' => forceListNatAux xs (x' :: acc) k

@[expose] def forceListNat {α : Type} (xs : List Nat) (k : List Nat → α) : α :=
  forceListNatAux xs [] k

private theorem forceListNatAux_eq {α : Type} :
    ∀ (xs acc : List Nat) (k : List Nat → α), forceListNatAux xs acc k = k (acc.reverse ++ xs)
  | [], acc, k => by simp [forceListNatAux]
  | x :: xs, acc, k => by
    simp only [forceListNatAux, withForcedNat_eq, forceListNatAux_eq xs (x :: acc) k,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem forceListNat_eq {α : Type} (xs : List Nat) (k : List Nat → α) :
    forceListNat xs k = k xs :=
  forceListNatAux_eq xs [] k

@[expose] def forceListBV8Aux {α : Type} :
    List (BitVec 8) → List (BitVec 8) → (List (BitVec 8) → α) → α
  | [], acc, k => k acc.reverse
  | b :: bs, acc, k =>
    withForcedNat b.toNat fun n => forceListBV8Aux bs (BitVec.ofNat 8 n :: acc) k

@[expose] def forceListBV8 {α : Type} (bs : List (BitVec 8)) (k : List (BitVec 8) → α) : α :=
  forceListBV8Aux bs [] k

private theorem forceListBV8Aux_eq {α : Type} :
    ∀ (bs acc : List (BitVec 8)) (k : List (BitVec 8) → α),
      forceListBV8Aux bs acc k = k (acc.reverse ++ bs)
  | [], acc, k => by simp [forceListBV8Aux]
  | b :: bs, acc, k => by
    unfold forceListBV8Aux
    rw [withForcedNat_eq, forceListBV8Aux_eq bs,
      show BitVec.ofNat 8 b.toNat = b from
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt])]
    simp [List.reverse_cons, List.append_assoc]

theorem forceListBV8_eq {α : Type} (bs : List (BitVec 8)) (k : List (BitVec 8) → α) :
    forceListBV8 bs k = k bs :=
  forceListBV8Aux_eq bs [] k

@[expose] def forceListBV64Aux {α : Type} :
    List (BitVec 64) → List (BitVec 64) → (List (BitVec 64) → α) → α
  | [], acc, k => k acc.reverse
  | w :: ws, acc, k => withForcedBV64 w fun w' => forceListBV64Aux ws (w' :: acc) k

@[expose] def forceListBV64 {α : Type} (ws : List (BitVec 64)) (k : List (BitVec 64) → α) : α :=
  forceListBV64Aux ws [] k

private theorem forceListBV64Aux_eq {α : Type} :
    ∀ (ws acc : List (BitVec 64)) (k : List (BitVec 64) → α),
      forceListBV64Aux ws acc k = k (acc.reverse ++ ws)
  | [], acc, k => by simp [forceListBV64Aux]
  | w :: ws, acc, k => by
    simp only [forceListBV64Aux, withForcedBV64_eq, forceListBV64Aux_eq ws (w :: acc) k,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem forceListBV64_eq {α : Type} (ws : List (BitVec 64)) (k : List (BitVec 64) → α) :
    forceListBV64 ws k = k ws :=
  forceListBV64Aux_eq ws [] k

@[expose] def forceArrayBV64 {α : Type} (arr : Array (BitVec 64)) (k : Array (BitVec 64) → α) : α :=
  forceListBV64 arr.toList fun ws => k (Array.mk ws)

theorem forceArrayBV64_eq {α : Type} (arr : Array (BitVec 64)) (k : Array (BitVec 64) → α) :
    forceArrayBV64 arr k = k arr := by
  rcases arr with ⟨ws⟩
  exact forceListBV64_eq ws (fun ws => k (Array.mk ws))

@[expose] def arrayOfFnFast {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  Array.mk ((List.range n).map f)

theorem arrayOfFnFast_eq {α : Type} (n : Nat) (f : Nat → α) :
    arrayOfFnFast n f = Array.ofFn (n := n) (fun i => f i.1) := by
  ext i h1 h2 <;> simp [arrayOfFnFast]

@[expose] def arrayMapFast {α β : Type} (f : α → β) (a : Array α) : Array β :=
  Array.mk (a.toList.map f)

theorem arrayMapFast_eq {α β : Type} (f : α → β) (a : Array α) :
    arrayMapFast f a = a.map f := by
  rcases a with ⟨xs⟩
  simp [arrayMapFast]

@[expose] def arrayGetDFast {α : Type} (a : Array α) (i : Nat) (d : α) : α :=
  a.toList.getD i d

theorem arrayGetDFast_eq {α : Type} (a : Array α) (i : Nat) (d : α) :
    arrayGetDFast a i d = a.getD i d := by
  rcases a with ⟨xs⟩
  simp only [arrayGetDFast, Array.getD, List.getD_eq_getElem?_getD, Array.size]
  by_cases h : i < xs.length <;> simp [h]

@[expose] def arraySetFast {α : Type} (a : Array α) (i : Nat) (v : α) : Array α :=
  Array.mk (a.toList.set i v)

theorem arraySetFast_eq {α : Type} (a : Array α) (i : Nat) (v : α) :
    arraySetFast a i v = a.set! i v := by
  rcases a with ⟨xs⟩
  unfold arraySetFast Array.set! Array.setIfInBounds
  split
  · rfl
  · next hi =>
    exact congrArg Array.mk (List.set_eq_of_length_le (Nat.le_of_not_lt hi))

@[expose] def laneGetFast (s : KeccakState) (x y : Nat) : BitVec 64 :=
  arrayGetDFast s (5 * y + x) 0#64

private theorem laneGetFast_eq (s : KeccakState) (x y : Nat) :
    laneGetFast s x y = laneGet s x y :=
  arrayGetDFast_eq s (5 * y + x) 0#64

@[expose] def packLane64Fast (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  let b0 := (bs.getD off 0#8).toNat
  let b1 := (bs.getD (off + 1) 0#8).toNat
  let b2 := (bs.getD (off + 2) 0#8).toNat
  let b3 := (bs.getD (off + 3) 0#8).toNat
  let b4 := (bs.getD (off + 4) 0#8).toNat
  let b5 := (bs.getD (off + 5) 0#8).toNat
  let b6 := (bs.getD (off + 6) 0#8).toNat
  let b7 := (bs.getD (off + 7) 0#8).toNat
  withForcedNat
    (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))
    (BitVec.ofNat 64)

private theorem packLane64_step (acc : BitVec 64) (b : BitVec 8) (s : Nat)
    (hs : s + 8 ≤ 64) (hacc : acc.toNat < 2 ^ s) :
    (acc ||| (b.zeroExtend 64 <<< s)).toNat = acc.toNat + b.toNat * 2 ^ s := by
  have hb64 : b.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have hbound : b.toNat * 2 ^ s < 2 ^ (s + 8) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ s)]
    exact Nat.mul_lt_mul_of_pos_right b.isLt (Nat.two_pow_pos s)
  have hlt64 : acc.toNat + b.toNat * 2 ^ s < 2 ^ 64 := by
    have hle : 2 ^ (s + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hs
    have hpow : 2 ^ (s + 8) = 2 ^ s + (2 ^ 8 - 1) * 2 ^ s := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ s)]; omega
    have hb1 : b.toNat ≤ 2 ^ 8 - 1 := Nat.le_sub_one_of_lt b.isLt
    have hmul : b.toNat * 2 ^ s ≤ (2 ^ 8 - 1) * 2 ^ s := Nat.mul_le_mul_right _ hb1
    omega
  have hsh : (b.zeroExtend 64 <<< s).toNat = b.toNat * 2 ^ s := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hb64, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hand : (acc &&& (b.zeroExtend 64 <<< s)) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hsh]; change _ = 0
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < s
    · have h1 : (b.toNat * 2 ^ s).testBit i = false := by
        rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]; simp [Nat.not_le_of_lt hi]
      rw [h1, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by omega) (by omega))),
          Bool.false_and]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, hsh]
  exact Nat.mod_eq_of_lt hlt64

private theorem packLane64Fast_eq (bs : List (BitVec 8)) (off : Nat) :
    packLane64Fast bs off = packLane64 bs off := by
  unfold packLane64Fast packLane64
  rw [withForcedNat_eq]
  apply BitVec.eq_of_toNat_eq
  let b0 := bs.getD off 0#8
  let b1 := bs.getD (off + 1) 0#8
  let b2 := bs.getD (off + 2) 0#8
  let b3 := bs.getD (off + 3) 0#8
  let b4 := bs.getD (off + 4) 0#8
  let b5 := bs.getD (off + 5) 0#8
  let b6 := bs.getD (off + 6) 0#8
  let b7 := bs.getD (off + 7) 0#8
  have s0 : (b0.zeroExtend 64).toNat = b0.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b0.isLt; omega)
  let a1 := b0.zeroExtend 64
  let a2 := a1 ||| (b1.zeroExtend 64 <<< 8)
  let a3 := a2 ||| (b2.zeroExtend 64 <<< 16)
  let a4 := a3 ||| (b3.zeroExtend 64 <<< 24)
  let a5 := a4 ||| (b4.zeroExtend 64 <<< 32)
  let a6 := a5 ||| (b5.zeroExtend 64 <<< 40)
  let a7 := a6 ||| (b6.zeroExtend 64 <<< 48)
  have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt; have hb3 := b3.isLt
  have hb4 := b4.isLt; have hb5 := b5.isLt; have hb6 := b6.isLt; have hb7 := b7.isLt
  have s1 := packLane64_step a1 b1 8 (by decide) (by change a1.toNat < _; rw [s0]; omega)
  have s2 := packLane64_step a2 b2 16 (by decide) (by change a2.toNat < _; rw [s1, s0]; omega)
  have s3 := packLane64_step a3 b3 24 (by decide) (by change a3.toNat < _; rw [s2, s1, s0]; omega)
  have s4 := packLane64_step a4 b4 32 (by decide) (by change a4.toNat < _; rw [s3, s2, s1, s0]; omega)
  have s5 := packLane64_step a5 b5 40 (by decide) (by change a5.toNat < _; rw [s4, s3, s2, s1, s0]; omega)
  have s6 := packLane64_step a6 b6 48 (by decide) (by change a6.toNat < _; rw [s5, s4, s3, s2, s1, s0]; omega)
  have s7 := packLane64_step a7 b7 56 (by decide) (by change a7.toNat < _; rw [s6, s5, s4, s3, s2, s1, s0]; omega)
  change (BitVec.ofNat 64
    (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
      256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))))).toNat =
    (a7 ||| (b7.zeroExtend 64 <<< 56)).toNat
  rw [s7, s6, s5, s4, s3, s2, s1, s0, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

@[expose] def unpackLane64Fast (w : BitVec 64) : List (BitVec 8) :=
  withForcedNat w.toNat fun n =>
    let n1 := n / 256; let n2 := n1 / 256
    let n3 := n2 / 256; let n4 := n3 / 256
    let n5 := n4 / 256; let n6 := n5 / 256
    let n7 := n6 / 256
    forceListBV8
      [BitVec.ofNat 8 (n % 256), BitVec.ofNat 8 (n1 % 256),
       BitVec.ofNat 8 (n2 % 256), BitVec.ofNat 8 (n3 % 256),
       BitVec.ofNat 8 (n4 % 256), BitVec.ofNat 8 (n5 % 256),
       BitVec.ofNat 8 (n6 % 256), BitVec.ofNat 8 (n7 % 256)]
      id

private theorem unpackLane64Fast_eq (w : BitVec 64) :
    unpackLane64Fast w = unpackLane64 w := by
  unfold unpackLane64Fast unpackLane64
  rw [withForcedNat_eq, forceListBV8_eq, id_eq]
  have bit8 (s : Nat) : BitVec.ofNat 8 ((w.toNat / 2 ^ s) % 256) = (w >>> s).truncate 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 256)]
  have b0 := bit8 0
  rw [Nat.pow_zero, Nat.div_one] at b0
  have d1 : w.toNat / 256 = w.toNat / 2 ^ 8 := rfl
  have d2 : w.toNat / 2 ^ 8 / 256 = w.toNat / 2 ^ 16 := by rw [Nat.div_div_eq_div_mul]
  have d3 : w.toNat / 2 ^ 16 / 256 = w.toNat / 2 ^ 24 := by rw [Nat.div_div_eq_div_mul]
  have d4 : w.toNat / 2 ^ 24 / 256 = w.toNat / 2 ^ 32 := by rw [Nat.div_div_eq_div_mul]
  have d5 : w.toNat / 2 ^ 32 / 256 = w.toNat / 2 ^ 40 := by rw [Nat.div_div_eq_div_mul]
  have d6 : w.toNat / 2 ^ 40 / 256 = w.toNat / 2 ^ 48 := by rw [Nat.div_div_eq_div_mul]
  have d7 : w.toNat / 2 ^ 48 / 256 = w.toNat / 2 ^ 56 := by rw [Nat.div_div_eq_div_mul]
  rw [d1, d2, d3, d4, d5, d6, d7, b0, bit8 8, bit8 16, bit8 24, bit8 32, bit8 40, bit8 48, bit8 56]

@[expose] def keccakF1600RoundFast (s : KeccakState) (rc : BitVec 64) : KeccakState :=
  forceArrayBV64
    (arrayOfFnFast 5 fun x =>
      xor64Fast (xor64Fast (xor64Fast (xor64Fast
        (laneGetFast s x 0) (laneGetFast s x 1)) (laneGetFast s x 2)) (laneGetFast s x 3))
        (laneGetFast s x 4))
    fun c =>
  forceArrayBV64
    (arrayOfFnFast 5 fun x =>
      xor64Fast (arrayGetDFast c ((x + 4) % 5) 0#64) (rotl64Fast (arrayGetDFast c ((x + 1) % 5) 0#64) 1))
    fun d =>
  forceArrayBV64
    (arrayOfFnFast 25 fun idx =>
      let x := idx % 5
      let y := idx / 5
      xor64Fast (laneGetFast s x y) (arrayGetDFast d x 0#64))
    fun aTheta =>
  forceArrayBV64
    (arrayOfFnFast 25 fun idx =>
      let x' := idx % 5
      let y' := idx / 5
      let x := (x' + 3 * y') % 5
      let y := x'
      rotl64Fast (laneGetFast aTheta x y) (keccakRhoOffset (5 * y + x)))
    fun bRhoPi =>
  forceArrayBV64
    (arrayOfFnFast 25 fun idx =>
      let x := idx % 5
      let y := idx / 5
      let chi := xor64Fast (laneGetFast bRhoPi x y)
        (and64Fast (not64Fast (laneGetFast bRhoPi ((x + 1) % 5) y))
          (laneGetFast bRhoPi ((x + 2) % 5) y))
      if idx == 0 then xor64Fast chi rc else chi)
    id

theorem keccakF1600RoundFast_eq (s : KeccakState) (rc : BitVec 64) :
    keccakF1600RoundFast s rc = keccakF1600Round s rc := by
  unfold keccakF1600RoundFast keccakF1600Round
  simp only [forceArrayBV64_eq, id_eq, arrayOfFnFast_eq, arrayGetDFast_eq, laneGetFast_eq,
    xor64Fast_eq, and64Fast_eq, not64Fast_eq, rotl64Fast_eq]

structure Keccak25 where
  a00 : Nat
  a10 : Nat
  a20 : Nat
  a30 : Nat
  a40 : Nat
  a01 : Nat
  a11 : Nat
  a21 : Nat
  a31 : Nat
  a41 : Nat
  a02 : Nat
  a12 : Nat
  a22 : Nat
  a32 : Nat
  a42 : Nat
  a03 : Nat
  a13 : Nat
  a23 : Nat
  a33 : Nat
  a43 : Nat
  a04 : Nat
  a14 : Nat
  a24 : Nat
  a34 : Nat
  a44 : Nat

@[expose] def forceRow5 {α : Type} (s : KeccakState) (off : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) : α :=
  withForcedNat (arrayGetDFast s off 0#64).toNat fun v0 =>
  withForcedNat (arrayGetDFast s (off + 1) 0#64).toNat fun v1 =>
  withForcedNat (arrayGetDFast s (off + 2) 0#64).toNat fun v2 =>
  withForcedNat (arrayGetDFast s (off + 3) 0#64).toNat fun v3 =>
  withForcedNat (arrayGetDFast s (off + 4) 0#64).toNat fun v4 =>
  k v0 v1 v2 v3 v4

@[expose] def ofKeccakState (s : KeccakState) : Keccak25 :=
  forceRow5 s 0 fun a00 a10 a20 a30 a40 =>
  forceRow5 s 5 fun a01 a11 a21 a31 a41 =>
  forceRow5 s 10 fun a02 a12 a22 a32 a42 =>
  forceRow5 s 15 fun a03 a13 a23 a33 a43 =>
  forceRow5 s 20 fun a04 a14 a24 a34 a44 =>
  { a00, a10, a20, a30, a40,
    a01, a11, a21, a31, a41,
    a02, a12, a22, a32, a42,
    a03, a13, a23, a33, a43,
    a04, a14, a24, a34, a44 }

@[expose] def toKeccakState (q : Keccak25) : KeccakState :=
  Array.mk
    [BitVec.ofNat 64 q.a00, BitVec.ofNat 64 q.a10, BitVec.ofNat 64 q.a20, BitVec.ofNat 64 q.a30, BitVec.ofNat 64 q.a40,
     BitVec.ofNat 64 q.a01, BitVec.ofNat 64 q.a11, BitVec.ofNat 64 q.a21, BitVec.ofNat 64 q.a31, BitVec.ofNat 64 q.a41,
     BitVec.ofNat 64 q.a02, BitVec.ofNat 64 q.a12, BitVec.ofNat 64 q.a22, BitVec.ofNat 64 q.a32, BitVec.ofNat 64 q.a42,
     BitVec.ofNat 64 q.a03, BitVec.ofNat 64 q.a13, BitVec.ofNat 64 q.a23, BitVec.ofNat 64 q.a33, BitVec.ofNat 64 q.a43,
     BitVec.ofNat 64 q.a04, BitVec.ofNat 64 q.a14, BitVec.ofNat 64 q.a24, BitVec.ofNat 64 q.a34, BitVec.ofNat 64 q.a44]

@[expose] def u64RotlNat (a s : Nat) : Nat :=
  let r := Nat.mod s 64
  if r == 0 then a else u64RotrNat a (Nat.sub 64 r)

@[expose] def keccakChiNat (b0 b1 b2 : Nat) : Nat :=
  Nat.xor b0 (Nat.land (Nat.sub 18446744073709551615 b1) b2)

@[expose] def keccakChiRow0 {α : Type} (rc b0 b1 b2 b3 b4 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) : α :=
  withForcedNat b0 fun b0 =>
  withForcedNat b1 fun b1 =>
  withForcedNat b2 fun b2 =>
  withForcedNat b3 fun b3 =>
  withForcedNat b4 fun b4 =>
  withForcedNat (Nat.xor (keccakChiNat b0 b1 b2) rc) fun o0 =>
  withForcedNat (keccakChiNat b1 b2 b3) fun o1 =>
  withForcedNat (keccakChiNat b2 b3 b4) fun o2 =>
  withForcedNat (keccakChiNat b3 b4 b0) fun o3 =>
  withForcedNat (keccakChiNat b4 b0 b1) fun o4 =>
  k o0 o1 o2 o3 o4

@[expose] def keccakChiRow {α : Type} (b0 b1 b2 b3 b4 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) : α :=
  withForcedNat b0 fun b0 =>
  withForcedNat b1 fun b1 =>
  withForcedNat b2 fun b2 =>
  withForcedNat b3 fun b3 =>
  withForcedNat b4 fun b4 =>
  withForcedNat (keccakChiNat b0 b1 b2) fun o0 =>
  withForcedNat (keccakChiNat b1 b2 b3) fun o1 =>
  withForcedNat (keccakChiNat b2 b3 b4) fun o2 =>
  withForcedNat (keccakChiNat b3 b4 b0) fun o3 =>
  withForcedNat (keccakChiNat b4 b0 b1) fun o4 =>
  k o0 o1 o2 o3 o4

@[expose] def keccakRound25 (q : Keccak25) (rc : Nat) : Keccak25 :=
  withForcedNat (Nat.xor (Nat.xor (Nat.xor (Nat.xor q.a00 q.a01) q.a02) q.a03) q.a04) fun c0 =>
  withForcedNat (Nat.xor (Nat.xor (Nat.xor (Nat.xor q.a10 q.a11) q.a12) q.a13) q.a14) fun c1 =>
  withForcedNat (Nat.xor (Nat.xor (Nat.xor (Nat.xor q.a20 q.a21) q.a22) q.a23) q.a24) fun c2 =>
  withForcedNat (Nat.xor (Nat.xor (Nat.xor (Nat.xor q.a30 q.a31) q.a32) q.a33) q.a34) fun c3 =>
  withForcedNat (Nat.xor (Nat.xor (Nat.xor (Nat.xor q.a40 q.a41) q.a42) q.a43) q.a44) fun c4 =>
  withForcedNat (Nat.xor c4 (u64RotlNat c1 1)) fun d0 =>
  withForcedNat (Nat.xor c0 (u64RotlNat c2 1)) fun d1 =>
  withForcedNat (Nat.xor c1 (u64RotlNat c3 1)) fun d2 =>
  withForcedNat (Nat.xor c2 (u64RotlNat c4 1)) fun d3 =>
  withForcedNat (Nat.xor c3 (u64RotlNat c0 1)) fun d4 =>
  keccakChiRow0 rc
    (u64RotlNat (Nat.xor q.a00 d0) 0)
    (u64RotlNat (Nat.xor q.a11 d1) 44)
    (u64RotlNat (Nat.xor q.a22 d2) 43)
    (u64RotlNat (Nat.xor q.a33 d3) 21)
    (u64RotlNat (Nat.xor q.a44 d4) 14)
    fun o00 o10 o20 o30 o40 =>
  keccakChiRow
    (u64RotlNat (Nat.xor q.a30 d3) 28)
    (u64RotlNat (Nat.xor q.a41 d4) 20)
    (u64RotlNat (Nat.xor q.a02 d0) 3)
    (u64RotlNat (Nat.xor q.a13 d1) 45)
    (u64RotlNat (Nat.xor q.a24 d2) 61)
    fun o01 o11 o21 o31 o41 =>
  keccakChiRow
    (u64RotlNat (Nat.xor q.a10 d1) 1)
    (u64RotlNat (Nat.xor q.a21 d2) 6)
    (u64RotlNat (Nat.xor q.a32 d3) 25)
    (u64RotlNat (Nat.xor q.a43 d4) 8)
    (u64RotlNat (Nat.xor q.a04 d0) 18)
    fun o02 o12 o22 o32 o42 =>
  keccakChiRow
    (u64RotlNat (Nat.xor q.a40 d4) 27)
    (u64RotlNat (Nat.xor q.a01 d0) 36)
    (u64RotlNat (Nat.xor q.a12 d1) 10)
    (u64RotlNat (Nat.xor q.a23 d2) 15)
    (u64RotlNat (Nat.xor q.a34 d3) 56)
    fun o03 o13 o23 o33 o43 =>
  keccakChiRow
    (u64RotlNat (Nat.xor q.a20 d2) 62)
    (u64RotlNat (Nat.xor q.a31 d3) 55)
    (u64RotlNat (Nat.xor q.a42 d4) 39)
    (u64RotlNat (Nat.xor q.a03 d0) 41)
    (u64RotlNat (Nat.xor q.a14 d1) 2)
    fun o04 o14 o24 o34 o44 =>
  { a00 := o00, a10 := o10, a20 := o20, a30 := o30, a40 := o40,
    a01 := o01, a11 := o11, a21 := o21, a31 := o31, a41 := o41,
    a02 := o02, a12 := o12, a22 := o22, a32 := o32, a42 := o42,
    a03 := o03, a13 := o13, a23 := o23, a33 := o33, a43 := o43,
    a04 := o04, a14 := o14, a24 := o24, a34 := o34, a44 := o44 }

@[expose] def keccakRoundConstantsNat : List Nat :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
   0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
   0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
   0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

private theorem u64RotrNat_lt (x : BitVec 64) {s : Nat} (hs : 0 < s ∧ s < 64) :
    u64RotrNat x.toNat s < 2 ^ 64 := by
  unfold u64RotrNat
  change x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (64 - s) < 2 ^ 64
  have hpow : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hs.2)]
  have h1 : x.toNat / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), Nat.mul_comm, ← hpow]; exact x.isLt
  have h2 := Nat.le_sub_one_of_lt (Nat.mod_lt x.toNat (Nat.two_pow_pos s))
  calc x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (64 - s)
    _ < 2 ^ (64 - s) + (2 ^ s - 1) * 2 ^ (64 - s) :=
        Nat.add_lt_add_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
    _ = (1 + (2 ^ s - 1)) * 2 ^ (64 - s) := by rw [Nat.add_mul, Nat.one_mul]
    _ = 2 ^ s * 2 ^ (64 - s) := by rw [Nat.add_sub_cancel' (Nat.two_pow_pos s)]
    _ = 2 ^ 64 := hpow.symm

private theorem u64RotlNat_lt (x : BitVec 64) (s : Nat) : u64RotlNat x.toNat s < 2 ^ 64 := by
  unfold u64RotlNat
  have hrlt : s % 64 < 64 := Nat.mod_lt s (by omega)
  change (if (s % 64 == 0) = true then x.toNat else u64RotrNat x.toNat (64 - s % 64)) < 2 ^ 64
  by_cases hr0 : s % 64 = 0
  · simp [hr0, x.isLt]
  · have hb : (s % 64 == 0) = false := beq_false_of_ne hr0
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact u64RotrNat_lt x (by omega)

private theorem u64RotlNat_toNat (x : BitVec 64) (s : Nat) :
    u64RotlNat x.toNat s = (x.rotateLeft s).toNat := by
  have hrot : BitVec.ofNat 64 (u64RotlNat x.toNat s) = rotl64Fast x s := by
    unfold u64RotlNat rotl64Fast rotr64Fast
    change BitVec.ofNat 64 (if (s % 64 == 0) = true then x.toNat else u64RotrNat x.toNat (64 - s % 64)) =
      if (s % 64 == 0) = true then withForcedBV64 x id else
        withForcedNat x.toNat fun a => withForcedNat (u64RotrNat a (64 - s % 64)) (BitVec.ofNat 64)
    by_cases hr0 : s % 64 = 0
    · simp [hr0, withForcedBV64_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp [beq_false_of_ne hr0, withForcedNat_eq]
  rw [← rotl64Fast_eq, ← hrot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (u64RotlNat_lt x s)]

private theorem nat_xor_toNat (x y : BitVec 64) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := by
  rw [BitVec.toNat_xor]; rfl

private theorem nat_and_toNat (x y : BitVec 64) : Nat.land x.toNat y.toNat = (x &&& y).toNat := by
  rw [BitVec.toNat_and]; rfl

private theorem nat_not_toNat (x : BitVec 64) :
    Nat.sub 18446744073709551615 x.toNat = (~~~x).toNat := by
  have h := congrArg BitVec.toNat (not64Fast_eq x)
  unfold not64Fast at h
  rw [withForcedNat_eq] at h
  change (BitVec.ofNat 64 (18446744073709551615 - x.toNat)).toNat = (~~~x).toNat at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega)] at h
  exact h

private theorem chi_toNat (b0 b1 b2 : BitVec 64) :
    keccakChiNat b0.toNat b1.toNat b2.toNat = (b0 ^^^ (~~~b1 &&& b2)).toNat := by
  unfold keccakChiNat
  rw [nat_not_toNat, nat_and_toNat, nat_xor_toNat]

private theorem keccakRound25_ofKeccakState (s : KeccakState) (rc : BitVec 64) :
    keccakRound25 (ofKeccakState s) rc.toNat = ofKeccakState (keccakF1600Round s rc) := by
  rw [← keccakF1600RoundFast_eq]
  unfold keccakRound25 keccakChiRow0 keccakChiRow ofKeccakState forceRow5 keccakF1600RoundFast
    laneGetFast
  simp only [forceArrayBV64_eq, id_eq, withForcedNat_eq, xor64Fast_eq, and64Fast_eq,
    not64Fast_eq, rotl64Fast_eq, chi_toNat, nat_xor_toNat, u64RotlNat_toNat]
  rfl

private theorem toKeccakState_ofKeccakState_round (s : KeccakState) (rc : BitVec 64) :
    toKeccakState (ofKeccakState (keccakF1600Round s rc)) = keccakF1600Round s rc := by
  have hsize : (keccakF1600Round s rc).size = 25 := by simp [keccakF1600Round]
  generalize keccakF1600Round s rc = a at hsize ⊢
  rcases a with ⟨ws⟩
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4,
    _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ | ⟨w9,
    _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14,
    _ | ⟨w15, _ | ⟨w16, _ | ⟨w17, _ | ⟨w18, _ | ⟨w19,
    _ | ⟨w20, _ | ⟨w21, _ | ⟨w22, _ | ⟨w23, _ | ⟨w24, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases hsize
  unfold ofKeccakState forceRow5 toKeccakState arrayGetDFast
  simp only [withForcedNat_eq, List.getD_cons_zero, List.getD_cons_succ, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

private theorem foldl_keccakRound25 :
    ∀ (rcs : List (BitVec 64)) (s : KeccakState),
      (rcs.map BitVec.toNat).foldl keccakRound25 (ofKeccakState s) =
        ofKeccakState (rcs.foldl keccakF1600Round s)
  | [], _ => rfl
  | rc :: rcs, s => by
    simp only [List.map_cons, List.foldl_cons, keccakRound25_ofKeccakState]
    exact foldl_keccakRound25 rcs (keccakF1600Round s rc)

@[expose] def keccakF1600Fast (s : KeccakState) : KeccakState :=
  toKeccakState (keccakRoundConstantsNat.foldl keccakRound25 (ofKeccakState s))

theorem keccakF1600Fast_eq (s : KeccakState) : keccakF1600Fast s = keccakF1600 s := by
  have hrcs : keccakRoundConstantsNat = keccakRoundConstants.map BitVec.toNat := rfl
  have hlast : keccakRoundConstants =
      keccakRoundConstants.take 23 ++ [0x8000000080008008#64] := rfl
  unfold keccakF1600Fast keccakF1600
  rw [hrcs, foldl_keccakRound25]
  conv_rhs => rw [hlast, List.foldl_append, List.foldl_cons, List.foldl_nil]
  conv_lhs => rw [hlast, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact toKeccakState_ofKeccakState_round _ _

@[expose] def keccakAbsorbBlockFast (rateLanes : Nat) (s : KeccakState) (blk : List (BitVec 8)) :
    KeccakState :=
  forceListBV8 blk fun blk' =>
    forceArrayBV64
      (arrayOfFnFast 25 fun idx =>
        if idx < rateLanes then xor64Fast (arrayGetDFast s idx 0#64) (packLane64Fast blk' (8 * idx))
        else arrayGetDFast s idx 0#64)
      keccakF1600Fast

theorem keccakAbsorbBlockFast_eq (rateLanes : Nat) (s : KeccakState) (blk : List (BitVec 8)) :
    keccakAbsorbBlockFast rateLanes s blk = keccakAbsorbBlock rateLanes s blk := by
  unfold keccakAbsorbBlockFast keccakAbsorbBlock
  simp only [forceListBV8_eq, forceArrayBV64_eq, arrayOfFnFast_eq, arrayGetDFast_eq,
    xor64Fast_eq, packLane64Fast_eq, keccakF1600Fast_eq]

@[expose] def keccakPadBlocksFast (rateBytes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    List (List (BitVec 8)) :=
  if rateBytes == 0 then [] else
  let fullCount := msg.length / rateBytes
  let remLen := msg.length % rateBytes
  let fullBlocks := (List.range fullCount).map fun i => (msg.drop (i * rateBytes)).take rateBytes
  let tailBytes := msg.drop (fullCount * rateBytes)
  let lastBlock := (List.range rateBytes).map fun j =>
    let base : BitVec 8 :=
      if j < remLen then tailBytes.getD j 0#8
      else if j == remLen then dsByte
      else 0#8
    if j == rateBytes - 1 then
      BitVec.ofNat 8 (if base.toNat < 128 then base.toNat + 128 else base.toNat - 128)
    else base
  fullBlocks ++ [forceListBV8 lastBlock id]

private theorem xor80_table :
    ((List.range 256).all fun n =>
      decide (BitVec.ofNat 8 (if n < 128 then n + 128 else n - 128) =
        BitVec.ofNat 8 n ^^^ 0x80#8)) = true := by
  rfl_kernel

private theorem xor80_eq (b : BitVec 8) :
    BitVec.ofNat 8 (if b.toNat < 128 then b.toNat + 128 else b.toNat - 128) = b ^^^ 0x80#8 := by
  have h := of_decide_eq_true (List.all_eq_true.mp xor80_table b.toNat (List.mem_range.mpr b.isLt))
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

private theorem keccakPadBlocksFast_eq (rateBytes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    keccakPadBlocksFast rateBytes dsByte msg = keccakPadBlocks rateBytes dsByte msg := by
  unfold keccakPadBlocksFast keccakPadBlocks
  simp only [forceListBV8_eq, id_eq, xor80_eq]

@[expose] def keccakAbsorbFast (rateLanes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    KeccakState :=
  forceListBV8 msg fun msg' =>
    (keccakPadBlocksFast (8 * rateLanes) dsByte msg').foldl (keccakAbsorbBlockFast rateLanes)
      (forceArrayBV64 keccakZeroState id)

theorem keccakAbsorbFast_eq (rateLanes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    keccakAbsorbFast rateLanes dsByte msg = keccakAbsorb rateLanes dsByte msg := by
  unfold keccakAbsorbFast keccakAbsorb
  simp only [forceListBV8_eq, forceArrayBV64_eq, id_eq, keccakPadBlocksFast_eq,
    show keccakAbsorbBlockFast rateLanes = keccakAbsorbBlock rateLanes from
      funext₂ (keccakAbsorbBlockFast_eq rateLanes)]

@[expose] def keccakExtractRateFast (rateLanes : Nat) (s : KeccakState) : List (BitVec 8) :=
  forceListBV8 (((List.range rateLanes).map fun idx => unpackLane64Fast (arrayGetDFast s idx 0#64)).flatten) id

theorem keccakExtractRateFast_eq (rateLanes : Nat) (s : KeccakState) :
    keccakExtractRateFast rateLanes s = keccakExtractRate rateLanes s := by
  unfold keccakExtractRateFast keccakExtractRate
  simp only [forceListBV8_eq, id_eq, arrayGetDFast_eq, unpackLane64Fast_eq]

@[expose] def keccakSqueezeBlocksFast (rateLanes : Nat) : Nat → KeccakState → List (BitVec 8)
  | 0, _ => []
  | 1, s => keccakExtractRateFast rateLanes s
  | n + 2, s =>
    forceArrayBV64 s fun s =>
    keccakExtractRateFast rateLanes s ++
      keccakSqueezeBlocksFast rateLanes (n + 1) (keccakF1600Fast s)

theorem keccakSqueezeBlocksFast_eq (rateLanes : Nat) :
    ∀ (n : Nat) (s : KeccakState),
      keccakSqueezeBlocksFast rateLanes n s = keccakSqueezeBlocks rateLanes n s
  | 0, _ => rfl
  | 1, s => keccakExtractRateFast_eq rateLanes s
  | n + 2, s => by
    simp only [keccakSqueezeBlocksFast, keccakSqueezeBlocks, forceArrayBV64_eq,
      keccakExtractRateFast_eq, keccakF1600Fast_eq, keccakSqueezeBlocksFast_eq rateLanes (n + 1)]

@[expose] def keccakSpongeFast (rateLanes : Nat) (dsByte : BitVec 8) (outLen : Nat)
    (msg : List (BitVec 8)) : List (BitVec 8) :=
  let rateBytes := 8 * rateLanes
  let nBlocks := (outLen + rateBytes - 1) / rateBytes
  forceListBV8 (keccakSqueezeBlocksFast rateLanes nBlocks (keccakAbsorbFast rateLanes dsByte msg))
    fun raw => forceListBV8 ((List.range outLen).map fun i => raw.getD i 0#8) id

theorem keccakSpongeFast_eq (rateLanes : Nat) (dsByte : BitVec 8) (outLen : Nat)
    (msg : List (BitVec 8)) :
    keccakSpongeFast rateLanes dsByte outLen msg = keccakSponge rateLanes dsByte outLen msg := by
  unfold keccakSpongeFast keccakSponge
  simp only [forceListBV8_eq, id_eq, keccakAbsorbFast_eq, keccakSqueezeBlocksFast_eq]

@[expose] def sha3_256Fast (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSpongeFast 17 0x06#8 32 msg

@[expose] def sha3_512Fast (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSpongeFast 9 0x06#8 64 msg

@[expose] def shake256Fast (outLen : Nat) (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSpongeFast 17 0x1f#8 outLen msg

@[expose] def shake128FirstBlocksFast (seed34 : List (BitVec 8)) (nBlocks : Nat) : List (BitVec 8) :=
  keccakSqueezeBlocksFast 21 nBlocks (keccakAbsorbFast 21 0x1f#8 seed34)

theorem sha3_256Fast_eq : sha3_256Fast = sha3_256List :=
  funext (keccakSpongeFast_eq 17 0x06#8 32)

theorem sha3_512Fast_eq : sha3_512Fast = sha3_512List :=
  funext (keccakSpongeFast_eq 9 0x06#8 64)

theorem shake256Fast_eq (outLen : Nat) : shake256Fast outLen = shake256List outLen :=
  funext (keccakSpongeFast_eq 17 0x1f#8 outLen)

theorem shake128FirstBlocksFast_eq (seed34 : List (BitVec 8)) (nBlocks : Nat) :
    shake128FirstBlocksFast seed34 nBlocks = CryptoGames.MLKEM.shake128FirstBlocks seed34 nBlocks := by
  unfold shake128FirstBlocksFast CryptoGames.MLKEM.shake128FirstBlocks
  rw [keccakAbsorbFast_eq, keccakSqueezeBlocksFast_eq]

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak
