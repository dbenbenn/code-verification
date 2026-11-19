/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes

/-!
# `grow_amortized` and `grow_one` for `<DecodeError>::push`

Verifies `RawVecInner::grow_amortized` and `RawVec::grow_one` for growing the
`DecodeError` context vector.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `grow_amortized` specification and verification -/

@[expose] def newCap (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 4)

theorem newCap_toNat {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (newCap cap).toNat = max (2 * cap.toNat) 4 := by
  unfold newCap
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

abbrev GrowAmortizedGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def growAmortizedSpec (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, gsp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
    stackAt (gsp - 96#64) allocHookStack
  post := fun (v, cap, ptr, gsp) s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32))) ∗
      A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
      stackAt (gsp - 96#64) allocHookStack

theorem grow_amortized_new_eq {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (if (4#64).ult (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = true then
      if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64
    else 4#64) = newCap cap := by
  have hadd : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64).toNat =
      max (2 * cap.toNat) (cap.toNat + 1) := by
    by_cases hc1 : (cap + 1#64).ule (cap <<< 1) = true
    · simp only [hc1, ite_true, hsh]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
    · simp only [hc1, Bool.false_eq_true, ite_false, hadd]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
  apply BitVec.eq_of_toNat_eq
  rw [newCap_toNat h]
  generalize (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = m1 at hm1 ⊢
  by_cases hc2 : (4#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    change 4 = max (2 * cap.toNat) 4
    omega

@[expose] def growOneStrPairSpec (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, osp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = osp ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
    stackAt (osp - 112#64) allocHookStack
  post := fun (v, cap, _ptr, osp) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32) ∗
      A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
      stackAt (osp - 112#64) allocHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
