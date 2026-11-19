/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.InImageKit

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.GrowOne.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev cliGrowOneStack : Nat := finishGrowStackX + 64

abbrev CliGrowBytesGhost := BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

abbrev FGCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_cliGrowOne (sp : BitVec 64) :
    stackAt sp cliGrowOneStack =
      stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp finishGrowStackX 8 (by decide)
  change stackAt sp cliGrowOneStack =
    stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_split_stk (sp : BitVec 64) {stk : Nat}
    (hlo : 0x40 + finishGrowStackX ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - cliGrowOneStack) ∗
        stackAt sp cliGrowOneStack := by
  have heq : stk = cliGrowOneStack + (stk - cliGrowOneStack) := by
    dsimp [cliGrowOneStack]; omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp cliGrowOneStack (stk - cliGrowOneStack) (by omega), ← heq]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

private theorem pull_fg0_err (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

@[expose] def finishGrowZeroCellsSpec (A : RustAlloc) : Spec FGCellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

@[expose] def finishGrowNeCellsSpec (A : RustAlloc) : Spec FGCellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
  post := fun (out, cap, ptr, new, align, stride, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

@[expose] def growOneDirBytesInnerSpec (A : RustAlloc) : Spec CliGrowBytesGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 48 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 48) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length)) ∗
    A.pool ∗ stackAt s.sp cliGrowOneStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 48) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 48 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp cliGrowOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def vecHeaderBytes (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ (unpack64 ptr ++ unpack64 len)

private theorem vecHeader_eq_bytes (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = (a ↦ₛ vecHeaderBytes cap ptr len) := by
  unfold vecHeader vecHeaderBytes
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  simp only [pointsToBytes_append, unpack64_length, h16, ← pointsTo64_eq_pointsToBytes]

private theorem dirEntry_body_eq (b c1 p1 l1 c2 p2 l2 : BitVec 64) (R1 R2 : SepProp) :
    (vecHeader b c1 p1 l1 ∗ R1) ∗ (vecHeader (b + 0x18#64) c2 p2 l2 ∗ R2) =
      (b ↦ₛ (vecHeaderBytes c1 p1 l1 ++ vecHeaderBytes c2 p2 l2)) ∗ (R1 ∗ R2) := by
  have hl : (vecHeaderBytes c1 p1 l1).length = 24 := by simp [vecHeaderBytes, unpack64_length]
  rw [vecHeader_eq_bytes, vecHeader_eq_bytes, pointsToBytes_append, hl]
  change _ = (_ ∗ ((b + 0x18#64) ↦ₛ _)) ∗ _
  ac_rfl

private theorem dirEntry_reloc (A : RustAlloc) (e : List (BitVec 8) × List (BitVec 8)) (a : BitVec 64) :
    dirEntryAt A e a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 48 ∧ ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ dirEntryAt A e b⌝ ∗ (a ↦ₛ bs) ∗ H := by
  dsimp only [dirEntryAt, vecU8, vecU8At]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [dirEntry_body_eq]
  apply Entails.sepExists_right
    (vecHeaderBytes c1 p1 (BitVec.ofNat 64 e.1.length) ++
      vecHeaderBytes c2 p2 (BitVec.ofNat 64 e.2.length))
  apply Entails.sepExists_right
  refine Entails.pure_right ⟨by simp [vecHeaderBytes, unpack64_length], fun b => ?_⟩ (Entails.refl _)
  rw [← dirEntry_body_eq]
  exact sepConj_mono
    (Entails.sepExists_right c1 (Entails.sepExists_right p1 (Entails.refl _)))
    (Entails.sepExists_right c2 (Entails.sepExists_right p2 (Entails.refl _)))

private theorem arrayAt_dirEntry_reloc (A : RustAlloc) :
    ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (a : BitVec 64),
      arrayAt (dirEntryAt A) 48 a xs ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (a ↦ₛ bs) ∗ H
  | [], a => by
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    simp only [arrayAt, pointsToBytes_nil, List.length_nil, Nat.zero_mul, emp_sepConj]
    exact Entails.pure_right ⟨trivial, fun _ => Entails.refl emp⟩ (Entails.refl emp)
  | e :: xs, a => by
    dsimp only [arrayAt]
    refine Entails.trans (sepConj_mono (dirEntry_reloc A e a) (arrayAt_dirEntry_reloc A xs (a + 48#64))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs1
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H2
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hl1, hr1⟩
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hl2, hr2⟩
    refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
    have hlen : (bs1 ++ bs2).length = (e :: xs).length * 48 := by
      simp only [List.length_append, List.length_cons, hl1, hl2]; omega
    refine Entails.pure_right ⟨hlen, fun b => ?_⟩ ?_
    · rw [pointsToBytes_append, hl1]
      have harr : ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
          ((b ↦ₛ bs1) ∗ H1) ∗ (((b + 48#64) ↦ₛ bs2) ∗ H2) := by ac_rfl
      rw [harr]
      exact sepConj_mono (hr1 b) (hr2 (b + 48#64))
    · rw [pointsToBytes_append, hl1]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.GrowOne.Helpers
