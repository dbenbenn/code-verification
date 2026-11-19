/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public meta import ProofLib.GenDecodes
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen

public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk`: Loop Proofs

**Checked by Lean.**

Proves the inner binary-search loop (`0x6c524..0x6c548`) and single-iteration `memmove` / `grow_one`
helpers (`0x6c46c..0x6c460`) for `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`).
-/

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
namespace AddChunkNorm
@[scoped arm64_norm, scoped wp_norm] theorem ofNat_add_one_norm (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := EncoderIntoPb.ofNat_add_one j
@[local arm64_norm ↓, local wp_norm ↓] theorem sp_setPC_pre (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) : (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) : ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) : calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl
end AddChunkNorm
open AddChunkNorm

/-! ## Fetch Macro and Arithmetic / BitVector Helpers -/

theorem bv64_lsr1_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl

theorem bv64_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by rw [← BitVec.ofNat_add]

theorem bv64_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact hba

theorem bv64_lsl2_ofNat {n : Nat} (hn : 4 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega

theorem truncate32_zeroExtend64_16 (x : BitVec 16) :
    BitVec.truncate 32 (x.zeroExtend 64) = x.zeroExtend 32 := by bv_bits

theorem bv32_ult_zeroExtend16 (a b : BitVec 16) :
    (a.zeroExtend 32).ult (b.zeroExtend 32) = decide (a.toNat < b.toNat) := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

set_option linter.unusedSimpArgs false

theorem bv64_ult_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (1#64).ult (BitVec.ofNat 64 n) = decide (1 < n) := by
  rw [BitVec.ult_eq_decide, show (1#64 : BitVec 64).toNat = 1 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## Inner Binary Search Loop (`0x6c524..0x6c548`) -/

theorem insert_suffix_prepare_memmove (ptr : BitVec 64) (vec : List Pt) (insertIdx cap : Nat)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap) (hcap : cap * 4 < 2 ^ 63) :
    let x22 := ptr + BitVec.ofNat 64 (4 * insertIdx)
    let suffix := vec.drop insertIdx
    (ptSliceAt ptr vec ∗ memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap - vec.length) * 4)) ⊢
      ∃∗ slotBs : List (BitVec 8),
        ⌜slotBs.length = 4⌝ ∗ ptSliceAt ptr (vec.take insertIdx) ∗
        (x22 ↦ₛ (ptListBytes suffix ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap - (vec.length + 1)) * 4) := by
  intro x22 suffix
  have hmul : (cap - vec.length) * 4 = 4 + (cap - (vec.length + 1)) * 4 := by omega
  have hadd4 : ptr + BitVec.ofNat 64 (vec.length * 4) + 4#64 =
      ptr + BitVec.ofNat 64 ((vec.length + 1) * 4) := by
    rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 2; omega
  have hx22_add : x22 + BitVec.ofNat 64 (ptListBytes suffix).length =
      ptr + BitVec.ofNat 64 (vec.length * 4) := by
    dsimp only [x22, suffix]; rw [ptListBytes_length, List.length_drop, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [ptSliceAt_split_take_drop vec insertIdx ptr (by omega), hmul,
    memRegion_split (ptr + BitVec.ofNat 64 (vec.length * 4)) 4 ((cap - (vec.length + 1)) * 4) (by omega),
    hadd4, ProofLib.memRegion_eq_exists_bytes (ptr + BitVec.ofNat 64 (vec.length * 4)) 4 (by decide),
    ptSliceAt_eq_pointsToBytes suffix x22, ← hx22_add]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro slotBs; refine Entails.sepExists_right slotBs ?_
  rw [pointsToBytes_append]; exact Entails.of_eq (by sep_ac_rfl)

theorem ptSliceAt_reassemble_insert (ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) :
    let x22 := ptr + BitVec.ofNat 64 (4 * insertIdx)
    (ptSliceAt ptr (vec.take insertIdx) ∗ ((x22 ↦₁₆ pt.x.value) ∗ ((x22 + 2#64) ↦₁₆ pt.y.value)) ∗
      ptSliceAt (x22 + 4#64) (vec.drop insertIdx)) =
      ptSliceAt ptr (vec.take insertIdx ++ (pt :: vec.drop insertIdx)) := by
  intro x22; rw [ptSliceAt_append, List.length_take_of_le hins]; rfl

theorem reassemble_sortedSetPtOf_insert (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
      ptSliceAt ptr (vec.take insertIdx) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 vec.length + 1#64)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } := by
  let vec' := vec.take insertIdx ++ (pt :: vec.drop insertIdx)
  have hlen' : vec'.length = vec.length + 1 := by
    dsimp [vec']; rw [List.length_append, List.length_take_of_le hins, List.length_cons, List.length_drop]; omega
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 vec'.length := by
    rw [hlen', show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  have hslice := ptSliceAt_reassemble_insert ptr vec insertIdx pt hins; dsimp only at hslice
  rw [hbv_len', ← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  rw [← hslice]; exact Entails.of_eq (by sep_ac_rfl)

theorem reassemble_sortedSetPtOf_snoc (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (pt : Pt)
    (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (ptSliceAt ptr vec ∗ ((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢ sortedSetPtOf A v { vec := vec ++ [pt] } := by
  let vec' := vec ++ [pt]
  have hlen' : vec'.length = vec.length + 1 := by simp [vec']
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  rw [← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  dsimp [vec']; rw [ptSliceAt_append_singleton]; unfold ptAt; exact Entails.of_eq (by ac_rfl)

theorem reassemble_sortedSetPtOf_set (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (idx : Nat) (pt : Pt)
    (hidx : idx < vec.length) (hle : vec.length ≤ cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (ptSliceAt ptr (vec.take idx) ∗ ((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢ sortedSetPtOf A v { vec := vec.set idx pt } := by
  let vec' := vec.set idx pt
  have hlen' : vec'.length = vec.length := List.length_set
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  rw [← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  dsimp [vec']; rw [ptSliceAt_set vec idx pt ptr hidx]; unfold ptAt; exact Entails.of_eq (by ac_rfl)

theorem bv64_beq_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 1#64) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; intro heq
    have hto := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hto; exact h hto

theorem bv64_bne_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != 1#64) = decide (n ≠ 1) := by
  by_cases h : n = 1
  · subst h; rfl
  · simp only [h, not_false_eq_true, decide_true, bne_iff_ne, ne_eq]; intro heq
    have hto := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hto; exact h hto

theorem bv32_beq_zeroExtend16 (a b : BitVec 16) :
    (BitVec.zeroExtend 32 a == BitVec.zeroExtend 32 b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne, ne_eq]; intro heq; apply h
    apply BitVec.eq_of_toNat_eq; have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hto
    exact hto

theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv64_ule_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

@[expose] def sortedSetPtGrownAt (A : RustAlloc) (v : BitVec 64) (vec : List Pt) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜vec.length < cap.toNat ∧ ptr ≠ 0#64 ∧ cap.toNat * 4 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
    A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
    memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)

theorem growOnePtFull_post_entails_grown (A : RustAlloc) (v cap : BitVec 64) (vec : List Pt)
    (h1 : 1 ≤ vec.length) (hcap_eq : cap.toNat = vec.length) (hlen_le : vec.length ≤ 65536) :
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
      memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ⊢
    sortedSetPtGrownAt A v vec := by
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p'
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hp', _⟩
  unfold sortedSetPtGrownAt
  let cap' := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    dsimp [cap']
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : vec.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 4 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  apply Entails.pure_right ⟨hlt, hp', hcap'_lt⟩
  rw [← ptSliceAt_eq_pointsToBytes, ptListBytes_length, Nat.mul_comm 4 vec.length, ← hcap'_toNat,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap_eq]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_growOne4k (sp : BitVec 64) :
    stackAt sp growOneStack = stackAt (sp - 64#64) finishGrowStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (by decide)

private theorem grow_new_cap_eq4k {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2 : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hsh : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  by_cases hlt : 4 < 2 * cap.toNat
  · have hult : (4#64).ult (cap <<< 1) = true := by rw [BitVec.ult_eq_decide, decide_eq_true_iff, h2]; exact hlt
    rw [hult]; simp only [↓reduceIte, hsh, (by omega : max (2 * cap.toNat) 4 = 2 * cap.toNat)]
  · have hult : (4#64).ult (cap <<< 1) = false := by rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, h2]; exact hlt
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte, (by omega : max (2 * cap.toNat) 4 = 4)]

end CryptoVerification.SpqrV1.Poly.AddChunk
