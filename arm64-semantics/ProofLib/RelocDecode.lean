/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.PlacedHelpers
public import ProofLib.Invariant
public import ProofLib.LiteralFetchLint
public import ProofLib.BV.ReflectROBDD
public import ProofLib.SepLogic.CodeLookup
public import ProofLib.ProgramReflection.IdxTree
import ProofLib.Hoare.Model

/-!
# Layout-Generic Relocation Decoding

Proves page and low-12-bit cancellation identities, symbolic instruction decoders for AArch64
relocation word patchers against `Arm64.decode`, fetch rules for `Program.hasWords`, and linker
range-extension veneers.
-/

@[expose] public section

namespace Arm64
namespace Obj

set_option linter.literalFetch false

/-! ## Branch Relocation Word Patching (`patchCalls`) -/

def patchCalls (calls : List (Nat × String)) (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) : List (BitVec 32) :=
  words.mapIdx fun j w =>
    match calls.find? (·.1 == 4 * j) with
    | some (_, sym) => branchWord w (a + BitVec.ofNat 64 (4 * j)) (resolve sym)
    | none => w

theorem branchWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : BranchInRange place target) :
    ((branchWord w place target).extractLsb' 0 26).signExtend 64 <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold branchWord
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x8000000#64 < 0x10000000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

theorem branchWord_mask {w : BitVec 32} {place target : BitVec 64} :
    branchWord w place target &&& 0xfc000000#32 = w &&& 0xfc000000#32 := by
  unfold branchWord
  generalize (target - place) >>> 2 = d
  bv_bits

set_option linter.deprecated false in
theorem decode_branch {v : BitVec 32} {off : BitVec 64}
    (hv : v &&& 0x7c000000#32 = 0x14000000#32)
    (himm : (v.extractLsb' 0 26).signExtend 64 <<< 2 = off) :
    decode v = if v.getLsbD 31 then some (.bl off)
      else some (.b off) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]), if_neg (by simp [h4]),
    if_neg (by simp [h5]), if_neg (by simp [h6]), if_neg (by simp [h7]), if_neg (by simp [h8]),
    if_neg (by simp [h9]), if_pos (by simp [h10])]
  simp only [himm]

theorem decode_branchWord_bl {w : BitVec 32} (hw : w &&& 0xfc000000#32 = 0x94000000#32)
    {place target : BitVec 64} (hr : BranchInRange place target) :
    decode (branchWord w place target) =
      some (.bl (target - place)) := by
  have himm := branchWord_imm (w := w) hr
  have hv := (branchWord_mask (w := w) (place := place) (target := target)).trans hw
  generalize branchWord w place target = v at himm hv ⊢
  have hc : v &&& 0x7c000000#32 = 0x14000000#32 := by bv_bits
  have h11 : v.getLsbD 31 = true := by bv_bits
  rw [decode_branch hc himm, h11]; rfl

theorem decode_branchWord_b {w : BitVec 32} (hw : w &&& 0xfc000000#32 = 0x14000000#32)
    {place target : BitVec 64} (hr : BranchInRange place target) :
    decode (branchWord w place target) =
      some (.b (target - place)) := by
  have himm := branchWord_imm (w := w) hr
  have hv := (branchWord_mask (w := w) (place := place) (target := target)).trans hw
  generalize branchWord w place target = v at himm hv ⊢
  have hc : v &&& 0x7c000000#32 = 0x14000000#32 := by bv_bits
  have h11 : v.getLsbD 31 = false := by bv_bits
  rw [decode_branch hc himm, h11]; rfl

theorem fetch_patchCalls_bl {prog : Program} {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} {r : Nat × String}
    (h : prog.hasWords a (patchCalls calls words a resolve))
    (hr : calls.find? (·.1 == r.1) = some r) (h4 : r.1 % 4 = 0)
    (hlen : r.1 / 4 < words.length)
    (hw : words[r.1 / 4] &&& 0xfc000000#32 = 0x94000000#32)
    (hrange : BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2)) :
    prog.fetch (a + BitVec.ofNat 64 r.1) =
      some (.bl (resolve r.2 - (a + BitVec.ofNat 64 r.1))) := by
  have hj : r.1 = 4 * (r.1 / 4) := by omega
  have hlen' : r.1 / 4 < (patchCalls calls words a resolve).length := by
    simp [patchCalls, hlen]
  have hf := Program.fetch_of_hasWords h (r.1 / 4) hlen'
  rw [← hj] at hf
  rw [hf]
  have hget : (patchCalls calls words a resolve)[r.1 / 4] =
      branchWord words[r.1 / 4] (a + BitVec.ofNat 64 r.1) (resolve r.2) := by
    simp only [patchCalls, List.getElem_mapIdx]
    rw [← hj, hr]
  rw [hget]
  exact decode_branchWord_bl hw hrange

/-- A call-free word slice `(words.drop k).take n` of a linker-patched function is held unpatched
    at `a + 4 * k`. -/
theorem hasWords_patchCalls_slice {prog : Program} {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} (k n : Nat)
    (h : prog.hasWords a (patchCalls calls words a resolve))
    (hn : 0 < n) (hkn : k + n ≤ words.length)
    (hfree : ∀ j < n, calls.find? (·.1 == 4 * (k + j)) = none) :
    prog.hasWords (a + BitVec.ofNat 64 (4 * k)) ((words.drop k).take n) := by
  obtain ⟨hb, hr, hs, ho⟩ := h
  have hlen : (patchCalls calls words a resolve).length = words.length := List.length_mapIdx
  have hsl : ((words.drop k).take n).length = n := by simp; omega
  rw [hlen] at hb hs ho
  have hoff : (a + BitVec.ofNat 64 (4 * k) - prog.base).toNat = (a - prog.base).toNat + 4 * k := by
    rw [show a + BitVec.ofNat 64 (4 * k) - prog.base = (a - prog.base) + BitVec.ofNat 64 (4 * k)
      by bv_bits, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold Program.hasWords Program.hasWordsOff Program.hookFree
  simp only [hoff, hsl]
  refine ⟨by omega, fun i hi => ?_, ?_, ?_⟩
  · have hi' : k + i < (patchCalls calls words a resolve).length := by omega
    rw [show (a - prog.base).toNat + 4 * k + 4 * i = (a - prog.base).toNat + 4 * (k + i) by omega,
      hr (k + i) hi']
    simp [patchCalls, hfree i (by omega)]
  all_goals
    rw [List.all_eq_true] at hs ho ⊢
    rintro ⟨nm, o⟩ hx
    first | have := hs _ hx | have := ho _ hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at this ⊢
    exact this.imp_left fun _ => by omega

theorem disp_sub_eq (base : BitVec 64) (off k t : Nat) :
    (base + BitVec.ofNat 64 t) - (base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 t - BitVec.ofNat 64 (off + k) := by
  have h1 : BitVec.ofNat 64 (off + k) = BitVec.ofNat 64 off + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [h1]
  bv_bits

theorem branchInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : branchInRange (off + roff) t = true) :
    BranchInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) := by
  unfold branchInRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold BranchInRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem readWordOff_patchBranchBytes {prog : Program} {bs : List (BitVec 8)}
    {base : BitVec 64} {off j t : Nat} {w w' : BitVec 32}
    (hal : off % 4 = 0)
    (htake : (prog.code.drop (off + 4 * j)).take 4 =
      patchBranchBytes ((bs.drop (4 * j)).take 4) (off + 4 * j) t)
    (hread : ({ code := bs } : Program).readWordOff (4 * j) = some w')
    (hmask : (w' &&& 0xfc000000#32) = (w &&& 0xfc000000#32)) :
    prog.readWordOff (off + 4 * j) =
      some (branchWord w (base + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * j))
        (base + BitVec.ofNat 64 t)) := by
  have hk1 : (off + 4 * j) % 4 = 0 := by omega
  have hk2 : (4 * j) % 4 = 0 := by omega
  simp only [Program.readWordOff, hk1, hk2, ne_eq, not_true_eq_false, ↓reduceIte] at hread ⊢
  rcases hbs : bs.drop (4 * j) with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;>
    simp [hbs] at hread
  subst hread
  rcases hprog : prog.code.drop (off + 4 * j) with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _⟩⟩⟩⟩ <;>
    simp [hbs, hprog, patchBranchBytes, bytesLE, List.range_succ, List.range_zero] at htake
  obtain ⟨rfl, rfl, rfl, rfl⟩ := htake
  simp only [Option.some.injEq]
  unfold branchWord
  rw [disp_sub_eq]
  generalize BitVec.ofNat 64 t - BitVec.ofNat 64 (off + 4 * j) = d
  revert hmask
  bv_bits

/-! ## Page and Low-12-Bit Cancellation Identities -/

/-- `ADRP` page-cancellation identity:
    `(place &&& ~0xfff) + (pageOf target - pageOf place) = pageOf target`. -/
@[simp, arm64_norm, wp_norm]
theorem adrp_pageOf_cancel (place target : BitVec 64) :
    (place &&& 0xfffffffffffff000#64) + (pageOf target - pageOf place) = pageOf target := by
  change pageOf place + (pageOf target - pageOf place) = pageOf target
  bv_lin

/-- Variant of `adrp_pageOf_cancel` with `pageOf place` on the left. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_sub_cancel (place target : BitVec 64) :
    pageOf place + (pageOf target - pageOf place) = pageOf target := by
  bv_lin

/-- Page and `:lo12:` reconstruction identity: `pageOf target + lo12Of target = target`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_lo12Of (target : BitVec 64) :
    pageOf target + lo12Of target = target := by
  unfold pageOf lo12Of
  bv_bits

/-- Reassociated page + index + `:lo12:` reconstruction identity:
    `(pageOf target + idx) + lo12Of target = target + idx`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_idx_add_lo12Of (target idx : BitVec 64) :
    (pageOf target + idx) + lo12Of target = target + idx := by
  rw [show (pageOf target + idx) + lo12Of target = (pageOf target + lo12Of target) + idx by bv_lin]
  rw [pageOf_add_lo12Of]

/-- Reassociated page + `:lo12:` + index identity:
    `pageOf target + (lo12Of target + idx) = target + idx`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_lo12Of_add_idx (target idx : BitVec 64) :
    pageOf target + (lo12Of target + idx) = target + idx := by
  rw [← BitVec.add_assoc, pageOf_add_lo12Of]

@[simp]
theorem lo12Of_zero : lo12Of 0#64 = 0#64 := rfl

@[simp]
theorem pageOf_zero : pageOf 0#64 = 0#64 := rfl

theorem pageOf_and_fff (x : BitVec 64) : pageOf x &&& 0xfff#64 = 0#64 := by
  unfold pageOf
  bv_slice

theorem pageOf_base_add {base off : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + off) = base + pageOf off := by
  unfold pageOf
  bv_bits

theorem lo12Of_base_add {base off : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    lo12Of (base + off) = lo12Of off := by
  unfold lo12Of
  bv_bits

theorem pageOf_diff_base_add {base place target : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + target) - pageOf (base + place) = pageOf target - pageOf place := by
  rw [pageOf_base_add hb, pageOf_base_add hb]
  bv_lin

theorem pageOf_diff_base_add3 {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + BitVec.ofNat 64 t) -
      pageOf (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) =
    pageOf (BitVec.ofNat 64 t) - pageOf (BitVec.ofNat 64 (off + roff)) := by
  have h1 : base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff =
      base + BitVec.ofNat 64 (off + roff) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h1, pageOf_diff_base_add hb]

/-! ## Symbolic Decoders for Relocation Word Patchers -/

theorem adrpWordOff_extract (w : BitVec 32) (d : BitVec 64) :
    ((adrpWordOff w d).extractLsb' 5 19) ++ ((adrpWordOff w d).extractLsb' 29 2) =
      d.extractLsb' 12 21 := by
  unfold adrpWordOff
  bv_slice

theorem adrpWordOff_mask (w : BitVec 32) (d : BitVec 64) :
    adrpWordOff w d &&& 0x9f00001f#32 = w &&& 0x9f00001f#32 := by
  unfold adrpWordOff
  bv_slice

theorem adrp_mask_preserve {v w : BitVec 32} (hmask : v &&& 0x9f00001f#32 = w &&& 0x9f00001f#32) :
    v &&& 0x9f000000#32 = w &&& 0x9f000000#32 ∧ v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem pageOf_sub_and_fff (place target : BitVec 64) :
    (pageOf target - pageOf place) &&& 0xfff#64 = 0#64 := by
  have ht : (pageOf target).toNat % 4096 = 0 := by
    have h := congrArg BitVec.toNat (pageOf_and_fff target)
    rwa [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h
  have hp : (pageOf place).toNat % 4096 = 0 := by
    have h := congrArg BitVec.toNat (pageOf_and_fff place)
    rwa [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem signExtend_extractLsb_12_21 {d : BitVec 64}
    (hal : d &&& 0xfff#64 = 0#64)
    (hlt : d + 0x100000000#64 < 0x200000000#64) :
    ((d.extractLsb' 12 21).signExtend 64) <<< 12 = d := by
  bv_bits

theorem adrpWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : AdrpInRange place target) :
    ((((adrpWord w place target).extractLsb' 5 19) ++
      ((adrpWord w place target).extractLsb' 29 2)).signExtend 64) <<< 12 =
      pageOf target - pageOf place := by
  obtain ⟨hfit1, hfit2⟩ := hr
  have hal := pageOf_sub_and_fff place target
  unfold adrpWord
  rw [adrpWordOff_extract]
  apply signExtend_extractLsb_12_21 hal
  generalize pageOf target - pageOf place = d at hfit1 hfit2 ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
  rw [BitVec.lt_def, BitVec.toNat_add]
  have := d.isLt
  simp only [BitVec.toNat_ofNat]
  split at hfit1 <;> omega

set_option linter.deprecated false in
theorem decode_adr_or_adrp {v : BitVec 32}
    (hv : v &&& 0x1f000000#32 = 0x10000000#32) :
    decode v =
      let page := v.getLsbD 31
      let imm21 := (v.extractLsb' 5 19) ++ (v.extractLsb' 29 2)
      let offset := if page then (imm21.signExtend 64) <<< 12 else imm21.signExtend 64
      let rd := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.adr page rd offset) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_pos (by simp [h4])]

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_PG_HI21`. -/
theorem decode_adrpWord {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    {place target : BitVec 64} (hr : AdrpInRange place target) :
    decode (adrpWord w place target) =
      some (.adr true (Reg.fromZRBits (w.extractLsb' 0 5)) (pageOf target - pageOf place)) := by
  have himm := adrpWord_imm (w := w) hr
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))
  have hv9 : adrpWord w place target &&& 0x9f000000#32 = 0x90000000#32 := hm.trans hw
  have hv1 : adrpWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrpWord w place target).getLsbD 31 = true := by bv_bits
  change (adrpWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_pos rfl, himm, hrd]

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_PG_HI21_NC` (unchecked range variant). -/
theorem decode_adrpWord_nc {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (place target : BitVec 64) :
    decode (adrpWord w place target) =
      some (.adr true (Reg.fromZRBits (w.extractLsb' 0 5))
        ((((pageOf target - pageOf place).extractLsb' 12 21).signExtend 64) <<< 12)) := by
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))
  have hv9 : adrpWord w place target &&& 0x9f000000#32 = 0x90000000#32 := hm.trans hw
  have hv1 : adrpWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrpWord w place target).getLsbD 31 = true := by bv_bits
  change (adrpWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_pos rfl, hrd]
  unfold adrpWord
  rw [adrpWordOff_extract]

theorem adrWordOff_extract (w : BitVec 32) (d : BitVec 64) :
    ((adrWordOff w d).extractLsb' 5 19) ++ ((adrWordOff w d).extractLsb' 29 2) =
      d.extractLsb' 0 21 := by
  unfold adrWordOff
  bv_slice

theorem adrWordOff_mask (w : BitVec 32) (d : BitVec 64) :
    adrWordOff w d &&& 0x9f00001f#32 = w &&& 0x9f00001f#32 := by
  unfold adrWordOff
  bv_slice

theorem signExtend_extractLsb_0_21 {d : BitVec 64}
    (hlt : d + 0x100000#64 < 0x200000#64) :
    (d.extractLsb' 0 21).signExtend 64 = d := by
  bv_bits

theorem adrWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : AdrInRange place target) :
    (((adrWord w place target).extractLsb' 5 19) ++
      ((adrWord w place target).extractLsb' 29 2)).signExtend 64 =
      target - place := by
  obtain ⟨hfit1, hfit2⟩ := hr
  unfold adrWord
  rw [adrWordOff_extract]
  apply signExtend_extractLsb_0_21
  generalize target - place = d at hfit1 hfit2 ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
  rw [BitVec.lt_def, BitVec.toNat_add]
  have := d.isLt
  simp only [BitVec.toNat_ofNat]
  split at hfit1 <;> omega

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_LO21`. -/
theorem decode_adrWord {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x10000000#32)
    {place target : BitVec 64} (hr : AdrInRange place target) :
    decode (adrWord w place target) =
      some (.adr false (Reg.fromZRBits (w.extractLsb' 0 5)) (target - place)) := by
  have himm := adrWord_imm (w := w) hr
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrWordOff_mask w (target - place))
  have hv9 : adrWord w place target &&& 0x9f000000#32 = 0x10000000#32 := hm.trans hw
  have hv1 : adrWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrWord w place target).getLsbD 31 = false := by bv_bits
  change (adrWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_neg Bool.false_ne_true, himm, hrd]

/-! ### `:lo12:` Immediate Relocations -/

theorem lo12Word_mask {scale : Nat} (w : BitVec 32) (target : BitVec 64) :
    lo12Word scale w target &&& 0xffc003ff#32 = w &&& 0xffc003ff#32 := by
  unfold lo12Word
  generalize (target &&& 0xfff#64) >>> scale = d
  bv_slice

theorem lo12_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xffc003ff#32 = w &&& 0xffc003ff#32) :
    v &&& 0xffc00000#32 = w &&& 0xffc00000#32 ∧
    v &&& 0x3f000000#32 = w &&& 0x3f000000#32 ∧
    v.extractLsb' 30 2 = w.extractLsb' 30 2 ∧
    v.extractLsb' 22 2 = w.extractLsb' 22 2 ∧
    v.extractLsb' 5 5 = w.extractLsb' 5 5 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem lo12Word_extract {scale : Nat} (w : BitVec 32) (target : BitVec 64) :
    (lo12Word scale w target).extractLsb' 10 12 =
      ((target &&& 0xfff#64) >>> scale).extractLsb' 0 12 := by
  unfold lo12Word
  generalize (target &&& 0xfff#64) >>> scale = d
  bv_slice

theorem lo12Word0_imm (w : BitVec 32) (target : BitVec 64) :
    ((lo12Word 0 w target).extractLsb' 10 12).zeroExtend 64 = lo12Of target := by
  rw [lo12Word_extract]
  unfold lo12Of
  bv_slice

theorem lo12Word0_imm12 (w : BitVec 32) (target : BitVec 64) :
    (lo12Word 0 w target).extractLsb' 10 12 = (lo12Of target).truncate 12 := by
  rw [lo12Word_extract]
  unfold lo12Of
  bv_slice

@[simp, arm64_norm, wp_norm]
theorem zeroExtend_truncate_lo12Of (target : BitVec 64) :
    ((lo12Of target).truncate 12).zeroExtend 64 = lo12Of target := by
  unfold lo12Of
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem setWidth_truncate_lo12Of (target : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 12 (lo12Of target)) = lo12Of target := by
  unfold lo12Of
  bv_bits

theorem lo12Word1_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 1 target) :
    (((lo12Word 1 w target).extractLsb' 10 12).zeroExtend 64) <<< 1 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 1).extractLsb' 0 12).zeroExtend 64) <<< 1 = target &&& 0xfff#64
  have h0 : target &&& 1#64 = 0#64 := hal
  bv_bits

theorem lo12Word2_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 2 target) :
    (((lo12Word 2 w target).extractLsb' 10 12).zeroExtend 64) <<< 2 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 2).extractLsb' 0 12).zeroExtend 64) <<< 2 = target &&& 0xfff#64
  have h0 : target &&& 3#64 = 0#64 := hal
  bv_bits

theorem lo12Word3_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 3 target) :
    (((lo12Word 3 w target).extractLsb' 10 12).zeroExtend 64) <<< 3 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 3).extractLsb' 0 12).zeroExtend 64) <<< 3 = target &&& 0xfff#64
  have h0 : target &&& 7#64 = 0#64 := hal
  bv_bits

theorem lo12Word4_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 4 target) :
    (((lo12Word 4 w target).extractLsb' 10 12).zeroExtend 64) <<< 4 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 4).extractLsb' 0 12).zeroExtend 64) <<< 4 = target &&& 0xfff#64
  have h0 : target &&& 15#64 = 0#64 := hal
  bv_bits

theorem lo12Word_imm {scale : Nat} (hscale : scale ≤ 4) (w : BitVec 32) (target : BitVec 64)
    (hal : Lo12Aligned scale target) :
    (((lo12Word scale w target).extractLsb' 10 12).zeroExtend 64) <<< scale = lo12Of target := by
  match scale with
  | 0 => simpa using lo12Word0_imm w target
  | 1 => exact lo12Word1_imm w target hal
  | 2 => exact lo12Word2_imm w target hal
  | 3 => exact lo12Word3_imm w target hal
  | 4 => exact lo12Word4_imm w target hal
  | n + 5 => omega

set_option linter.deprecated false in
theorem decode_addLo12 {v : BitVec 32}
    (hv : v &&& 0xffc00000#32 = 0x91000000#32) :
    decode v = some (.addSubImm .W64 .ADD
      (Reg.fromSPBits (v.extractLsb' 0 5))
      (Reg.fromSPBits (v.extractLsb' 5 5))
      (v.extractLsb' 10 12) false) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  have h30 : v.getLsbD 30 = false := by bv_bits
  have h29 : v.getLsbD 29 = false := by bv_bits
  have h22 : v.getLsbD 22 = false := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_pos (by simp [h5])]
  dsimp only
  rw [hsf, h30, h29, h22]
  rfl

/-- Symbolic decoder for `R_AARCH64_ADD_ABS_LO12_NC`. -/
theorem decode_addLo12Word {w : BitVec 32} (hw : w &&& 0xffc00000#32 = 0x91000000#32)
    (target : BitVec 64) :
    decode (lo12Word 0 w target) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5))
        ((lo12Of target).truncate 12) false) := by
  have himm := lo12Word0_imm12 w target
  have ⟨hm1, _, _, _, hrn, hrd⟩ := lo12_mask_preserve (lo12Word_mask (scale := 0) w target)
  have hv : lo12Word 0 w target &&& 0xffc00000#32 = 0x91000000#32 := hm1.trans hw
  rw [decode_addLo12 hv, himm, hrd, hrn]

set_option linter.deprecated false in
theorem decode_ldstGprUnsigned {v : BitVec 32}
    (hv1 : v &&& 0x3f000000#32 = 0x39000000#32)
    (hv2 : (v &&& 0xffc00000#32 == 0xf9800000#32) = false) :
    decode v =
      let sizeBits := (v.extractLsb' 30 2).toNat
      let opc := (v.extractLsb' 22 2).toNat
      let imm12 : BitVec 12 := v.extractLsb' 10 12
      let offset : BitVec 64 := (imm12.zeroExtend 64) <<< sizeBits
      let rn := Reg.fromSPBits (v.extractLsb' 5 5)
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      mkLoadStoreInst sizeBits opc rt (.Offset rn offset) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [hv2]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_pos (by simp [h30])]

/-- Symbolic decoder for all GPR unsigned-immediate `:lo12:` load/store relocations
    (`R_AARCH64_LDST{8,16,32,64}_ABS_LO12_NC`, covering `LDRB`, `STRB`, `LDRSB`, `LDRH`, `STRH`,
    `LDRSH`, `LDR` 32/64, `STR` 32/64, `LDRSW`). -/
theorem decode_ldstGprLo12Word {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hal : Lo12Aligned scale target) :
    decode (lo12Word scale w target) =
      mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
        (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)) := by
  have hle : scale ≤ 4 := by
    subst hscale
    have := (w.extractLsb' 30 2).isLt
    omega
  have himm := lo12Word_imm hle w target hal
  have ⟨hm1, hm2, hsz, hopc, hrn, hrt⟩ :=
    lo12_mask_preserve (lo12Word_mask (scale := scale) w target)
  have hv1 : lo12Word scale w target &&& 0x3f000000#32 = 0x39000000#32 := hm2.trans hw1
  have hv2 : (lo12Word scale w target &&& 0xffc00000#32 == 0xf9800000#32) = false := by
    rw [hm1]; exact hw2
  rw [decode_ldstGprUnsigned hv1 hv2]
  dsimp only
  rw [hsz, hscale, hopc, hrn, hrt, himm]

set_option linter.deprecated false in
theorem decode_ldstSimdUnsigned {v : BitVec 32}
    (hv1 : v &&& 0x3f000000#32 = 0x3d000000#32) :
    decode v =
      (let sizeBits := (v.extractLsb' 30 2).toNat
       let opc := (v.extractLsb' 22 2).toNat
       match decodeSimdLoadStoreType sizeBits opc with
       | some (isLoad, sz, scale) =>
         let imm12 : BitVec 12 := v.extractLsb' 10 12
         let offset : BitVec 64 := (imm12.zeroExtend 64) <<< scale
         let rn := Reg.fromSPBits (v.extractLsb' 5 5)
         let vt : BitVec 5 := v.extractLsb' 0 5
         let addr := AddrMode.Offset rn offset
         if isLoad then some (.ldrSimd sz vt addr)
         else some (.strSimd sz vt addr)
       | none => none) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h25b : (v &&& 0xffc00000#32 == 0xf9800000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = false := by bv_bits
  have h31 : (v &&& 0x3f000000#32 == 0x38000000#32) = false := by bv_bits
  have h32 : (v &&& 0x3f000000#32 == 0x18000000#32) = false := by bv_bits
  have h33 : (v &&& 0x3f000000#32 == 0x1c000000#32) = false := by bv_bits
  have h34 : (v &&& 0x3fbffc00#32 == 0x089ffc00#32) = false := by bv_bits
  have h35 : (v &&& 0x3fff7c00#32 == 0x085f7c00#32) = false := by bv_bits
  have h36 : (v &&& 0x3fe07c00#32 == 0x08007c00#32) = false := by bv_bits
  have h37 : (v &&& 0xbfff0000#32 == 0x887f0000#32) = false := by bv_bits
  have h38 : (v &&& 0xbfe00000#32 == 0x88200000#32) = false := by bv_bits
  have h39 : (v &&& 0x3fa07c00#32 == 0x08a07c00#32) = false := by bv_bits
  have h40 : (v &&& 0xbfa07c00#32 == 0x08207c00#32) = false := by bv_bits
  have h41 : (v &&& 0xffd00000#32 == 0xd5100000#32) = false := by bv_bits
  have h42 : (v &&& 0xfffff01f#32 == 0xd503301f#32) = false := by bv_bits
  have h43 : (v &&& 0x3f800000#32 == 0x2c000000#32) = false := by bv_bits
  have h44 : (v &&& 0x3e000000#32 == 0x2c000000#32) = false := by bv_bits
  have h45 : (v &&& 0x3f000000#32 == 0x3d000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [h25b]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_neg (by simp [h30]), if_neg (by simp [h31]),
    if_neg (by simp [h32]), if_neg (by simp [h33]), if_neg (by simp [h34]),
    if_neg (by simp [h35]), if_neg (by simp [h36]), if_neg (by simp [h37]),
    if_neg (by simp [h38]), if_neg (by simp [h39]), if_neg (by simp [h40]),
    if_neg (by simp [h41]), if_neg (by simp [h42]), if_neg (by simp [h43]),
    if_neg (by simp [h44]), if_pos (by simp [h45])]
  rfl

/-- Symbolic decoder for all SIMD/FP unsigned-immediate `:lo12:` load/store relocations
    (`R_AARCH64_LDST{8,16,32,64,128}_ABS_LO12_NC`, covering `LDR`/`STR` `Bt`/`Ht`/`St`/`Dt`/`Qt`). -/
theorem decode_ldstSimdLo12Word {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {isLoad : Bool} {sz : SimdMemSize}
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (isLoad, sz, scale))
    (hw1 : w &&& 0x3f000000#32 = 0x3d000000#32)
    (hal : Lo12Aligned scale target) :
    decode (lo12Word scale w target) =
      let addr := AddrMode.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)
      if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
      else some (.strSimd sz (w.extractLsb' 0 5) addr) := by
  have hle : scale ≤ 4 := by
    revert htype
    generalize (w.extractLsb' 30 2).toNat = s
    generalize (w.extractLsb' 22 2).toNat = o
    unfold decodeSimdLoadStoreType
    split <;> intro h <;> cases h <;> omega
  have himm := lo12Word_imm hle w target hal
  have ⟨_, hm2, hsz, hopc, hrn, hrt⟩ :=
    lo12_mask_preserve (lo12Word_mask (scale := scale) w target)
  have hv1 : lo12Word scale w target &&& 0x3f000000#32 = 0x3d000000#32 := hm2.trans hw1
  rw [decode_ldstSimdUnsigned hv1]
  dsimp only
  rw [hsz, hopc, htype]
  dsimp only
  rw [hrn, hrt, himm]

/-! ### 19-Bit and 14-Bit PC-Relative Relocations -/

theorem imm19WordOff_extract (w : BitVec 32) (d : BitVec 64) :
    (imm19WordOff w d).extractLsb' 5 19 = (d >>> 2).extractLsb' 0 19 := by
  unfold imm19WordOff
  bv_slice

theorem imm19WordOff_mask (w : BitVec 32) (d : BitVec 64) :
    imm19WordOff w d &&& 0xff00001f#32 = w &&& 0xff00001f#32 := by
  unfold imm19WordOff
  bv_slice

theorem imm19_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xff00001f#32 = w &&& 0xff00001f#32) :
    v &&& 0xff000010#32 = w &&& 0xff000010#32 ∧
    v &&& 0x7e000000#32 = w &&& 0x7e000000#32 ∧
    v &&& 0x3f000000#32 = w &&& 0x3f000000#32 ∧
    v.getLsbD 31 = w.getLsbD 31 ∧
    v.getLsbD 24 = w.getLsbD 24 ∧
    v.extractLsb' 30 2 = w.extractLsb' 30 2 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 ∧
    v.extractLsb' 0 4 = w.extractLsb' 0 4 := by
  bv_slice

theorem imm19Word_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : Imm19InRange place target) :
    (((imm19Word w place target).extractLsb' 5 19).signExtend 64) <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold imm19Word
  rw [imm19WordOff_extract]
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x100000#64 < 0x200000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

set_option linter.deprecated false in
theorem decode_bcond {v : BitVec 32} (hv : v &&& 0xff000010#32 = 0x54000000#32) :
    decode v = some (.bCond (CondCode.ofBits (v.extractLsb' 0 4))
      (((v.extractLsb' 5 19).signExtend 64) <<< 2)) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_pos (by simp [h13])]

/-- Symbolic decoder for `R_AARCH64_CONDBR19` on `B.<cond>`. -/
theorem decode_imm19Word_bcond {w : BitVec 32} (hw : w &&& 0xff000010#32 = 0x54000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      some (.bCond (CondCode.ofBits (w.extractLsb' 0 4)) (target - place)) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨hm1, _, _, _, _, _, _, hc⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0xff000010#32 = 0x54000000#32 := hm1.trans hw
  change (imm19Word w place target).extractLsb' 0 4 = w.extractLsb' 0 4 at hc
  rw [decode_bcond hv, himm, hc]

set_option linter.deprecated false in
theorem decode_cbz {v : BitVec 32} (hv : v &&& 0x7e000000#32 = 0x34000000#32) :
    decode v =
      let sf : RegWidth := if v.getLsbD 31 then .W64 else .W32
      let target : BitVec 64 := ((v.extractLsb' 5 19).signExtend 64) <<< 2
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.cbz sf (v.getLsbD 24) rt target) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_pos (by simp [h11])]
  rfl

/-- Symbolic decoder for `R_AARCH64_CONDBR19` on `CBZ`/`CBNZ`. -/
theorem decode_imm19Word_cbz {w : BitVec 32} (hw : w &&& 0x7e000000#32 = 0x34000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let disp : BitVec 64 := target - place
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.cbz sf (w.getLsbD 24) rt disp) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨_, hm2, _, h31, h24, _, hrt, _⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0x7e000000#32 = 0x34000000#32 := hm2.trans hw
  change (imm19Word w place target).getLsbD 31 = w.getLsbD 31 at h31
  change (imm19Word w place target).getLsbD 24 = w.getLsbD 24 at h24
  change (imm19Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_cbz hv]
  dsimp only
  rw [h31, h24, hrt, himm]

set_option linter.deprecated false in
theorem decode_ldrLit {v : BitVec 32} (hv : v &&& 0x3f000000#32 = 0x18000000#32) :
    decode v =
      (let opc := (v.extractLsb' 30 2).toNat
       let imm19 : BitVec 19 := v.extractLsb' 5 19
       let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
       let rtBits := v.extractLsb' 0 5
       let rt := Reg.fromZRBits rtBits
       match opc with
       | 0 => some (.ldrLit .W32 false rt offset)
       | 1 => some (.ldrLit .W64 false rt offset)
       | 2 => some (.ldrLit .W64 true rt offset)
       | _ => some (.prfmLit rtBits offset)) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h25b : (v &&& 0xffc00000#32 == 0xf9800000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = false := by bv_bits
  have h31 : (v &&& 0x3f000000#32 == 0x38000000#32) = false := by bv_bits
  have h32 : (v &&& 0x3f000000#32 == 0x18000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [h25b]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_neg (by simp [h30]), if_neg (by simp [h31]),
    if_pos (by simp [h32])]
  rfl

/-- Symbolic decoder for `R_AARCH64_LD_PREL_LO19` on `LDR`/`LDRSW` (literal). -/
theorem decode_imm19Word_ldrLit {w : BitVec 32} (hw : w &&& 0x3f000000#32 = 0x18000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      (let opc := (w.extractLsb' 30 2).toNat
       let offset : BitVec 64 := target - place
       let rtBits := w.extractLsb' 0 5
       let rt := Reg.fromZRBits rtBits
       match opc with
       | 0 => some (.ldrLit .W32 false rt offset)
       | 1 => some (.ldrLit .W64 false rt offset)
       | 2 => some (.ldrLit .W64 true rt offset)
       | _ => some (.prfmLit rtBits offset)) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨_, _, hm3, _, _, hopc, hrt, _⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0x3f000000#32 = 0x18000000#32 := hm3.trans hw
  change (imm19Word w place target).extractLsb' 30 2 = w.extractLsb' 30 2 at hopc
  change (imm19Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_ldrLit hv]
  dsimp only
  rw [hopc, hrt, himm]

theorem tstbr14WordOff_extract (w : BitVec 32) (d : BitVec 64) :
    (tstbr14WordOff w d).extractLsb' 5 14 = (d >>> 2).extractLsb' 0 14 := by
  unfold tstbr14WordOff
  bv_slice

theorem tstbr14WordOff_mask (w : BitVec 32) (d : BitVec 64) :
    tstbr14WordOff w d &&& 0xfff8001f#32 = w &&& 0xfff8001f#32 := by
  unfold tstbr14WordOff
  bv_slice

theorem tstbr14_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xfff8001f#32 = w &&& 0xfff8001f#32) :
    v &&& 0x7e000000#32 = w &&& 0x7e000000#32 ∧
    v.getLsbD 31 = w.getLsbD 31 ∧
    v.getLsbD 24 = w.getLsbD 24 ∧
    v.extractLsb' 19 5 = w.extractLsb' 19 5 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem tstbr14Word_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : TstBr14InRange place target) :
    (((tstbr14Word w place target).extractLsb' 5 14).signExtend 64) <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold tstbr14Word
  rw [tstbr14WordOff_extract]
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x8000#64 < 0x10000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

set_option linter.deprecated false in
theorem decode_tbz {v : BitVec 32} (hv : v &&& 0x7e000000#32 = 0x36000000#32) :
    decode v =
      let sf : RegWidth := if v.getLsbD 31 then .W64 else .W32
      let bitPos := (if v.getLsbD 31 then 32 else 0) + (v.extractLsb' 19 5).toNat
      let target : BitVec 64 := ((v.extractLsb' 5 14).signExtend 64) <<< 2
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.tbz sf (v.getLsbD 24) rt bitPos target) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_pos (by simp [h12])]

/-- Symbolic decoder for `R_AARCH64_TSTBR14` on `TBZ`/`TBNZ`. -/
theorem decode_tstbr14Word {w : BitVec 32} (hw : w &&& 0x7e000000#32 = 0x36000000#32)
    {place target : BitVec 64} (hr : TstBr14InRange place target) :
    decode (tstbr14Word w place target) =
      let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let bitPos := (if w.getLsbD 31 then 32 else 0) + (w.extractLsb' 19 5).toNat
      let disp : BitVec 64 := target - place
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.tbz sf (w.getLsbD 24) rt bitPos disp) := by
  have himm := tstbr14Word_imm (w := w) hr
  have ⟨hm, h31, h24, hb40, hrt⟩ := tstbr14_mask_preserve (tstbr14WordOff_mask w (target - place))
  have hv : tstbr14Word w place target &&& 0x7e000000#32 = 0x36000000#32 := hm.trans hw
  change (tstbr14Word w place target).getLsbD 31 = w.getLsbD 31 at h31
  change (tstbr14Word w place target).getLsbD 24 = w.getLsbD 24 at h24
  change (tstbr14Word w place target).extractLsb' 19 5 = w.extractLsb' 19 5 at hb40
  change (tstbr14Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_tbz hv]
  dsimp only
  rw [h31, h24, hb40, hrt, himm]

/-! ### `TLSDESC -> TLSLE` and `TLSLE` Relocation Word Decoders -/

theorem decode_moveWide64 {v : BitVec 32}
    (hv : v &&& 0x9f800000#32 = 0x92800000#32) :
    decode v =
      let opc := (v.extractLsb' 29 2).toNat
      let hw := (v.extractLsb' 21 2).toNat * 16
      let imm16 : BitVec 16 := v.extractLsb' 5 16
      let rd := Reg.fromZRBits (v.extractLsb' 0 5)
      match opc with
      | 0 => some (.moveWide .W64 .MOVN rd imm16 hw)
      | 2 => some (.moveWide .W64 .MOVZ rd imm16 hw)
      | 3 => some (.moveWide .W64 .MOVK rd imm16 hw)
      | _ => none := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  unfold decode
  simp only [h1, h2, h3, h3a, h3b, h3c, h4, h5, h6, h7, hsf, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSDESC_ADR_PAGE21` relaxed to Local-Exec (`TLSLE`):
    `tlsdescAdrPage21Word target` decodes to `movz x0, #((target >> 16) & 0xffff), lsl #16`. -/
theorem decode_tlsdescAdrPage21Word (target : BitVec 64) :
    decode (tlsdescAdrPage21Word target) =
      some (.moveWide .W64 .MOVZ .x0 (target.extractLsb' 16 16) 16) := by
  have hv : tlsdescAdrPage21Word target &&& 0x9f800000#32 = 0x92800000#32 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hopc : (tlsdescAdrPage21Word target).extractLsb' 29 2 = 2#2 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hhw : (tlsdescAdrPage21Word target).extractLsb' 21 2 = 1#2 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hrd : (tlsdescAdrPage21Word target).extractLsb' 0 5 = 0#5 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have himm : (tlsdescAdrPage21Word target).extractLsb' 5 16 = target.extractLsb' 16 16 := by
    unfold tlsdescAdrPage21Word; bv_bits
  rw [decode_moveWide64 hv]
  dsimp only
  rw [hopc, hhw, hrd, himm]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSDESC_LD64_LO12` relaxed to Local-Exec (`TLSLE`):
    `tlsdescLd64Lo12Word target` decodes to `movk x0, #(target & 0xffff)`. -/
theorem decode_tlsdescLd64Lo12Word (target : BitVec 64) :
    decode (tlsdescLd64Lo12Word target) =
      some (.moveWide .W64 .MOVK .x0 (target.extractLsb' 0 16) 0) := by
  have hv : tlsdescLd64Lo12Word target &&& 0x9f800000#32 = 0x92800000#32 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hopc : (tlsdescLd64Lo12Word target).extractLsb' 29 2 = 3#2 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hhw : (tlsdescLd64Lo12Word target).extractLsb' 21 2 = 0#2 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hrd : (tlsdescLd64Lo12Word target).extractLsb' 0 5 = 0#5 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have himm : (tlsdescLd64Lo12Word target).extractLsb' 5 16 = target.extractLsb' 0 16 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  rw [decode_moveWide64 hv]
  dsimp only
  rw [hopc, hhw, hrd, himm]
  rfl

theorem decode_addHi12 {v : BitVec 32}
    (hv : v &&& 0xffc00000#32 = 0x91400000#32) :
    decode v = some (.addSubImm .W64 .ADD
      (Reg.fromSPBits (v.extractLsb' 0 5))
      (Reg.fromSPBits (v.extractLsb' 5 5))
      (v.extractLsb' 10 12) true) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  have h30 : v.getLsbD 30 = false := by bv_bits
  have h29 : v.getLsbD 29 = false := by bv_bits
  have h22 : v.getLsbD 22 = true := by bv_bits
  unfold decode
  simp only [h1, h2, h3, h3a, h3b, h3c, h4, h5, hsf, h30, h29, h22, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSLE_ADD_TPREL_HI12`. -/
theorem decode_tprelHi12Word {w : BitVec 32} (hw : w &&& 0xffc00000#32 = 0x91400000#32)
    (target : BitVec 64) :
    decode (tprelHi12Word w target) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5))
        (target.extractLsb' 12 12) true) := by
  have hm : tprelHi12Word w target &&& 0xffc003ff#32 = w &&& 0xffc003ff#32 := by
    unfold tprelHi12Word; bv_slice
  have ⟨hm1, _, _, _, hrn, hrd⟩ := lo12_mask_preserve hm
  have hv : tprelHi12Word w target &&& 0xffc00000#32 = 0x91400000#32 := hm1.trans hw
  have himm : (tprelHi12Word w target).extractLsb' 10 12 = target.extractLsb' 12 12 := by
    unfold tprelHi12Word; bv_slice
  rw [decode_addHi12 hv, himm, hrd, hrn]

/-! ## Fetch Rules for `Program.hasWords` -/

section RelocFetchRules
set_option linter.literalFetch false

/-- Fetch rule for an `ADRP` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_adrpAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrpWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x90000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd)
    (hrange : AdrpInRange P target) :
    prog.fetch pc =
      some (.adr true rd (pageOf target - pageOf pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrpWord (beq_iff_eq.mp hw) hrange, hrd, h_P, ← h_pc]

/-- Fetch rule for an `ADD :lo12:` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_addLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {target : BitVec 64}
    {rd rn : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word 0 w target))
    (hw : (w &&& 0xffc00000#32 == 0x91000000#32) = true)
    (hrd : Reg.fromSPBits (w.extractLsb' 0 5) = rd)
    (hrn : Reg.fromSPBits (w.extractLsb' 5 5) = rn) :
    prog.fetch pc =
      some (.addSubImm .W64 .ADD rd rn ((lo12Of target).truncate 12) false) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_addLo12Word (beq_iff_eq.mp hw) target, hrd, hrn]

/-- Fetch rule for a GPR `:lo12:` load/store slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_ldstGprLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word scale w target))
    (h_scale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : (w &&& 0x3f000000#32 == 0x39000000#32) = true)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (h_inst : mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)) = some inst)
    (hal : Lo12Aligned scale target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_ldstGprLo12Word h_scale (beq_iff_eq.mp hw1) hw2 hal, h_inst]

/-- Fetch rule for a SIMD/FP `:lo12:` load/store slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_ldstSimdLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {isLoad : Bool} {sz : SimdMemSize} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word scale w target))
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (isLoad, sz, scale))
    (hw1 : (w &&& 0x3f000000#32 == 0x3d000000#32) = true)
    (h_inst : (let addr := AddrMode.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)
      if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
      else some (.strSimd sz (w.extractLsb' 0 5) addr)) = some inst)
    (hal : Lo12Aligned scale target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_ldstSimdLo12Word htype (beq_iff_eq.mp hw1) hal, h_inst]

/-- Fetch rule for an unchecked `ADRP` (`R_AARCH64_ADR_PREL_PG_HI21_NC`) slot at index `i`. -/
theorem fetch_of_hasWords_adrpNcAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrpWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x90000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd) :
    prog.fetch pc =
      some (.adr true rd (((pageOf target - pageOf pc).extractLsb' 12 21).signExtend 64 <<< 12)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrpWord_nc (beq_iff_eq.mp hw) P target, hrd, h_P, ← h_pc]

/-- Fetch rule for an `ADR` (`R_AARCH64_ADR_PREL_LO21`) slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_adrAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x10000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd)
    (hrange : AdrInRange P target) :
    prog.fetch pc =
      some (.adr false rd (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrWord (beq_iff_eq.mp hw) hrange, hrd, h_P, ← h_pc]

theorem lo12Aligned_zero (target : BitVec 64) : Lo12Aligned 0 target :=
  BitVec.and_zero

/-- Fetch rule for a `BL` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_blAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (branchWord w P target))
    (hw : (w &&& 0xfc000000#32 == 0x94000000#32) = true)
    (hrange : BranchInRange P target) :
    prog.fetch pc =
      some (.bl (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_branchWord_bl (beq_iff_eq.mp hw) hrange, h_P, ← h_pc]

/-- Fetch rule for a `B` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_bAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (branchWord w P target))
    (hw : (w &&& 0xfc000000#32 == 0x14000000#32) = true)
    (hrange : BranchInRange P target) :
    prog.fetch pc =
      some (.b (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_branchWord_b (beq_iff_eq.mp hw) hrange, h_P, ← h_pc]

/-- Fetch rule for a `B.cond` relocated slot (`R_AARCH64_CONDBR19`). -/
theorem fetch_of_hasWords_bcondAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {cc : CondCode}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0xff000010#32 == 0x54000000#32) = true)
    (hcc : CondCode.ofBits (w.extractLsb' 0 4) = cc)
    (hrange : Imm19InRange P target) :
    prog.fetch pc =
      some (.bCond cc (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_bcond (beq_iff_eq.mp hw) hrange, hcc, h_P, ← h_pc]

/-- Fetch rule for a `CBZ`/`CBNZ` relocated slot (`R_AARCH64_CONDBR19`). -/
theorem fetch_of_hasWords_cbzAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0x7e000000#32 == 0x34000000#32) = true)
    (h_inst : (let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let disp : BitVec 64 := target - pc
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.cbz sf (w.getLsbD 24) rt disp)) = some inst)
    (hrange : Imm19InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_cbz (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-- Fetch rule for an `LDR`/`LDRSW` (literal) relocated slot (`R_AARCH64_LD_PREL_LO19`). -/
theorem fetch_of_hasWords_ldrLitAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0x3f000000#32 == 0x18000000#32) = true)
    (h_inst : (let opc := (w.extractLsb' 30 2).toNat
      let offset : BitVec 64 := target - pc
      let rtBits := w.extractLsb' 0 5
      let rt := Reg.fromZRBits rtBits
      match opc with
      | 0 => some (.ldrLit .W32 false rt offset)
      | 1 => some (.ldrLit .W64 false rt offset)
      | 2 => some (.ldrLit .W64 true rt offset)
      | _ => some (.prfmLit rtBits offset)) = some inst)
    (hrange : Imm19InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_ldrLit (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-- Fetch rule for a `TBZ`/`TBNZ` relocated slot (`R_AARCH64_TSTBR14`). -/
theorem fetch_of_hasWords_tstbr14At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (tstbr14Word w P target))
    (hw : (w &&& 0x7e000000#32 == 0x36000000#32) = true)
    (h_inst : (let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let bitPos := (if w.getLsbD 31 then 32 else 0) + (w.extractLsb' 19 5).toNat
      let disp : BitVec 64 := target - pc
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.tbz sf (w.getLsbD 24) rt bitPos disp)) = some inst)
    (hrange : TstBr14InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_tstbr14Word (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-! ## Linker Veneers -/

/-- Standard 3-instruction AArch64 ADRP range-extension veneer (`__AArch64ADRPThunk_<sym>`)
    at address `vAddr` jumping to `target` via intra-procedure-call scratch register `x16`. -/
def VeneerAt (prog : Program) (vAddr target : BitVec 64) : Prop :=
  AdrpInRange vAddr target ∧
  prog.hasWords vAddr
    [ adrpWord 0x90000010#32 vAddr target
    , lo12Word 0 0x91000210#32 target
    , 0xd61f0200#32 ]

theorem fetch_veneer_0 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch vAddr =
      some (.adr true .x16 (pageOf target - pageOf vAddr)) :=
  fetch_of_hasWords_adrpAt 0 h.2 (BitVec.add_zero vAddr).symm rfl rfl rfl rfl h.1

theorem fetch_veneer_1 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch (vAddr + 4#64) =
      some (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) :=
  fetch_of_hasWords_addLo12At 1 h.2 rfl rfl rfl rfl rfl

theorem fetch_veneer_2 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch (vAddr + 8#64) = some (.br .x16) :=
  Program.fetch_of_hasWords_decodeAt 2 h.2 rfl rfl

end RelocFetchRules

/-- Executing a 3-instruction AArch64 veneer at `vAddr` reaches `target` in 3 steps, modifying
    only `X16` (to `target`) and `pc` (to `target`). -/
theorem reaches_pc_of_veneerAt {prog : Program} {vAddr target : BitVec 64} {s0 : State}
    (h : VeneerAt prog vAddr target)
    (hpc : s0.pc = vAddr) (hrun : s0.status = .Running) :
    reaches_pc prog target s0
      (fun sm => sm = (s0.writeReg64 (.gpr 16#5) target).setPC target) := by
  have hs1 : execInst (.adr true .x16 (pageOf target - pageOf vAddr)) s0 =
      (s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64) := by
    cases s0
    subst hpc
    dsimp [execInst, execInstWithSvc, Reg.x16, State.writeReg, State.writeReg64,
      State.advancePC, State.setPC]
    rw [adrp_pageOf_cancel]
  have hs2 : execInst (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false)
      ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)) =
      (s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64) := by
    have hawc (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
      simp only [AddWithCarry64, Bool.false_eq_true, ↓reduceIte]
      bv_bits
    cases s0
    dsimp [execInst, execInstWithSvc, execAddSubImm, Reg.x16, evalAddSub, State.readReg,
      State.readReg64, State.writeReg, State.writeReg64, State.advancePC, State.setPC,
      RegFile.read, RegFile.write]
    congr 1
    · congr 1
      funext i
      by_cases hi : i = 16#5 <;>
        simp [hi, hawc, zeroExtend_truncate_lo12Of, pageOf_add_lo12Of]
    · bv_lin
  have hs3 : execInst (.br .x16)
      ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)) =
      (s0.writeReg64 (.gpr 16#5) target).setPC target := by
    cases s0; rfl
  have hf0 : prog.fetch s0.pc =
      some (.adr true .x16 (pageOf target - pageOf vAddr)) := by
    rw [hpc]; exact fetch_veneer_0 h
  have hrun1 : ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).status = .Running := by
    cases s0; exact hrun
  have hf1 : prog.fetch ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).pc =
      some (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) := by
    have hpc1 : ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).pc = vAddr + 4#64 := by
      cases s0; rfl
    rw [hpc1]; exact fetch_veneer_1 h
  have hrun2 : ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).status = .Running := by
    cases s0; exact hrun
  have hf2 : prog.fetch ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).pc =
      some (.br .x16) := by
    have hpc2 : ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).pc = vAddr + 8#64 := by
      cases s0; rfl
    rw [hpc2]; exact fetch_veneer_2 h
  have hrun3 : ((s0.writeReg64 (.gpr 16#5) target).setPC target).status = .Running := by
    cases s0; exact hrun
  have hpc3 : ((s0.writeReg64 (.gpr 16#5) target).setPC target).pc = target := by
    cases s0; rfl
  apply reaches_pc_step hrun hf0
  change reaches_pc prog target
    (execInst (.adr true .x16 (pageOf target - pageOf vAddr)) s0) _ _
  rw [hs1]
  apply reaches_pc_step hrun1 hf1
  change reaches_pc prog target
    (execInst (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) _) _ _
  rw [hs2]
  apply reaches_pc_step hrun2 hf2
  change reaches_pc prog target (execInst (.br .x16) _) _ _
  rw [hs3]
  exact reaches_pc_refl hpc3 hrun3 rfl

/-- Any `subroutine_ok` contract at `target` whose precondition and postconditions do not depend on
    `X16` or entry `pc` transfers across a range-extension veneer `VeneerAt prog vAddr target`. -/
theorem subroutine_ok_of_veneerAt {α : Type} {prog : Program} {vAddr target : BitVec 64}
    {spec : Spec α} (h : VeneerAt prog vAddr target)
    (hok : subroutine_ok prog target spec)
    (hpre : ∀ x s, spec.pre x ((s.writeReg64 (.gpr 16#5) target).setPC target) = spec.pre x s)
    (hpost : ∀ x s sf, spec.post x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.post x s sf)
    (hpanic : ∀ x s sf, spec.onPanic x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onPanic x s sf)
    (hexit : ∀ x c s sf, spec.onExit x c ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onExit x c s sf)
    (hoom_eq : ∀ x s sf, spec.onOom x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onOom x s sf := by
      intros; rfl) :
    subroutine_ok prog vAddr spec := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hsat hsp => reaches_outcome_iff.mpr fun hcode => ?_
  let sm : State := (s0.writeReg64 (.gpr 16#5) target).setPC target
  have hreach := reaches_pc_of_veneerAt h hpc hrun hcode
  rcases hreach with ⟨s1, hsteps1, ⟨_, _, rfl⟩ | ⟨_, hoom⟩⟩
  · have hmem : sm.mem = s0.mem := by cases s0; rfl
    have hsp' : sm.sp = s0.sp := by cases s0; rfl
    have hspAl : sm.spAligned = s0.spAligned := by cases s0; rfl
    have hrun' : sm.status = .Running := by cases s0; exact hrun
    have hsat' : sm.mem ⊨ spec.pre x sm ∗ R := by rw [hmem, hpre]; exact hsat
    obtain ⟨sf, hsteps2, hout⟩ :=
      reaches_outcome_iff.mp (subroutine_ok_iff.mp hok x R sm rfl hrun' hsat' (hspAl.trans hsp)) (hmem ▸ hcode)
    refine ⟨sf, hsteps1.trans hsteps2, ?_⟩
    unfold SubroutineOutcome Returned CallingConventionPreserved CalleeSavedPreserved at hout ⊢
    have hlr : sm.readReg64 Reg.lr = s0.readReg64 Reg.lr := by cases s0; rfl
    have h19 : sm.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := by cases s0; rfl
    have h20 : sm.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := by cases s0; rfl
    have h21 : sm.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := by cases s0; rfl
    have h22 : sm.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := by cases s0; rfl
    have h23 : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := by cases s0; rfl
    have h24 : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := by cases s0; rfl
    have h25 : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := by cases s0; rfl
    have h26 : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := by cases s0; rfl
    have h27 : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := by cases s0; rfl
    have h28 : sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) := by cases s0; rfl
    have hfp : sm.readReg64 Reg.fp = s0.readReg64 Reg.fp := by cases s0; rfl
    have hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by cases s0; rfl
    have hpost' : spec.post x sm sf = spec.post x s0 sf := hpost x s0 sf
    have hpanic' : spec.onPanic x sm sf = spec.onPanic x s0 sf := hpanic x s0 sf
    have hexit' : ∀ c, spec.onExit x c sm sf = spec.onExit x c s0 sf := fun c => hexit x c s0 sf
    have hoom' : spec.onOom x sm sf = spec.onOom x s0 sf := hoom_eq x s0 sf
    simp only [hlr, hsp', h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hvregs,
      hpost', hpanic', hexit', hoom'] at hout
    exact hout
  · exact False.elim hoom

/-! ## Code and Data Relocation Linking -/

@[simp, arm64_norm, wp_norm]
theorem addSignedAddr_zero (symAddr : BitVec 64) :
    addSignedAddr symAddr 0 = symAddr := rfl

theorem CodeRelocInRange.of_find?_eq_some {relocs : List RelocEntry} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : ∀ r ∈ relocs,
      CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off) (addSignedAddr (resolve r.sym) r.addend))
    (off : Nat) {r : RelocEntry}
    (hfind : relocs.find? (·.off == off) = some r) :
    CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off) (addSignedAddr (resolve r.sym) r.addend) :=
  hrange r (List.mem_of_find?_eq_some hfind)

theorem BranchInRange.of_find?_eq_some {calls : List (Nat × String)} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : ∀ r ∈ calls, BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2))
    (off : Nat) {r : Nat × String}
    (hfind : calls.find? (·.1 == off) = some r) :
    BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2) :=
  hrange r (List.mem_of_find?_eq_some hfind)

/-- Patch a list of 32-bit template words `words` at base address `a` according to `relocs`,
    using `resolve` to map each symbol name to its 64-bit runtime address. -/
def patchRelocs (relocs : List RelocEntry) (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) : List (BitVec 32) :=
  words.zipIdx.map fun (w, j) =>
    match relocs.find? (·.off == 4 * j) with
    | some r =>
      let place := a + BitVec.ofNat 64 (4 * j)
      let target := addSignedAddr (resolve r.sym) r.addend
      patchRelocWord r.kind w place target
    | none => w

theorem lo12Aligned_to_prop {scale : Nat} (hscale : scale ≤ 4) {base : BitVec 64} {t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : lo12Aligned scale t = true) :
    Lo12Aligned scale (base + BitVec.ofNat 64 t) := by
  unfold lo12Aligned at h
  rw [beq_iff_eq] at h
  unfold Lo12Aligned
  have hmask : (base + BitVec.ofNat 64 t) &&& lo12AlignMask scale =
      BitVec.ofNat 64 t &&& lo12AlignMask scale := by
    match scale with
    | 0 => dsimp only [lo12AlignMask]; bv_bits
    | 1 => dsimp only [lo12AlignMask]; bv_bits
    | 2 => dsimp only [lo12AlignMask]; bv_bits
    | 3 => dsimp only [lo12AlignMask]; bv_bits
    | 4 => dsimp only [lo12AlignMask]; bv_bits
    | n + 5 => omega
  rw [hmask, h]

theorem adrpInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : adrpInRange (off + roff) t = true) :
    AdrpInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold adrpInRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold AdrpInRange
  rw [pageOf_diff_base_add3 hb]
  exact h

theorem imm19InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : imm19InRange (off + roff) t = true) :
    Imm19InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold imm19InRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Imm19InRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem tstbr14InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : tstbr14InRange (off + roff) t = true) :
    TstBr14InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold tstbr14InRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold TstBr14InRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem adrInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : adrInRange (off + roff) t = true) :
    AdrInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold adrInRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold AdrInRange
  rw [disp_sub_eq]
  exact h

theorem prel32InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : prel32InRange (off + roff) t = true) :
    Prel32InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold prel32InRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Prel32InRange
  rw [disp_sub_eq]
  exact h

theorem codeRelocInRange_to_prop {kind : RelocKind} {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : codeRelocInRange kind (off + roff) t = true) :
    CodeRelocInRange kind (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) := by
  cases kind with
  | call26 | jump26 => exact branchInRange_to_prop h
  | adrpHi21 | adrGotPage | tlsieAdrGottprelPage21 => exact adrpInRange_to_prop hb h
  | adrpHi21Nc | addLo12 | ldst8Lo12 => trivial
  | ldst16Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | ldst32Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | ldst64Lo12 | ld64GotLo12Nc | tlsieLd64GottprelLo12Nc => exact lo12Aligned_to_prop (by omega) hb h
  | ldst128Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | condbr19 | ldPrelLo19 => exact imm19InRange_to_prop h
  | tstbr14 => exact tstbr14InRange_to_prop h
  | adrPrelLo21 => exact adrInRange_to_prop h
  | prel32 => exact prel32InRange_to_prop h
  | abs64 | abs32 => contradiction
  | _ => contradiction

theorem patchRelocWord_base_add {kind : RelocKind} {w : BitVec 32}
    {base : BitVec 64} {off roff t : Nat} (hb : base &&& 0xfff#64 = 0#64)
    (hcr : codeRelocInRange kind (off + roff) t = true) :
    patchRelocWord kind w (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) =
    patchCodeRelocWord kind w (off + roff) t := by
  have hlo : (base + BitVec.ofNat 64 t) &&& 0xfff#64 = BitVec.ofNat 64 t &&& 0xfff#64 :=
    lo12Of_base_add hb
  cases kind with
  | call26 | jump26 =>
    simp only [patchRelocWord, patchCodeRelocWord, branchWord, disp_sub_eq]
  | adrpHi21 | adrpHi21Nc | adrGotPage | tlsieAdrGottprelPage21 =>
    simp only [patchRelocWord, patchCodeRelocWord, adrpWord, pageOf_diff_base_add3 hb]
  | addLo12 | ldst8Lo12 | ldst16Lo12 | ldst32Lo12 | ldst64Lo12 | ldst128Lo12
  | ld64GotLo12Nc | tlsieLd64GottprelLo12Nc =>
    simp only [patchRelocWord, patchCodeRelocWord, lo12Word, hlo]
  | condbr19 | ldPrelLo19 =>
    simp only [patchRelocWord, patchCodeRelocWord, imm19Word, disp_sub_eq]
  | tstbr14 =>
    simp only [patchRelocWord, patchCodeRelocWord, tstbr14Word, disp_sub_eq]
  | adrPrelLo21 =>
    simp only [patchRelocWord, patchCodeRelocWord, adrWord, disp_sub_eq]
  | prel32 =>
    simp only [patchRelocWord, patchCodeRelocWord, disp_sub_eq]
  | abs64 | abs32 => rfl
  | _ => contradiction

theorem addSignedAddr_eq_of_addSignedOff (base : BitVec 64) {symOff t : Nat} {addend : Int}
    (h : addSignedOff symOff addend = some t) :
    addSignedAddr (base + BitVec.ofNat 64 symOff) addend = base + BitVec.ofNat 64 t := by
  unfold addSignedOff at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  rename_i ht
  injection h with ht_eq
  subst ht_eq
  unfold addSignedAddr
  split
  · rename_i h0
    rw [beq_iff_eq] at h0
    subst h0
    simp
  · have h1 : BitVec.ofInt 64 addend =
        BitVec.ofInt 64 ((symOff : Int) + addend) - BitVec.ofNat 64 symOff := by
      rw [← BitVec.ofInt_natCast, BitVec.ofInt_add]
      bv_lin
    have h2 : BitVec.ofInt 64 ((symOff : Int) + addend) =
        BitVec.ofNat 64 ((symOff : Int) + addend).toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg ht.1]
    rw [h1, h2]
    bv_lin

theorem getD_eq_drop_getD (bs : List (BitVec 8)) (k i : Nat) :
    bs.getD (k + i) 0#8 = (bs.drop k).getD i 0#8 := by
  simp [List.getD, List.getElem?_drop]

theorem wordOfBytesLE_eq_of_readWordOff {bs : List (BitVec 8)} {k : Nat} {w : BitVec 32}
    (h : ({ code := bs } : Program).readWordOff k = some w) :
    wordOfBytesLE bs k = w := by
  unfold Program.readWordOff at h
  split at h <;> try contradiction
  unfold wordOfBytesLE
  rw [show bs.getD k 0#8 = (bs.drop k).getD 0 0#8 by simp [List.getD],
    getD_eq_drop_getD bs k 1, getD_eq_drop_getD bs k 2, getD_eq_drop_getD bs k 3]
  rcases hbs : bs.drop k with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;>
    simp only [hbs, List.getD, Option.some.injEq, reduceCtorEq] at h ⊢
  subst h
  bv_robdd

theorem readWordOff_of_take4_bytesOfWordLE {prog : Program} {k : Nat} {v : BitVec 32}
    (hk : k % 4 = 0) (htake : (prog.code.drop k).take 4 = bytesOfWordLE v) :
    prog.readWordOff k = some v := by
  simp only [Program.readWordOff, hk, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases hprog : prog.code.drop k with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _⟩⟩⟩⟩ <;>
    simp [hprog, bytesOfWordLE, bytesLE, List.range_succ, List.range_zero] at htake
  obtain ⟨rfl, rfl, rfl, rfl⟩ := htake
  simp only [Option.some.injEq]
  bv_bits

theorem base_aligned_and_fff {b : BitVec 64} (h : b.toNat % pageSize = 0) :
    b &&& 0xfff#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact h

theorem drop_take_eq_of_getD {xs ys : List (BitVec 8)} {relOff : Nat}
    (hlen : relOff + ys.length ≤ xs.length)
    (hget : ∀ i < ys.length, xs.getD (relOff + i) 0#8 = ys.getD i 0#8) :
    (xs.drop relOff).take ys.length = ys := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_drop]
    have hi := hget i h2
    have hx : xs.getD (relOff + i) 0#8 = xs[relOff + i]'(by omega) := by
      rw [List.getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hy : ys.getD i 0#8 = ys[i] := by
      rw [List.getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact hx.symm.trans (hi.trans hy)

end Obj

/-- Opcode/register bitmask preserved by `patchCodeRelocWord` and `patchRelocWord` for relocation
    `kind`. Two template words `w'` and `w` agreeing on `relocOpcodeMask kind` produce identical
    patched instruction words for any `(place, target)`. -/
def Obj.relocOpcodeMask : Obj.RelocKind → BitVec 32
  | .call26 | .jump26 => 0xfc000000#32
  | .adrpHi21 | .adrpHi21Nc | .adrPrelLo21
  | .adrGotPage | .tlsieAdrGottprelPage21 => 0x9f00001f#32
  | .addLo12 | .ldst8Lo12 | .ldst16Lo12 | .ldst32Lo12 | .ldst64Lo12 | .ldst128Lo12
  | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc
  | .tlsleAddTprelHi12 | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc
  | .tlsleLdst8TprelLo12Nc | .tlsleLdst16TprelLo12Nc | .tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc | .tlsleLdst128TprelLo12Nc => 0xffc003ff#32
  | .condbr19 | .ldPrelLo19 => 0xff00001f#32
  | .tstbr14 => 0xfff8001f#32
  | .prel32 | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall => 0#32
  | .tlsleMovwTprelG1 | .tlsleMovwTprelG0 => 0xbfe0001f#32
  | .tlsleMovwTprelG1Nc | .tlsleMovwTprelG0Nc => 0xffe0001f#32
  | .abs64 | .abs32 => 0xffffffff#32

theorem Obj.patchCodeRelocWord_eq_of_mask {kind : Obj.RelocKind} {w' w : BitVec 32}
    {placeOff targetOff : Nat}
    (hm : w' &&& Obj.relocOpcodeMask kind = w &&& Obj.relocOpcodeMask kind) :
    Obj.patchCodeRelocWord kind w' placeOff targetOff =
      Obj.patchCodeRelocWord kind w placeOff targetOff := by
  cases kind <;>
    simp only [Obj.relocOpcodeMask, Obj.patchCodeRelocWord, Obj.branchWord,
      Obj.adrpWord, Obj.adrpWordOff, Obj.adrWord, Obj.adrWordOff,
      Obj.lo12Word, Obj.imm19Word, Obj.imm19WordOff, Obj.tstbr14Word, Obj.tstbr14WordOff] at hm ⊢ <;>
    first | rfl | rw [hm] | bv_bits

end Arm64

