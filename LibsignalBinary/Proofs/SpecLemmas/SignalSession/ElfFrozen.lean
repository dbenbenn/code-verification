/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP

public section

set_option autoImplicit false

/-!
# ELF `PT_LOAD` Segment Slice Offset and Sub-Range Helpers

**Checked by Lean.** Proves `SegSlice.sub` (sub-ranges of `SegSlice` preserve permission) and
`BitVec 64` offset-difference bounds (`sub_offsets`, `toNat_sub_offsets`, `offset_in_range`).
-/

namespace CryptoVerification.SignalSession.ElfFrozen

open Arm64 Arm64.Process ProofLib CryptoVerification.SignalSession.MuslElf
  CryptoVerification.SignalSession.InitStack

/-- A sub-range `[off', off' + n)` of a `SegSlice` is a `SegSlice` with the same permission. -/
theorem SegSlice.sub {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (h : SegSlice elf a bs p) (off' n : Nat) (hn : off' + n ≤ bs.length) :
    SegSlice elf (a + BitVec.ofNat 64 off') ((bs.drop off').take n) p := by
  obtain ⟨k, hk, off, hp, rfl, hbs⟩ := h
  refine ⟨k, hk, off + off', hp, ?_, ?_⟩
  · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · have hlen : ((bs.drop off').take n).length = n := by
      rw [List.length_take, List.length_drop]; omega
    rw [hlen]
    conv => rhs; rw [← hbs]
    rw [List.drop_take, List.drop_drop, List.take_take]
    congr 1
    omega

theorem sub_offsets (b : BitVec 64) (i o : Nat) :
    (b + BitVec.ofNat 64 i) - (b + BitVec.ofNat 64 o) = BitVec.ofNat 64 i - BitVec.ofNat 64 o := by
  bv_omega

theorem toNat_sub_offsets (b : BitVec 64) (i o L : Nat) (hL : L < 2 ^ 64) (hi : i < L)
    (ho : o < L) :
    ((b + BitVec.ofNat 64 i) - (b + BitVec.ofNat 64 o)).toNat = (2 ^ 64 - o + i) % 2 ^ 64 := by
  rw [sub_offsets, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : o < 2 ^ 64)]

theorem offset_in_range (i o n L : Nat) (hL : L < 2 ^ 64) (hi : i < L) (hon : o + n ≤ L)
    (h : (2 ^ 64 - o + i) % 2 ^ 64 < n) : o ≤ i ∧ i - o < n := by
  omega

