/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import

/-!
# 2-way NEON `keccak_f1600` state and memory representation

Shared state representations and layout lemmas for 2-way NEON Keccak proofs:
- `Keccak2Vecs` / `keccak2Lane`: 2-way 128-bit NEON Keccak-f[1600] lane representation
  (`st1.getD i 0#64 ++ st0.getD i 0#64`, low 64 bits = lane 0 `st0`, high 64 bits = lane 1 `st1`).
- Balanced separation-logic layout `Keccak2Mem` (`400` bytes = `25 × 16` bytes), decomposed into
  `Keccak2Rate16Mem` (`0..256`, `B08` `squeeze2::<136>`), `Keccak2Rate17Mem` (`0..272`, `B09`
  `load_block::<136>`), and `Keccak2Cap8Mem` (`272..400`, capacity lanes `17..24`).
- Kernel-checked `.rodata` round-constant agreement `keccakRcAt_eq` (`r < 24`) and read-only
  byte-slice splitting helpers.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakRoundConstants
  keccakZeroState
  packLane64
)

/-! ## 2-way 128-bit NEON lane representation -/

/-- `Nat`-indexed 2-way 128-bit NEON Keccak lane (`st1[idx]` in bits `64..127`, `st0[idx]` in bits `0..63`). -/
@[expose] def keccak2Lane (st0 st1 : KeccakState) (idx : Nat) : BitVec 128 :=
  st1.getD idx 0#64 ++ st0.getD idx 0#64

/-- `Fin 25`-indexed 2-way 128-bit NEON Keccak state (`low 64 = st0`, `high 64 = st1`). -/
@[expose] def Keccak2Vecs (st0 st1 : KeccakState) (i : Fin 25) : BitVec 128 :=
  st1.getD i.val 0#64 ++ st0.getD i.val 0#64

theorem Keccak2Vecs_eq_lane (st0 st1 : KeccakState) (i : Fin 25) :
    Keccak2Vecs st0 st1 i = keccak2Lane st0 st1 i.val := rfl

theorem keccakZeroState_getD (idx : Nat) :
    keccakZeroState.getD idx 0#64 = 0#64 := by
  unfold keccakZeroState
  by_cases h : idx < 25
  · simp [Array.getD, h]
  · simp [Array.getD, h]

theorem keccak2Lane_zero (idx : Nat) :
    keccak2Lane keccakZeroState keccakZeroState idx = 0#128 := by
  simp only [keccak2Lane, keccakZeroState_getD]
  rfl

/-- XOR a 136-byte (`17`-lane) block into lanes `0..16` of `s` without permuting (`B09`). -/
@[expose] def keccakXorRate17 (s : KeccakState) (blk : List (BitVec 8)) : KeccakState :=
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    if idx < 17 then s.getD idx 0#64 ^^^ packLane64 blk (8 * idx)
    else s.getD idx 0#64

/-- XOR a 72-byte (`9`-lane) block into lanes `0..8` of `s` without permuting (`B00`). -/
@[expose] def keccakXorRate9 (s : KeccakState) (blk : List (BitVec 8)) : KeccakState :=
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    if idx < 9 then s.getD idx 0#64 ^^^ packLane64 blk (8 * idx)
    else s.getD idx 0#64

theorem keccakXorRate17_getD_lt (s : KeccakState) (blk : List (BitVec 8)) {idx : Nat}
    (h : idx < 17) :
    (keccakXorRate17 s blk).getD idx 0#64 = s.getD idx 0#64 ^^^ packLane64 blk (8 * idx) := by
  have h25 : idx < 25 := by omega
  simp [keccakXorRate17, Array.getD, h25, h]

theorem keccakXorRate17_getD_ge (s : KeccakState) (blk : List (BitVec 8)) {idx : Nat}
    (h17 : 17 ≤ idx) (hs : s.size ≤ 25) :
    (keccakXorRate17 s blk).getD idx 0#64 = s.getD idx 0#64 := by
  by_cases h25 : idx < 25
  · have hnot : ¬(idx < 17) := by omega
    simp [keccakXorRate17, Array.getD, h25, hnot]
  · have hnot : ¬(idx < 25) := h25
    have hnot_s : ¬(idx < s.size) := by omega
    simp [keccakXorRate17, Array.getD, hnot, hnot_s]

/-! ## Balanced separation-logic layout of `KeccakState<2, uint64x2_t>` (`400` bytes) -/

/-- Vectors `0..3` (`bytes 0..64`) of `KeccakState<2, uint64x2_t>` at `ptr`. -/
@[expose] def Keccak2Q0Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  (((ptr ↦₆₄ st0.getD 0 0#64) ∗ ((ptr + 8#64) ↦₆₄ st1.getD 0 0#64)) ∗
   (((ptr + 16#64) ↦₆₄ st0.getD 1 0#64) ∗ ((ptr + 24#64) ↦₆₄ st1.getD 1 0#64))) ∗
  ((((ptr + 32#64) ↦₆₄ st0.getD 2 0#64) ∗ ((ptr + 40#64) ↦₆₄ st1.getD 2 0#64)) ∗
   (((ptr + 48#64) ↦₆₄ st0.getD 3 0#64) ∗ ((ptr + 56#64) ↦₆₄ st1.getD 3 0#64)))

/-- Vectors `4..7` (`bytes 64..128`) of `KeccakState<2, uint64x2_t>` at `ptr`. -/
@[expose] def Keccak2Q1Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  ((((ptr + 64#64) ↦₆₄ st0.getD 4 0#64) ∗ ((ptr + 72#64) ↦₆₄ st1.getD 4 0#64)) ∗
   (((ptr + 80#64) ↦₆₄ st0.getD 5 0#64) ∗ ((ptr + 88#64) ↦₆₄ st1.getD 5 0#64))) ∗
  ((((ptr + 96#64) ↦₆₄ st0.getD 6 0#64) ∗ ((ptr + 104#64) ↦₆₄ st1.getD 6 0#64)) ∗
   (((ptr + 112#64) ↦₆₄ st0.getD 7 0#64) ∗ ((ptr + 120#64) ↦₆₄ st1.getD 7 0#64)))

/-- Vectors `8..11` (`bytes 128..192`) of `KeccakState<2, uint64x2_t>` at `ptr`. -/
@[expose] def Keccak2Q2Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  ((((ptr + 128#64) ↦₆₄ st0.getD 8 0#64) ∗ ((ptr + 136#64) ↦₆₄ st1.getD 8 0#64)) ∗
   (((ptr + 144#64) ↦₆₄ st0.getD 9 0#64) ∗ ((ptr + 152#64) ↦₆₄ st1.getD 9 0#64))) ∗
  ((((ptr + 160#64) ↦₆₄ st0.getD 10 0#64) ∗ ((ptr + 168#64) ↦₆₄ st1.getD 10 0#64)) ∗
   (((ptr + 176#64) ↦₆₄ st0.getD 11 0#64) ∗ ((ptr + 184#64) ↦₆₄ st1.getD 11 0#64)))

/-- Vectors `12..15` (`bytes 192..256`) of `KeccakState<2, uint64x2_t>` at `ptr`. -/
@[expose] def Keccak2Q3Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  ((((ptr + 192#64) ↦₆₄ st0.getD 12 0#64) ∗ ((ptr + 200#64) ↦₆₄ st1.getD 12 0#64)) ∗
   (((ptr + 208#64) ↦₆₄ st0.getD 13 0#64) ∗ ((ptr + 216#64) ↦₆₄ st1.getD 13 0#64))) ∗
  ((((ptr + 224#64) ↦₆₄ st0.getD 14 0#64) ∗ ((ptr + 232#64) ↦₆₄ st1.getD 14 0#64)) ∗
   (((ptr + 240#64) ↦₆₄ st0.getD 15 0#64) ∗ ((ptr + 248#64) ↦₆₄ st1.getD 15 0#64)))

/-- Vectors `0..15` (`bytes 0..256`) accessed by `B08` (`squeeze2::<136>`). -/
@[expose] def Keccak2Rate16Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  (Keccak2Q0Mem ptr st0 st1 ∗ Keccak2Q1Mem ptr st0 st1) ∗
  (Keccak2Q2Mem ptr st0 st1 ∗ Keccak2Q3Mem ptr st0 st1)

/-- Vector `16` (`bytes 256..272`), the 17th rate lane of `SHA3-256` / `SHAKE-256` (`rate = 136`). -/
@[expose] def Keccak2Vec16Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  ((ptr + 256#64) ↦₆₄ st0.getD 16 0#64) ∗ ((ptr + 264#64) ↦₆₄ st1.getD 16 0#64)

/-- Vectors `0..16` (`bytes 0..272`) accessed by `B09` (`load_block::<136>`). -/
@[expose] def Keccak2Rate17Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  Keccak2Rate16Mem ptr st0 st1 ∗ Keccak2Vec16Mem ptr st0 st1

/-- Capacity vectors `17..24` (`bytes 272..400`). -/
@[expose] def Keccak2Cap8Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  (((((ptr + 272#64) ↦₆₄ st0.getD 17 0#64) ∗ ((ptr + 280#64) ↦₆₄ st1.getD 17 0#64)) ∗
    (((ptr + 288#64) ↦₆₄ st0.getD 18 0#64) ∗ ((ptr + 296#64) ↦₆₄ st1.getD 18 0#64))) ∗
   ((((ptr + 304#64) ↦₆₄ st0.getD 19 0#64) ∗ ((ptr + 312#64) ↦₆₄ st1.getD 19 0#64)) ∗
    (((ptr + 320#64) ↦₆₄ st0.getD 20 0#64) ∗ ((ptr + 328#64) ↦₆₄ st1.getD 20 0#64)))) ∗
  (((((ptr + 336#64) ↦₆₄ st0.getD 21 0#64) ∗ ((ptr + 344#64) ↦₆₄ st1.getD 21 0#64)) ∗
    (((ptr + 352#64) ↦₆₄ st0.getD 22 0#64) ∗ ((ptr + 360#64) ↦₆₄ st1.getD 22 0#64))) ∗
   ((((ptr + 368#64) ↦₆₄ st0.getD 23 0#64) ∗ ((ptr + 376#64) ↦₆₄ st1.getD 23 0#64)) ∗
    (((ptr + 384#64) ↦₆₄ st0.getD 24 0#64) ∗ ((ptr + 392#64) ↦₆₄ st1.getD 24 0#64))))

/-- Full 25-vector (`400`-byte) `KeccakState<2, uint64x2_t>` buffer in memory at `ptr`. -/
@[expose] def Keccak2Mem (ptr : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  Keccak2Rate17Mem ptr st0 st1 ∗ Keccak2Cap8Mem ptr st0 st1

theorem Keccak2Cap8Mem_xorRate17 (ptr : BitVec 64) (st0 st1 : KeccakState)
    (blk0 blk1 : List (BitVec 8))
    (hs0 : st0.size = 25) (hs1 : st1.size = 25) :
    Keccak2Cap8Mem ptr (keccakXorRate17 st0 blk0) (keccakXorRate17 st1 blk1) =
      Keccak2Cap8Mem ptr st0 st1 := by
  have g0 (i : Nat) (hi : 17 ≤ i) (hi25 : i < 25) :
      (keccakXorRate17 st0 blk0).getD i 0#64 = st0.getD i 0#64 := by
    have hnot : ¬(i < 17) := by omega
    simp [keccakXorRate17, Array.getD, hi25, hs0, hnot]
  have g1 (i : Nat) (hi : 17 ≤ i) (hi25 : i < 25) :
      (keccakXorRate17 st1 blk1).getD i 0#64 = st1.getD i 0#64 := by
    have hnot : ¬(i < 17) := by omega
    simp [keccakXorRate17, Array.getD, hi25, hs1, hnot]
  unfold Keccak2Cap8Mem
  simp only [
    g0 17 (by omega) (by omega), g1 17 (by omega) (by omega),
    g0 18 (by omega) (by omega), g1 18 (by omega) (by omega),
    g0 19 (by omega) (by omega), g1 19 (by omega) (by omega),
    g0 20 (by omega) (by omega), g1 20 (by omega) (by omega),
    g0 21 (by omega) (by omega), g1 21 (by omega) (by omega),
    g0 22 (by omega) (by omega), g1 22 (by omega) (by omega),
    g0 23 (by omega) (by omega), g1 23 (by omega) (by omega),
    g0 24 (by omega) (by omega), g1 24 (by omega) (by omega)]

/-! ## `Keccak2Mem` → `memRegion` collapse and `.rodata` round-constant agreement -/

private theorem pair64_entails_memRegion16 (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  have hsplit : memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 :=
    memRegion_split a 8 8 (by decide)
  rw [hsplit]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (pointsTo64_entails_memRegion (a + 8#64) v1)

private theorem quad_entails_memRegion64 (ptr : BitVec 64) (off : Nat)
    (a0 b0 a1 b1 a2 b2 a3 b3 : BitVec 64) :
    ((((ptr + BitVec.ofNat 64 off) ↦₆₄ a0) ∗ ((ptr + BitVec.ofNat 64 (off + 8)) ↦₆₄ b0)) ∗
     (((ptr + BitVec.ofNat 64 (off + 16)) ↦₆₄ a1) ∗ ((ptr + BitVec.ofNat 64 (off + 24)) ↦₆₄ b1))) ∗
    ((((ptr + BitVec.ofNat 64 (off + 32)) ↦₆₄ a2) ∗ ((ptr + BitVec.ofNat 64 (off + 40)) ↦₆₄ b2)) ∗
     (((ptr + BitVec.ofNat 64 (off + 48)) ↦₆₄ a3) ∗ ((ptr + BitVec.ofNat 64 (off + 56)) ↦₆₄ b3))) ⊢
      memRegion (ptr + BitVec.ofNat 64 off) 64 := by
  let base := ptr + BitVec.ofNat 64 off
  have h1 (k : Nat) : ptr + BitVec.ofNat 64 (off + k) = base + BitVec.ofNat 64 k := by
    dsimp [base]; rw [BitVec.ofNat_add]; bv_omega
  rw [h1 8, h1 16, h1 24, h1 32, h1 40, h1 48, h1 56]
  change ((((base ↦₆₄ a0) ∗ ((base + 8#64) ↦₆₄ b0)) ∗
           (((base + 16#64) ↦₆₄ a1) ∗ ((base + 24#64) ↦₆₄ b1))) ∗
          ((((base + 32#64) ↦₆₄ a2) ∗ ((base + 40#64) ↦₆₄ b2)) ∗
           (((base + 48#64) ↦₆₄ a3) ∗ ((base + 56#64) ↦₆₄ b3)))) ⊢ memRegion base 64
  rw [show base + 24#64 = (base + 16#64) + 8#64 by bv_omega,
      show base + 40#64 = (base + 32#64) + 8#64 by bv_omega,
      show base + 56#64 = (base + 48#64) + 8#64 by bv_omega,
      show memRegion base 64 = memRegion base 32 ∗ memRegion (base + 32#64) 32 from
        memRegion_split base 32 32 (by decide),
      show memRegion base 32 = memRegion base 16 ∗ memRegion (base + 16#64) 16 from
        memRegion_split base 16 16 (by decide),
      show memRegion (base + 32#64) 32 =
        memRegion (base + 32#64) 16 ∗ memRegion ((base + 32#64) + 16#64) 16 from
        memRegion_split (base + 32#64) 16 16 (by decide),
      show (base + 32#64) + 16#64 = base + 48#64 by bv_omega]
  exact sepConj_mono
    (sepConj_mono (pair64_entails_memRegion16 _ a0 b0) (pair64_entails_memRegion16 _ a1 b1))
    (sepConj_mono (pair64_entails_memRegion16 _ a2 b2) (pair64_entails_memRegion16 _ a3 b3))

/-- Collapse `Keccak2Mem ptr st0 st1` back into `memRegion ptr 400`. -/
theorem Keccak2Mem_entails_memRegion (ptr : BitVec 64) (st0 st1 : KeccakState) :
    Keccak2Mem ptr st0 st1 ⊢ memRegion ptr 400 := by
  unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
  have hq0 : Keccak2Q0Mem ptr st0 st1 ⊢ memRegion ptr 64 := by
    simpa [Keccak2Q0Mem] using quad_entails_memRegion64 ptr 0
      (st0.getD 0 0#64) (st1.getD 0 0#64) (st0.getD 1 0#64) (st1.getD 1 0#64)
      (st0.getD 2 0#64) (st1.getD 2 0#64) (st0.getD 3 0#64) (st1.getD 3 0#64)
  have hq1 : Keccak2Q1Mem ptr st0 st1 ⊢ memRegion (ptr + 64#64) 64 :=
    quad_entails_memRegion64 ptr 64 _ _ _ _ _ _ _ _
  have hq2 : Keccak2Q2Mem ptr st0 st1 ⊢ memRegion (ptr + 128#64) 64 :=
    quad_entails_memRegion64 ptr 128 _ _ _ _ _ _ _ _
  have hq3 : Keccak2Q3Mem ptr st0 st1 ⊢ memRegion (ptr + 192#64) 64 :=
    quad_entails_memRegion64 ptr 192 _ _ _ _ _ _ _ _
  have hv16 : Keccak2Vec16Mem ptr st0 st1 ⊢ memRegion (ptr + 256#64) 16 := by
    unfold Keccak2Vec16Mem
    rw [show ptr + 264#64 = (ptr + 256#64) + 8#64 by bv_omega]
    exact pair64_entails_memRegion16 (ptr + 256#64) _ _
  have hc8 : Keccak2Cap8Mem ptr st0 st1 ⊢ memRegion (ptr + 272#64) 128 := by
    unfold Keccak2Cap8Mem
    rw [show memRegion (ptr + 272#64) 128 =
          memRegion (ptr + 272#64) 64 ∗ memRegion ((ptr + 272#64) + 64#64) 64 from
          memRegion_split (ptr + 272#64) 64 64 (by decide),
        show (ptr + 272#64) + 64#64 = ptr + 336#64 by bv_omega]
    exact sepConj_mono
      (quad_entails_memRegion64 ptr 272 _ _ _ _ _ _ _ _)
      (quad_entails_memRegion64 ptr 336 _ _ _ _ _ _ _ _)
  rw [show memRegion ptr 400 = memRegion ptr 272 ∗ memRegion (ptr + 272#64) 128 from
        memRegion_split ptr 272 128 (by decide),
      show memRegion ptr 272 = memRegion ptr 256 ∗ memRegion (ptr + 256#64) 16 from
        memRegion_split ptr 256 16 (by decide),
      show memRegion ptr 256 = memRegion ptr 128 ∗ memRegion (ptr + 128#64) 128 from
        memRegion_split ptr 128 128 (by decide),
      show memRegion ptr 128 = memRegion ptr 64 ∗ memRegion (ptr + 64#64) 64 from
        memRegion_split ptr 64 64 (by decide),
      show memRegion (ptr + 128#64) 128 =
        memRegion (ptr + 128#64) 64 ∗ memRegion ((ptr + 128#64) + 64#64) 64 from
        memRegion_split (ptr + 128#64) 64 64 (by decide),
      show (ptr + 128#64) + 64#64 = ptr + 192#64 by bv_omega]
  exact sepConj_mono
    (sepConj_mono
      (sepConj_mono (sepConj_mono hq0 hq1) (sepConj_mono hq2 hq3))
      hv16)
    hc8

/-- For every round `r < 24`, the 64-bit little-endian entry `keccakRcAt r` in `mlkemData01Bytes`
    equals `keccakRoundConstants[r]`. -/
theorem keccakRcAt_eq (r : Nat) (hr : r < 24) :
    keccakRcAt r = keccakRoundConstants.getD r 0#64 := by
  have hall : ∀ k ∈ List.range 24, keccakRcAt k = keccakRoundConstants.getD k 0#64 := by
    decide +kernel
  exact hall r (List.mem_range.mpr hr)

/-- Split a read-only byte slice `(a ↦ᵣ bs)` at byte offset `off ≤ bs.length` into
    `(a ↦ᵣ bs.take off) ∗ ((a + ofNat 64 off) ↦ᵣ bs.drop off)`. -/
theorem pointsToBytesRO_take_drop (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (hoff : off ≤ bs.length) :
    (a ↦ᵣ bs) = (a ↦ᵣ bs.take off) ∗ ((a + BitVec.ofNat 64 off) ↦ᵣ bs.drop off) := by
  conv_lhs => rw [← List.take_append_drop off bs]
  rw [pointsToBytesRO_append, List.length_take_of_le hoff]

/-- Focus a `len`-byte sub-slice `(a + ofNat 64 off) ↦ᵣ (bs.drop off).take len` out of `(a ↦ᵣ bs)`. -/
theorem pointsToBytesRO_focus (a : BitVec 64) (bs : List (BitVec 8)) (off len : Nat)
    (hle : off + len ≤ bs.length) :
    (a ↦ᵣ bs) =
      ((a + BitVec.ofNat 64 off) ↦ᵣ (bs.drop off).take len) ∗
      ((a ↦ᵣ bs.take off) ∗ ((a + BitVec.ofNat 64 (off + len)) ↦ᵣ bs.drop (off + len))) :=
  pointsToBytesRO_split3 a bs off len hle

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
