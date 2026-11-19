/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WPFrozen

/-!
# `B00` (`keccak2::<72, 6>`): placed-code tree and loop state invariants

Shared definitions and helper lemmas for `mlkemBlk00` (`713` words):
- `WordTree` reflection for `libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>`.
- `sepWP_seq_env` segment sequencer preserving `CodeLoaded` and `MlKemRoOk`.
- Spilled callee-saved frame `SavedFrame00` (`160` bytes at `[sp0 - 160, sp0)`).
- Arithmetic, pad-buffer, and `keccakXorRate9` helper lemmas for the `inLen < 72` path.
- Register and stack-spill invariants at loop header `+0x06c8` (`LoopRegs`, `LoopSpillMem`) and
  mid-round cut `+0x07fc` (`MidRegs`, `MidSpillMem`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakZeroState
  packLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
  keccakXorRate9
  keccakZeroState_getD
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakD
  keccakRhoPi
  keccakTheta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock
  keccakPadBuf_eq_lastBlock
  readLE_8_eq_packLane64
)

/-! ## Placed-block reflection (`mlkemBlk00`, `713` words) and segment sequencer -/

@[expose] def blkLib00 : PlacedLib := mlkemMultiLib.blockLib 0

@[expose] def blkPl00 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 0

theorem blkPlaceable00 [MlKemPlacement] : blkLib00.Placeable blkPl00 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable

@[expose] def blkPC00 [MlKemPlacement] : Program := blkLib00.program blkPl00

@[expose] def blkProg00 : Program :=
  { code := blkLib00.text.code, symbols := blkLib00.text.symbols }

@[expose] def blkTree00 : WordTree := word_tree_of% blkProg00

set_option maxRecDepth 20000 in
theorem blk00_code_eq : blkLib00.text.code = blkTree00.toBytes := by rfl_kernel

theorem blk00_tree_size : blkTree00.checkSize? = some 713 := by rfl_kernel

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen`
    transitions. -/
theorem sepWP_seq_env {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        mlkemMultiLib.CodeLoaded mpl sm.mem ∧ MlKemRoOk mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun _ _ _ _ ⟨hc, hr⟩ hp1 => ⟨hc, hr, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hr, hp1⟩ => h2 sm Pm hpc hrun hc hr hp1)

/-! ## Spilled callee-saved frame (`[sp0 - 160, sp0)`) -/

/-- All 20 callee-saved registers (`d15..d8`, `fp, lr`, `x28..x19`) spilled at `[sp0 - 160, sp0)`. -/
@[expose] def SavedFrame00 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
  ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
  ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
  ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
  ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
  ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
  ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
  ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).truncate 64) ∗
  ((sp0 - 96#64)  ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 88#64)  ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 80#64)  ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64)  ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64)  ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64)  ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64)  ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64)  ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64)  ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64)  ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64)  ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64)   ↦₆₄ s0.readReg64 .x19)

theorem savedFrame00_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame00 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  dsimp only [SavedFrame00]
  have hsplit :
      memRegion (sp0 - 160#64) 160 =
        memRegion (sp0 - 160#64) 8 ∗ memRegion (sp0 - 152#64) 8 ∗
        memRegion (sp0 - 144#64) 8 ∗ memRegion (sp0 - 136#64) 8 ∗
        memRegion (sp0 - 128#64) 8 ∗ memRegion (sp0 - 120#64) 8 ∗
        memRegion (sp0 - 112#64) 8 ∗ memRegion (sp0 - 104#64) 8 ∗
        memRegion (sp0 - 96#64) 8 ∗ memRegion (sp0 - 88#64) 8 ∗
        memRegion (sp0 - 80#64) 8 ∗ memRegion (sp0 - 72#64) 8 ∗
        memRegion (sp0 - 64#64) 8 ∗ memRegion (sp0 - 56#64) 8 ∗
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 152#64) (n := 8) (k := 152) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 152#64) (b' := sp0 - 144#64) (n := 8) (k := 144) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := 136) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 120#64) (b' := sp0 - 112#64) (n := 8) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 112#64) (b' := sp0 - 104#64) (n := 8) (k := 104) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 104#64) (b' := sp0 - 96#64) (n := 8) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 88#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 88#64) (b' := sp0 - 80#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 80#64) (b' := sp0 - 72#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 72#64) (b' := sp0 - 64#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 56#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 56#64) (b' := sp0 - 48#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)

/-! ## Arithmetic, pad-buffer, and `keccakXorRate9` helpers -/

theorem xor_left_comm {w : Nat} (a b c : BitVec w) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem umulh_div72_nat {n : Nat} (hn : n < 72) :
    (n * 0xe38e38e38e38e38f / 2 ^ 64) / 2 ^ 6 = 0 := by
  rw [Nat.div_div_eq_div_mul]
  omega

theorem umulh_div72_bv {n : Nat} (hn : n < 72) :
    BitVec.ofNat 64 (((BitVec.ofNat 64 n).toNat * (0xe38e38e38e38e38f#64).toNat) / 2 ^ 64) >>> 6 =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc : (0xe38e38e38e38e38f#64).toNat = 0xe38e38e38e38e38f := rfl
  rw [hn64, hc]
  have hlt : n * 0xe38e38e38e38e38f / 2 ^ 64 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.shiftRight_eq_div_pow, umulh_div72_nat hn]
  rfl

theorem padBuf72_eq_lastBlock (msg : List (BitVec 8)) (hlt : msg.length < 72) :
    let buf0 := msg ++ List.replicate (72 - msg.length) 0#8
    let buf1 := ByteSlice.write8 buf0 msg.length 0x06#8
    ByteSlice.write8 buf1 71 (buf1.getD 71 0#8 ||| 0x80#8) =
      keccakLastBlock 72 0x06#8 msg := by
  have h := keccakPadBuf_eq_lastBlock (rateBytes := 72) 0x06#8 msg (by decide) (by decide)
  have hdiv : msg.length / 72 = 0 := Nat.div_eq_of_lt hlt
  have hmod : msg.length % 72 = msg.length := Nat.mod_eq_of_lt hlt
  simpa only [hdiv, hmod, Nat.zero_mul, List.drop_zero] using h

theorem readLE_8_before_write71 (buf : List (BitVec 8)) (v : BitVec 8) (off : Nat)
    (hlen : 72 ≤ buf.length) (hoff : off + 8 ≤ 64) :
    ByteSlice.readLE buf off 8 = packLane64 (ByteSlice.write8 buf 71 v) off := by
  rw [readLE_8_eq_packLane64]
  unfold packLane64
  have g (j : Nat) (hj : j < 8) :
      buf.getD (off + j) 0#8 = (ByteSlice.write8 buf 71 v).getD (off + j) 0#8 := by
    rw [ByteSlice.getD_write8 buf 71 v (off + j) 0#8 (by omega)]
    have hne : off + j ≠ 71 := by omega
    simp [hne]
  rw [show buf.getD off 0#8 = buf.getD (off + 0) 0#8 by simp,
      g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide),
      Nat.add_zero]

theorem keccakXorRate9_size (s : KeccakState) (blk : List (BitVec 8)) :
    (keccakXorRate9 s blk).size = 25 := by
  simp [keccakXorRate9]

theorem keccakXorRate9_zero_lt (blk : List (BitVec 8)) {idx : Nat} (h : idx < 9) :
    (keccakXorRate9 keccakZeroState blk).getD idx 0#64 = packLane64 blk (8 * idx) := by
  have h25 : idx < 25 := by omega
  simp [keccakXorRate9, keccakZeroState, h25, h]

theorem keccakXorRate9_zero_ge (blk : List (BitVec 8)) {idx : Nat} (h : 9 ≤ idx) :
    (keccakXorRate9 keccakZeroState blk).getD idx 0#64 = 0#64 := by
  by_cases h25 : idx < 25
  · have hnot : ¬(idx < 9) := by omega
    simp [keccakXorRate9, keccakZeroState, h25, hnot]
  · simp [keccakXorRate9, h25]

theorem keccak2Lane_xorRate9_zero_lt (blk0 blk1 : List (BitVec 8)) {idx : Nat} (h : idx < 9) :
    keccak2Lane (keccakXorRate9 keccakZeroState blk0) (keccakXorRate9 keccakZeroState blk1) idx =
      packLane64 blk1 (8 * idx) ++ packLane64 blk0 (8 * idx) := by
  simp [keccak2Lane, keccakXorRate9_zero_lt _ h]

theorem keccak2Lane_xorRate9_zero_ge (blk0 blk1 : List (BitVec 8)) {idx : Nat} (h : 9 ≤ idx) :
    keccak2Lane (keccakXorRate9 keccakZeroState blk0) (keccakXorRate9 keccakZeroState blk1) idx =
      0#128 := by
  simp only [keccak2Lane, keccakXorRate9_zero_ge _ h]
  rfl

/-! ## 2-way round helpers and stack/register loop invariants (`+0x06c8` and `+0x07fc`) -/

@[expose] def keccak2D (st0 st1 : KeccakState) (x : Nat) : BitVec 128 :=
  keccakD st1 x ++ keccakD st0 x

@[expose] def keccak2Theta (st0 st1 : KeccakState) (idx : Nat) : BitVec 128 :=
  keccakTheta st1 idx ++ keccakTheta st0 idx

@[expose] def keccak2RhoPi (st0 st1 : KeccakState) (idx : Nat) : BitVec 128 :=
  keccakRhoPi st1 idx ++ keccakRhoPi st0 idx

/-- 16-byte stack slot at `sp + off` holding 2-way Keccak lane `idx` (`st0[idx]` low, `st1[idx]` high). -/
@[expose] def LaneSlot (sp : BitVec 64) (off : Nat) (st0 st1 : KeccakState) (idx : Nat) : SepProp :=
  ((sp + BitVec.ofNat 64 off) ↦₆₄ st0.getD idx 0#64) ∗
    ((sp + BitVec.ofNat 64 (off + 8)) ↦₆₄ st1.getD idx 0#64)

/-- 224-byte stack spill region `[sp + 176 .. sp + 400]` at loop header `+0x06c8` (`r = 0 .. 24`):
    lanes `1, 6, 2, 3, 4` live at offsets `192, 208, 224, 304, 384`; remaining `144` bytes are scratch. -/
@[expose] def LoopSpillMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  memRegion (sp + 176#64) 16 ∗
    LaneSlot sp 192 st0 st1 1 ∗
    LaneSlot sp 208 st0 st1 6 ∗
    LaneSlot sp 224 st0 st1 2 ∗
    memRegion (sp + 240#64) 64 ∗
    LaneSlot sp 304 st0 st1 3 ∗
    memRegion (sp + 320#64) 64 ∗
    LaneSlot sp 384 st0 st1 4

/-- 224-byte stack spill region `[sp + 176 .. sp + 400]` at mid-round cut `+0x07fc`:
    slots `240..288` hold `A[13], A[18], A[7], A[8]` and `320..368` hold `A[24], A[19], A[14], A[9]`. -/
@[expose] def MidSpillMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  memRegion (sp + 176#64) 16 ∗
    LaneSlot sp 192 st0 st1 1 ∗
    LaneSlot sp 208 st0 st1 6 ∗
    LaneSlot sp 224 st0 st1 2 ∗
    LaneSlot sp 240 st0 st1 13 ∗
    LaneSlot sp 256 st0 st1 18 ∗
    LaneSlot sp 272 st0 st1 7 ∗
    LaneSlot sp 288 st0 st1 8 ∗
    LaneSlot sp 304 st0 st1 3 ∗
    LaneSlot sp 320 st0 st1 24 ∗
    LaneSlot sp 336 st0 st1 19 ∗
    LaneSlot sp 352 st0 st1 14 ∗
    LaneSlot sp 368 st0 st1 9 ∗
    LaneSlot sp 384 st0 st1 4

theorem laneSlot_entails_memRegion (sp : BitVec 64) (off : Nat)
    (st0 st1 : KeccakState) (idx : Nat) :
    LaneSlot sp off st0 st1 idx ⊢ memRegion (sp + BitVec.ofNat 64 off) 16 := by
  dsimp only [LaneSlot]
  have h16 : memRegion (sp + BitVec.ofNat 64 off) 16 =
      memRegion (sp + BitVec.ofNat 64 off) 8 ∗
        memRegion ((sp + BitVec.ofNat 64 off) + 8#64) 8 :=
    memRegion_split (sp + BitVec.ofNat 64 off) 8 8 (by decide)
  have hadd : sp + BitVec.ofNat 64 (off + 8) = (sp + BitVec.ofNat 64 off) + 8#64 := by bv_omega
  rw [h16, hadd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem LoopSpillMem_entails_memRegion224 (sp : BitVec 64) (st0 st1 : KeccakState) :
    LoopSpillMem sp st0 st1 ⊢ memRegion (sp + 176#64) 224 := by
  dsimp only [LoopSpillMem]
  have e192 := laneSlot_entails_memRegion sp 192 st0 st1 1
  have e208 := laneSlot_entails_memRegion sp 208 st0 st1 6
  have e224 := laneSlot_entails_memRegion sp 224 st0 st1 2
  have e304 := laneSlot_entails_memRegion sp 304 st0 st1 3
  have e384 := laneSlot_entails_memRegion sp 384 st0 st1 4
  have hsplit : memRegion (sp + 176#64) 224 =
      memRegion (sp + 176#64) 16 ∗
        memRegion (sp + 192#64) 16 ∗
        memRegion (sp + 208#64) 16 ∗
        memRegion (sp + 224#64) 16 ∗
        memRegion (sp + 240#64) 64 ∗
        memRegion (sp + 304#64) 16 ∗
        memRegion (sp + 320#64) 64 ∗
        memRegion (sp + 384#64) 16 := by
    rw [memRegion_split (sp + 176#64) 16 208 (by decide),
        show (sp + 176#64) + 16#64 = sp + 192#64 by bv_omega,
        memRegion_split (sp + 192#64) 16 192 (by decide),
        show (sp + 192#64) + 16#64 = sp + 208#64 by bv_omega,
        memRegion_split (sp + 208#64) 16 176 (by decide),
        show (sp + 208#64) + 16#64 = sp + 224#64 by bv_omega,
        memRegion_split (sp + 224#64) 16 160 (by decide),
        show (sp + 224#64) + 16#64 = sp + 240#64 by bv_omega,
        memRegion_split (sp + 240#64) 64 96 (by decide),
        show (sp + 240#64) + 64#64 = sp + 304#64 by bv_omega,
        memRegion_split (sp + 304#64) 16 80 (by decide),
        show (sp + 304#64) + 16#64 = sp + 320#64 by bv_omega,
        memRegion_split (sp + 320#64) 64 16 (by decide),
        show (sp + 320#64) + 64#64 = sp + 384#64 by bv_omega]
  rw [hsplit]
  exact sepConj_mono (Entails.refl _) <|
    sepConj_mono e192 <|
    sepConj_mono e208 <|
    sepConj_mono e224 <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono e304 <|
    sepConj_mono (Entails.refl _) e384

/-- Register state at loop header `+0x06c8` before round `r` (`0 ≤ r ≤ 24`). -/
structure LoopRegs (s : State) (sp rcBase out0 out1 : BitVec 64)
    (r : Nat) (st0 st1 : KeccakState) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx25      : s.readReg64 .x25 = rcBase
  hx20      : s.readReg64 .x20 = out0
  hx19      : s.readReg64 .x19 = out1
  hx8       : s.readReg64 .x8 = BitVec.ofNat 64 (8 * r)
  hv18      : s.readVReg128 18#5 = keccak2Lane st0 st1 0
  hv29      : s.readVReg128 29#5 = keccak2Lane st0 st1 5
  hv20      : s.readVReg128 20#5 = keccak2Lane st0 st1 7
  hv10      : s.readVReg128 10#5 = keccak2Lane st0 st1 8
  hv0       : s.readVReg128 0#5  = keccak2Lane st0 st1 9
  hv28      : s.readVReg128 28#5 = keccak2Lane st0 st1 10
  hv12      : s.readVReg128 12#5 = keccak2Lane st0 st1 11
  hv8       : s.readVReg128 8#5  = keccak2Lane st0 st1 12
  hv7       : s.readVReg128 7#5  = keccak2Lane st0 st1 13
  hv13      : s.readVReg128 13#5 = keccak2Lane st0 st1 14
  hv6       : s.readVReg128 6#5  = keccak2Lane st0 st1 15
  hv15      : s.readVReg128 15#5 = keccak2Lane st0 st1 16
  hv11      : s.readVReg128 11#5 = keccak2Lane st0 st1 17
  hv14      : s.readVReg128 14#5 = keccak2Lane st0 st1 18
  hv30      : s.readVReg128 30#5 = keccak2Lane st0 st1 19
  hv27      : s.readVReg128 27#5 = keccak2Lane st0 st1 20
  hv1       : s.readVReg128 1#5  = keccak2Lane st0 st1 21
  hv5       : s.readVReg128 5#5  = keccak2Lane st0 st1 22
  hv25      : s.readVReg128 25#5 = keccak2Lane st0 st1 23
  hv26      : s.readVReg128 26#5 = keccak2Lane st0 st1 24

/-- Register state at mid-round cut `+0x07fc` during round `r` (`r < 24`). -/
structure MidRegs (s : State) (sp rcBase out0 out1 : BitVec 64)
    (r : Nat) (st0 st1 : KeccakState) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx25      : s.readReg64 .x25 = rcBase
  hx20      : s.readReg64 .x20 = out0
  hx19      : s.readReg64 .x19 = out1
  hx8       : s.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1))
  hx9       : s.readReg64 .x9 = rcBase + BitVec.ofNat 64 (8 * r)
  hpstate   : s.pstate = subsPState64 (BitVec.ofNat 64 (8 * (r + 1))) 192#64
  hv0       : s.readVReg128 0#5  = keccak2Lane st0 st1 7
  hv1       : s.readVReg128 1#5  = keccak2Lane st0 st1 22
  hv4       : s.readVReg128 4#5  = keccak2Theta st0 st1 2
  hv5       : s.readVReg128 5#5  = keccak2RhoPi st0 st1 1
  hv6       : s.readVReg128 6#5  = keccak2D st0 st1 4
  hv7       : s.readVReg128 7#5  = keccak2D st0 st1 3
  hv8       : s.readVReg128 8#5  = keccak2Theta st0 st1 1
  hv9       : s.readVReg128 9#5  = keccak2D st0 st1 2
  hv10      : s.readVReg128 10#5 = keccak2Theta st0 st1 17
  hv13      : s.readVReg128 13#5 = keccak2Lane st0 st1 23
  hv16      : s.readVReg128 16#5 = keccak2RhoPi st0 st1 23
  hv18      : s.readVReg128 18#5 = keccak2Lane st0 st1 0
  hv19      : s.readVReg128 19#5 = keccak2RhoPi st0 st1 14
  hv21      : s.readVReg128 21#5 = keccak2D st0 st1 0
  hv24      : s.readVReg128 24#5 = keccak2RhoPi st0 st1 7
  hv25      : s.readVReg128 25#5 = keccak2Theta st0 st1 11
  hv27      : s.readVReg128 27#5 = keccak2Theta st0 st1 5
  hv29      : s.readVReg128 29#5 = keccak2Theta st0 st1 16
  hv30      : s.readVReg128 30#5 = keccak2Theta st0 st1 21
  hv31      : s.readVReg128 31#5 = keccak2Theta st0 st1 12

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
