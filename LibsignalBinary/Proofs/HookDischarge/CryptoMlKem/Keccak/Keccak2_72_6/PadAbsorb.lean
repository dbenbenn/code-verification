/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): `buf1` `SHA3-512` padding and 9-lane absorb

Proof of segment `[0x0600 → 0x06c8]` (`50` instructions) of `mlkemBlk00`: pads `buf1` into
`keccakLastBlock 72 0x06#8 in1` and interleaves/XORs the 9 64-bit rate lanes (`72` bytes) of
`blk0` and `blk1` into `LoopRegs ... 0 st0 st1` and `LoopSpillMem sp st0 st1` at loop header
`+0x06c8`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadAbsorb

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakZeroState
  packLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccakXorRate9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock
  keccakLastBlock_length
  readLE_8_eq_packLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base (
  LaneSlot
  LoopRegs
  LoopSpillMem
  blk00_code_eq
  blk00_tree_size
  blkLib00
  blkPC00
  blkPl00
  blkPlaceable00
  blkTree00
  keccak2Lane_xorRate9_zero_ge
  keccak2Lane_xorRate9_zero_lt
  keccakXorRate9_zero_lt
  padBuf72_eq_lastBlock
  readLE_8_before_write71
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue (
  ZeroStateMem00
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy (
  PadReadyRegs
  orr80_truncate8
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x0600 → 0x06c4]
end

private theorem packLane64_pad1_before_80 (in1 : List (BitVec 8)) (hin1 : in1.length < 72)
    (off : Nat) (hoff : off + 8 ≤ 64 := by decide) :
    packLane64
      (ByteSlice.write8 (in1 ++ List.replicate (72 - in1.length) 0#8) in1.length 0x06#8) off =
      packLane64 (keccakLastBlock 72 0x06#8 in1) off := by
  rw [← readLE_8_eq_packLane64]
  have hlen0 : (in1 ++ List.replicate (72 - in1.length) 0#8).length = 72 := by
    simp; omega
  have hlen :
      72 ≤ (ByteSlice.write8 (in1 ++ List.replicate (72 - in1.length) 0#8) in1.length 0x06#8).length := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hlen0]; omega), hlen0]
  rw [readLE_8_before_write71 _
        ((ByteSlice.write8 (in1 ++ List.replicate (72 - in1.length) 0#8) in1.length 0x06#8).getD 71 0#8 ||| 0x80#8)
        off hlen hoff,
      padBuf72_eq_lastBlock in1 hin1]

private theorem cells2_entails_memRegion16 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢ memRegion a 16 := by
  rw [show memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 from
    memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

private theorem cells4_entails_memRegion32 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
     (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ⊢ memRegion a 32 := by
  rw [show memRegion a 32 = memRegion a 16 ∗ memRegion (a + 16#64) 16 from
        memRegion_split a 16 16 (by decide),
      show a + 24#64 = (a + 16#64) + 8#64 by bv_omega]
  exact sepConj_mono (cells2_entails_memRegion16 a w0 w1)
    (cells2_entails_memRegion16 (a + 16#64) w2 w3)

private theorem cells8_entails_memRegion64 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    ((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
      (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
     ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
      (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ⊢ memRegion a 64 := by
  rw [show memRegion a 64 = memRegion a 32 ∗ memRegion (a + 32#64) 32 from
        memRegion_split a 32 32 (by decide),
      show a + 40#64 = (a + 32#64) + 8#64 by bv_omega,
      show a + 48#64 = (a + 32#64) + 16#64 by bv_omega,
      show a + 56#64 = (a + 32#64) + 24#64 by bv_omega]
  exact sepConj_mono (cells4_entails_memRegion32 a w0 w1 w2 w3)
    (cells4_entails_memRegion32 (a + 32#64) w4 w5 w6 w7)

private theorem zeroCells22_entails_memRegion176 (sp : BitVec 64) :
    ((((sp ↦₆₄ 0#64) ∗ ((sp + 8#64) ↦₆₄ 0#64)) ∗
      (((sp + 16#64) ↦₆₄ 0#64) ∗ ((sp + 24#64) ↦₆₄ 0#64))) ∗
     ((((sp + 32#64) ↦₆₄ 0#64) ∗ ((sp + 40#64) ↦₆₄ 0#64)) ∗
      (((sp + 48#64) ↦₆₄ 0#64) ∗ ((sp + 56#64) ↦₆₄ 0#64)))) ∗
    (((((sp + 64#64) ↦₆₄ 0#64) ∗ ((sp + 72#64) ↦₆₄ 0#64)) ∗
      (((sp + 80#64) ↦₆₄ 0#64) ∗ ((sp + 88#64) ↦₆₄ 0#64))) ∗
     ((((sp + 96#64) ↦₆₄ 0#64) ∗ ((sp + 104#64) ↦₆₄ 0#64)) ∗
      (((sp + 112#64) ↦₆₄ 0#64) ∗ ((sp + 120#64) ↦₆₄ 0#64)))) ∗
    ((((sp + 128#64) ↦₆₄ 0#64) ∗ ((sp + 136#64) ↦₆₄ 0#64)) ∗
     (((sp + 144#64) ↦₆₄ 0#64) ∗ ((sp + 152#64) ↦₆₄ 0#64))) ∗
    (((sp + 160#64) ↦₆₄ 0#64) ∗ ((sp + 168#64) ↦₆₄ 0#64)) ⊢ memRegion sp 176 := by
  have h176 : memRegion sp 176 =
      memRegion sp 64 ∗ memRegion (sp + 64#64) 64 ∗
        memRegion (sp + 128#64) 32 ∗ memRegion (sp + 160#64) 16 := by
    rw [memRegion_split sp 64 112 (by decide),
        memRegion_split (sp + 64#64) 64 48 (by decide),
        show (sp + 64#64) + 64#64 = sp + 128#64 by bv_omega,
        memRegion_split (sp + 128#64) 32 16 (by decide),
        show (sp + 128#64) + 32#64 = sp + 160#64 by bv_omega]
  have h64b :
      ((((sp + 64#64) ↦₆₄ 0#64) ∗ ((sp + 72#64) ↦₆₄ 0#64)) ∗
        (((sp + 80#64) ↦₆₄ 0#64) ∗ ((sp + 88#64) ↦₆₄ 0#64))) ∗
      ((((sp + 96#64) ↦₆₄ 0#64) ∗ ((sp + 104#64) ↦₆₄ 0#64)) ∗
        (((sp + 112#64) ↦₆₄ 0#64) ∗ ((sp + 120#64) ↦₆₄ 0#64))) ⊢ memRegion (sp + 64#64) 64 := by
    rw [show sp + 72#64 = (sp + 64#64) + 8#64 by bv_omega,
        show sp + 80#64 = (sp + 64#64) + 16#64 by bv_omega,
        show sp + 88#64 = (sp + 64#64) + 24#64 by bv_omega,
        show sp + 96#64 = (sp + 64#64) + 32#64 by bv_omega,
        show sp + 104#64 = (sp + 64#64) + 40#64 by bv_omega,
        show sp + 112#64 = (sp + 64#64) + 48#64 by bv_omega,
        show sp + 120#64 = (sp + 64#64) + 56#64 by bv_omega]
    exact cells8_entails_memRegion64 (sp + 64#64) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  have h32c :
      (((sp + 128#64) ↦₆₄ 0#64) ∗ ((sp + 136#64) ↦₆₄ 0#64)) ∗
      (((sp + 144#64) ↦₆₄ 0#64) ∗ ((sp + 152#64) ↦₆₄ 0#64)) ⊢ memRegion (sp + 128#64) 32 := by
    rw [show sp + 136#64 = (sp + 128#64) + 8#64 by bv_omega,
        show sp + 144#64 = (sp + 128#64) + 16#64 by bv_omega,
        show sp + 152#64 = (sp + 128#64) + 24#64 by bv_omega]
    exact cells4_entails_memRegion32 (sp + 128#64) 0#64 0#64 0#64 0#64
  have h16d :
      ((sp + 160#64) ↦₆₄ 0#64) ∗ ((sp + 168#64) ↦₆₄ 0#64) ⊢ memRegion (sp + 160#64) 16 := by
    rw [show sp + 168#64 = (sp + 160#64) + 8#64 by bv_omega]
    exact cells2_entails_memRegion16 (sp + 160#64) 0#64 0#64
  rw [h176]
  exact sepConj_mono (cells8_entails_memRegion64 sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) <|
    sepConj_mono h64b <| sepConj_mono h32c h16d

private theorem cells_to_loopSpillMem_zero (sp : BitVec 64) (st0 st1 : KeccakState) :
    ((sp + 176#64) ↦₆₄ 0#64) ∗ ((sp + 184#64) ↦₆₄ 0#64) ∗
      ((sp + 192#64) ↦₆₄ st0.getD 1 0#64) ∗ ((sp + 200#64) ↦₆₄ st1.getD 1 0#64) ∗
      ((sp + 208#64) ↦₆₄ st0.getD 6 0#64) ∗ ((sp + 216#64) ↦₆₄ st1.getD 6 0#64) ∗
      ((sp + 224#64) ↦₆₄ st0.getD 2 0#64) ∗ ((sp + 232#64) ↦₆₄ st1.getD 2 0#64) ∗
      ((((sp + 240#64) ↦₆₄ 0#64) ∗ ((sp + 248#64) ↦₆₄ 0#64)) ∗
        (((sp + 256#64) ↦₆₄ 0#64) ∗ ((sp + 264#64) ↦₆₄ 0#64))) ∗
      ((((sp + 272#64) ↦₆₄ 0#64) ∗ ((sp + 280#64) ↦₆₄ 0#64)) ∗
        (((sp + 288#64) ↦₆₄ 0#64) ∗ ((sp + 296#64) ↦₆₄ 0#64))) ∗
      ((sp + 304#64) ↦₆₄ st0.getD 3 0#64) ∗ ((sp + 312#64) ↦₆₄ st1.getD 3 0#64) ∗
      ((((sp + 320#64) ↦₆₄ 0#64) ∗ ((sp + 328#64) ↦₆₄ 0#64)) ∗
        (((sp + 336#64) ↦₆₄ 0#64) ∗ ((sp + 344#64) ↦₆₄ 0#64))) ∗
      ((((sp + 352#64) ↦₆₄ 0#64) ∗ ((sp + 360#64) ↦₆₄ 0#64)) ∗
        (((sp + 368#64) ↦₆₄ 0#64) ∗ ((sp + 376#64) ↦₆₄ 0#64))) ∗
      ((sp + 384#64) ↦₆₄ st0.getD 4 0#64) ∗ ((sp + 392#64) ↦₆₄ st1.getD 4 0#64) ⊢
      LoopSpillMem sp st0 st1 := by
  have h16 :
      ((sp + 176#64) ↦₆₄ 0#64) ∗ ((sp + 184#64) ↦₆₄ 0#64) ⊢ memRegion (sp + 176#64) 16 := by
    rw [show sp + 184#64 = (sp + 176#64) + 8#64 by bv_omega]
    exact cells2_entails_memRegion16 (sp + 176#64) 0#64 0#64
  have h64u :
      ((((sp + 240#64) ↦₆₄ 0#64) ∗ ((sp + 248#64) ↦₆₄ 0#64)) ∗
        (((sp + 256#64) ↦₆₄ 0#64) ∗ ((sp + 264#64) ↦₆₄ 0#64))) ∗
      ((((sp + 272#64) ↦₆₄ 0#64) ∗ ((sp + 280#64) ↦₆₄ 0#64)) ∗
        (((sp + 288#64) ↦₆₄ 0#64) ∗ ((sp + 296#64) ↦₆₄ 0#64))) ⊢ memRegion (sp + 240#64) 64 := by
    rw [show sp + 248#64 = (sp + 240#64) + 8#64 by bv_omega,
        show sp + 256#64 = (sp + 240#64) + 16#64 by bv_omega,
        show sp + 264#64 = (sp + 240#64) + 24#64 by bv_omega,
        show sp + 272#64 = (sp + 240#64) + 32#64 by bv_omega,
        show sp + 280#64 = (sp + 240#64) + 40#64 by bv_omega,
        show sp + 288#64 = (sp + 240#64) + 48#64 by bv_omega,
        show sp + 296#64 = (sp + 240#64) + 56#64 by bv_omega]
    exact cells8_entails_memRegion64 (sp + 240#64) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  have h64w :
      ((((sp + 320#64) ↦₆₄ 0#64) ∗ ((sp + 328#64) ↦₆₄ 0#64)) ∗
        (((sp + 336#64) ↦₆₄ 0#64) ∗ ((sp + 344#64) ↦₆₄ 0#64))) ∗
      ((((sp + 352#64) ↦₆₄ 0#64) ∗ ((sp + 360#64) ↦₆₄ 0#64)) ∗
        (((sp + 368#64) ↦₆₄ 0#64) ∗ ((sp + 376#64) ↦₆₄ 0#64))) ⊢ memRegion (sp + 320#64) 64 := by
    rw [show sp + 328#64 = (sp + 320#64) + 8#64 by bv_omega,
        show sp + 336#64 = (sp + 320#64) + 16#64 by bv_omega,
        show sp + 344#64 = (sp + 320#64) + 24#64 by bv_omega,
        show sp + 352#64 = (sp + 320#64) + 32#64 by bv_omega,
        show sp + 360#64 = (sp + 320#64) + 40#64 by bv_omega,
        show sp + 368#64 = (sp + 320#64) + 48#64 by bv_omega,
        show sp + 376#64 = (sp + 320#64) + 56#64 by bv_omega]
    exact cells8_entails_memRegion64 (sp + 320#64) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  have sub : ∀ {A B P Rest Q : SepProp},
      (A ⊢ B) → (P ⊢ A ∗ Rest) → (B ∗ Rest ⊢ Q) → (P ⊢ Q) :=
    fun hAB h1 h2 => Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)
  dsimp only [LoopSpillMem, LaneSlot]
  exact sub h16 (by sep_frame) (sub h64u (by sep_frame) (sub h64w (by sep_frame) (by sep_frame)))

private theorem padBufs_entails_memRegion160 (sp : BitVec 64)
    (blk0 blk1 : List (BitVec 8)) (h0 : blk0.length = 72) (h1 : blk1.length = 72) :
    ((sp + 400#64) ↦ₛ blk0) ∗ memRegion (sp + 472#64) 8 ∗
      ((sp + 480#64) ↦ₛ blk1) ∗ memRegion (sp + 552#64) 8 ⊢
      memRegion (sp + 400#64) 160 := by
  have h160 : memRegion (sp + 400#64) 160 =
      memRegion (sp + 400#64) 72 ∗ memRegion (sp + 472#64) 8 ∗
        memRegion (sp + 480#64) 72 ∗ memRegion (sp + 552#64) 8 := by
    rw [memRegion_split (sp + 400#64) 72 88 (by decide),
        show (sp + 400#64) + 72#64 = sp + 472#64 by bv_omega,
        memRegion_split (sp + 472#64) 8 80 (by decide),
        show (sp + 472#64) + 8#64 = sp + 480#64 by bv_omega,
        memRegion_split (sp + 480#64) 72 8 (by decide),
        show (sp + 480#64) + 72#64 = sp + 552#64 by bv_omega]
  have e0 : ((sp + 400#64) ↦ₛ blk0) ⊢ memRegion (sp + 400#64) 72 := by
    simpa only [h0] using pointsToBytes_entails_memRegion (sp + 400#64) blk0
  have e1 : ((sp + 480#64) ↦ₛ blk1) ⊢ memRegion (sp + 480#64) 72 := by
    simpa only [h1] using pointsToBytes_entails_memRegion (sp + 480#64) blk1
  rw [h160]
  exact sepConj_mono e0 (sepConj_mono (Entails.refl _) (sepConj_mono e1 (Entails.refl _)))

private theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

public section

/-- Step `[0x0600 → 0x06c8]` (`buf1` SHA3-512 pad + 9-lane 2-way absorb into `LoopRegs` and
    `LoopSpillMem`). -/
theorem pad1_absorb_ok [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (sp rcBase out0 out1 : BitVec 64)
    (in0 in1 : List (BitVec 8)) (_hin0 : in0.length < 72) (hin1 : in1.length < 72)
    (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x0600#64)
    (hregs : PadReadyRegs s sp rcBase out0 out1 in1.length) :
    let blk0 := keccakLastBlock 72 0x06#8 in0
    let blk1 := keccakLastBlock 72 0x06#8 in1
    let st0 := keccakXorRate9 keccakZeroState blk0
    let st1 := keccakXorRate9 keccakZeroState blk1
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x06c8#64) s
      (ZeroStateMem00 sp ∗
        ((sp + 400#64) ↦ₛ blk0) ∗
        memRegion (sp + 472#64) 8 ∗
        ((sp + 480#64) ↦ₛ (in1 ++ List.replicate (72 - in1.length) 0#8)) ∗
        memRegion (sp + 552#64) 8 ∗ F)
      (sepPost
        (fun sm => LoopRegs sm sp rcBase out0 out1 0 st0 st1)
        (memRegion sp 176 ∗ LoopSpillMem sp st0 st1 ∗ memRegion (sp + 400#64) 160 ∗ F)) := by
  intro blk0 blk1 st0 st1
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx26, hx25, hx24, hx21, hx20, hx19⟩
  have hblk0_len : blk0.length = 72 :=
    keccakLastBlock_length 72 0x06#8 in0
  have hblk1_len : blk1.length = 72 :=
    keccakLastBlock_length 72 0x06#8 in1
  have hbuf1_0_len : (in1 ++ List.replicate (72 - in1.length) 0#8).length = 72 := by
    clear * - hin1; simp; omega
  have hbuf1_1_len :
      (ByteSlice.write8 (in1 ++ List.replicate (72 - in1.length) 0#8) in1.length 0x06#8).length = 72 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf1_0_len]; omega), hbuf1_0_len]
  dsimp only [ZeroStateMem00]
  wp_steps 16
  simp only [orr80_truncate8, padBuf72_eq_lastBlock in1 hin1]
  rw [show keccakLastBlock 72 0x06#8 in1 = blk1 from rfl]
  apply step_simdLd1Single64
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨?_, ?_⟩
    · refine
        { hrun      := by wp_norm_lhs
          hsp_align := by wp_norm_lhs
          hsp       := by wp_norm_lhs
          hx29      := by wp_norm_lhs
          hx25      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx19      := by wp_norm_lhs
          hx8       := by wp_norm_lhs
          hv18      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 in1 hin1 0,
                keccak2Lane_xorRate9_zero_lt blk0 blk1 (idx := 0) (by decide)]
          hv29      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 in1 hin1 40,
                keccak2Lane_xorRate9_zero_lt blk0 blk1 (idx := 5) (by decide)]
          hv20      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 in1 hin1 56,
                keccak2Lane_xorRate9_zero_lt blk0 blk1 (idx := 7) (by decide)]
          hv10      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            simp only [readLE_8_eq_packLane64]
            rw [keccak2Lane_xorRate9_zero_lt blk0 blk1 (idx := 8) (by decide)]
          hv0       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv28      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv12      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv8       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv7       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv13      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv6       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv15      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv11      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv14      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv30      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv27      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv1       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv5       := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv25      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)]
          hv26      := by
            refine Eq.trans (by wp_norm_lhs) ?_
            rw [keccak2Lane_xorRate9_zero_ge blk0 blk1 (by decide)] }
    · simp only [readLE_8_eq_packLane64]
      rw [packLane64_pad1_before_80 in1 hin1 8,
          packLane64_pad1_before_80 in1 hin1 16,
          packLane64_pad1_before_80 in1 hin1 24,
          packLane64_pad1_before_80 in1 hin1 32,
          packLane64_pad1_before_80 in1 hin1 48,
          show keccakLastBlock 72 0x06#8 in1 = blk1 from rfl]
      have hl1_0 : packLane64 blk0 8  = st0.getD 1 0#64 :=
        (keccakXorRate9_zero_lt blk0 (idx := 1) (by decide)).symm
      have hl1_1 : packLane64 blk1 8  = st1.getD 1 0#64 :=
        (keccakXorRate9_zero_lt blk1 (idx := 1) (by decide)).symm
      have hl2_0 : packLane64 blk0 16 = st0.getD 2 0#64 :=
        (keccakXorRate9_zero_lt blk0 (idx := 2) (by decide)).symm
      have hl2_1 : packLane64 blk1 16 = st1.getD 2 0#64 :=
        (keccakXorRate9_zero_lt blk1 (idx := 2) (by decide)).symm
      have hl3_0 : packLane64 blk0 24 = st0.getD 3 0#64 :=
        (keccakXorRate9_zero_lt blk0 (idx := 3) (by decide)).symm
      have hl3_1 : packLane64 blk1 24 = st1.getD 3 0#64 :=
        (keccakXorRate9_zero_lt blk1 (idx := 3) (by decide)).symm
      have hl4_0 : packLane64 blk0 32 = st0.getD 4 0#64 :=
        (keccakXorRate9_zero_lt blk0 (idx := 4) (by decide)).symm
      have hl4_1 : packLane64 blk1 32 = st1.getD 4 0#64 :=
        (keccakXorRate9_zero_lt blk1 (idx := 4) (by decide)).symm
      have hl6_0 : packLane64 blk0 48 = st0.getD 6 0#64 :=
        (keccakXorRate9_zero_lt blk0 (idx := 6) (by decide)).symm
      have hl6_1 : packLane64 blk1 48 = st1.getD 6 0#64 :=
        (keccakXorRate9_zero_lt blk1 (idx := 6) (by decide)).symm
      rw [hl1_0, hl1_1, hl2_0, hl2_1, hl3_0, hl3_1, hl4_0, hl4_1, hl6_0, hl6_1]
      exact entails_sub (zeroCells22_entails_memRegion176 sp) (by sep_frame)
        (entails_sub (cells_to_loopSpillMem_zero sp st0 st1) (by sep_frame)
          (entails_sub (padBufs_entails_memRegion160 sp blk0 blk1 hblk0_len hblk1_len)
            (by sep_frame) (by sep_frame)))

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadAbsorb
