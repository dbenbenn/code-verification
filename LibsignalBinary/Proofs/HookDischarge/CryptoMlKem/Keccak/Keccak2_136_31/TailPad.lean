/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute2 -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B01` (`keccak2::<136, 31>`): tail `memcpy`, `SHAKE-256` padding, and 17-lane XOR

Proof of segment `[0x0434 → 0x05e4]` of `mlkemBlk01`: copies both input tails via `B28`
`memcpy`, applies `0x1f` / `0x80` `SHAKE-256` padding (`keccakLastBlock 136 0x1f#8`), and
interleaves/XORs all 17 rate lanes into `P2RoundRegs` and `Spill11` entering `Permute2` at
`+0x05e4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.TailPad

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs
  Keccak2SlicesRO
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk28
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  packLane64
  unpackLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpyRO_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Mem
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccak2Lane
  keccakXorRate17
  keccakXorRate17_getD_ge
  pointsToBytesRO_take_drop
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  extractLsb_hi_append
  extractLsb_lo_append
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorbPrefix17_size
  keccakLastBlock
  keccakLastBlock_length
  keccakPadBuf_eq_lastBlock
  memRegion128_cells
  pointsTo64_16_eq_bytes
  readLE_8_eq_packLane64
  unpackLane64_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  SavedCalleeFrame
  Spill11
  blk01_code_eq
  blk01_tree_size
  blkLib01
  blkPC01
  blkPl01
  blkPlaceable01
  blkTree01
  entails_sub
  memRegion176_to_spill11
  readLE_write8_135_lt
  replicate136_entails_split
  xor_packLane_left
  xor_packLane_right
  zero17_eq_replicate136
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue (
  AbsorbInvMem
  PostAbsorbRegs
  ofNat_mul136
  sepWP_seq_cl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute2 (P2RoundRegs)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x0434 → 0x05e0]
end

attribute [local simp, local arm64_norm, local wp_norm] ofNat_mul136

public section

/-- Scalar registers live at `+0x05e4` entering `Permute2.permute2_rounds`. -/
@[expose] def TailPermuteEntryRegs (s s0 : State) (rcBase : BitVec 64)
    (a : Keccak2ShakeArgs) : Prop :=
  s.status = .Running ∧
  s.spAligned = true ∧
  s.sp = s0.sp - 1040#64 ∧
  s.readReg64 .x8 = 0#64 ∧
  s.readReg64 .x20 = BitVec.ofNat 64 a.outLen ∧
  s.readReg64 .x21 = a.out1 ∧
  s.readReg64 .x22 = a.out0 ∧
  s.readReg64 .x27 = rcBase ∧
  s.readReg64 .fp = s0.sp - 96#64

end

/-! ## Arithmetic, pad-buffer, and lane-XOR helpers -/

private theorem sub_div_mul136_bv (n : Nat) (_hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (n / 136 * 136) = BitVec.ofNat 64 (n % 136) := by
  have h : n = n / 136 * 136 + n % 136 := by have := Nat.div_add_mod n 136; omega
  conv_lhs => rw [show BitVec.ofNat 64 n = BitVec.ofNat 64 (n / 136 * 136 + n % 136) from congrArg _ h]
  rw [BitVec.ofNat_add]; bv_omega

private theorem orr80_truncate8 (v : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v ||| 549755814016#64) = v ||| 0x80#8 := by
  bv_bits

private theorem padBuf136_31_eq_lastBlock (msg : List (BitVec 8)) :
    let buf0 := msg.drop (msg.length / 136 * 136) ++ List.replicate (136 - msg.length % 136) 0#8
    let buf1 := ByteSlice.write8 buf0 (msg.length % 136) 0x1f#8
    ByteSlice.write8 buf1 135 (buf1.getD 135 0#8 ||| 0x80#8) = keccakLastBlock 136 0x1f#8 msg :=
  keccakPadBuf_eq_lastBlock (rateBytes := 136) 0x1f#8 msg (by decide) (by decide)

private theorem lane_xor_left (st0 st1 : KeccakState) (blk0 blk1 : List (BitVec 8))
    (off k : Nat) (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    (packLane64 blk1 off ^^^ st1.getD k 0#64) ++ (packLane64 blk0 off ^^^ st0.getD k 0#64) =
      keccak2Lane (keccakXorRate17 st0 blk0) (keccakXorRate17 st1 blk1) k := by
  unfold keccak2Lane
  rw [xor_packLane_left st1 blk1 off k hoff hk, xor_packLane_left st0 blk0 off k hoff hk]

private theorem lane_xor_right (st0 st1 : KeccakState) (blk0 blk1 : List (BitVec 8))
    (off k : Nat) (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    (st1.getD k 0#64 ^^^ packLane64 blk1 off) ++ (st0.getD k 0#64 ^^^ packLane64 blk0 off) =
      keccak2Lane (keccakXorRate17 st0 blk0) (keccakXorRate17 st1 blk1) k := by
  unfold keccak2Lane
  rw [xor_packLane_right st1 blk1 off k hoff hk, xor_packLane_right st0 blk0 off k hoff hk]

private theorem lane_xor_ge (st0 st1 : KeccakState) (blk0 blk1 : List (BitVec 8))
    (hs0 : st0.size ≤ 25) (hs1 : st1.size ≤ 25) (k : Nat) (hk : 17 ≤ k := by decide) :
    st1.getD k 0#64 ++ st0.getD k 0#64 =
      keccak2Lane (keccakXorRate17 st0 blk0) (keccakXorRate17 st1 blk1) k := by
  unfold keccak2Lane
  rw [keccakXorRate17_getD_ge st1 blk1 hk hs1, keccakXorRate17_getD_ge st0 blk0 hk hs0]

private theorem cells128_entails_memRegion
    (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    (((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗ (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
      ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗ (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
     (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗ (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
      ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗ (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15))))) ⊢
      memRegion a 128 := by
  rw [pointsTo64_16_eq_bytes]
  have h := pointsToBytes_entails_memRegion a
    (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
      unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7 ++
      unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
      unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15)
  have hlen : (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
      unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7 ++
      unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
      unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15).length = 128 := by
    simp only [List.length_append, unpackLane64_length]
  rwa [hlen] at h

private theorem shift16_eq (ptr : BitVec 64) (off : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    ((((ptr + BitVec.ofNat 64 off) ↦₆₄ w0) ∗ ((ptr + BitVec.ofNat 64 (off + 8)) ↦₆₄ w1)) ∗
     (((ptr + BitVec.ofNat 64 (off + 16)) ↦₆₄ w2) ∗ ((ptr + BitVec.ofNat 64 (off + 24)) ↦₆₄ w3))) ∗
    ((((ptr + BitVec.ofNat 64 (off + 32)) ↦₆₄ w4) ∗ ((ptr + BitVec.ofNat 64 (off + 40)) ↦₆₄ w5)) ∗
     (((ptr + BitVec.ofNat 64 (off + 48)) ↦₆₄ w6) ∗ ((ptr + BitVec.ofNat 64 (off + 56)) ↦₆₄ w7))) ∗
    (((((ptr + BitVec.ofNat 64 (off + 64)) ↦₆₄ w8) ∗ ((ptr + BitVec.ofNat 64 (off + 72)) ↦₆₄ w9)) ∗
      (((ptr + BitVec.ofNat 64 (off + 80)) ↦₆₄ w10) ∗ ((ptr + BitVec.ofNat 64 (off + 88)) ↦₆₄ w11))) ∗
     ((((ptr + BitVec.ofNat 64 (off + 96)) ↦₆₄ w12) ∗ ((ptr + BitVec.ofNat 64 (off + 104)) ↦₆₄ w13)) ∗
      (((ptr + BitVec.ofNat 64 (off + 112)) ↦₆₄ w14) ∗ ((ptr + BitVec.ofNat 64 (off + 120)) ↦₆₄ w15)))) ⊢
      memRegion (ptr + BitVec.ofNat 64 off) 128 := by
  let b := ptr + BitVec.ofNat 64 off
  have hk (k : Nat) : ptr + BitVec.ofNat 64 (off + k) = b + BitVec.ofNat 64 k := by
    dsimp [b]; rw [BitVec.ofNat_add]; bv_omega
  rw [hk 8, hk 16, hk 24, hk 32, hk 40, hk 48, hk 56, hk 64, hk 72, hk 80, hk 88, hk 96, hk 104,
      hk 112, hk 120, ← sepConj_assoc]
  exact cells128_entails_memRegion b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

private theorem rest272_entails_memRegion (ptr : BitVec 64) (st0 st1 : KeccakState) :
    (Keccak2Q2Mem ptr st0 st1 ∗ Keccak2Q3Mem ptr st0 st1) ∗
      Keccak2Vec16Mem ptr st0 st1 ∗ Keccak2Cap8Mem ptr st0 st1 ⊢
      memRegion (ptr + 128#64) 272 := by
  have hq23 : Keccak2Q2Mem ptr st0 st1 ∗ Keccak2Q3Mem ptr st0 st1 ⊢ memRegion (ptr + 128#64) 128 := by
    unfold Keccak2Q2Mem Keccak2Q3Mem
    simpa only [sepConj_assoc] using shift16_eq ptr 128 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hv16 : Keccak2Vec16Mem ptr st0 st1 ⊢ memRegion (ptr + 256#64) 16 := by
    unfold Keccak2Vec16Mem
    rw [memRegion_split (ptr + 256#64) 8 8 (by decide), show ptr + 264#64 = (ptr + 256#64) + 8#64 by bv_omega]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have hc8 : Keccak2Cap8Mem ptr st0 st1 ⊢ memRegion (ptr + 272#64) 128 := by
    unfold Keccak2Cap8Mem
    simpa only [sepConj_assoc] using shift16_eq ptr 272 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [memRegion_split (ptr + 128#64) 128 144 (by decide),
      show (ptr + 128#64) + 128#64 = ptr + 256#64 by bv_omega,
      memRegion_split (ptr + 256#64) 16 128 (by decide),
      show (ptr + 256#64) + 16#64 = ptr + 272#64 by bv_omega]
  exact sepConj_mono hq23 (sepConj_mono hv16 hc8)

private theorem padBufs_entails_memRegion288 (sp : BitVec 64)
    (blk0 blk1 : List (BitVec 8)) (h0 : blk0.length = 136) (h1 : blk1.length = 136) :
    ((sp + 592#64) ↦ₛ blk0) ∗ memRegion (sp + 728#64) 8 ∗
      ((sp + 736#64) ↦ₛ blk1) ∗ memRegion (sp + 872#64) 8 ⊢ memRegion (sp + 592#64) 288 := by
  have h288 : memRegion (sp + 592#64) 288 =
      memRegion (sp + 592#64) 136 ∗ memRegion (sp + 728#64) 8 ∗
        memRegion (sp + 736#64) 136 ∗ memRegion (sp + 872#64) 8 := by
    rw [memRegion_split (sp + 592#64) 136 152 (by decide),
        show (sp + 592#64) + 136#64 = sp + 728#64 by bv_omega,
        memRegion_split (sp + 728#64) 8 144 (by decide),
        show (sp + 728#64) + 8#64 = sp + 736#64 by bv_omega,
        memRegion_split (sp + 736#64) 136 8 (by decide),
        show (sp + 736#64) + 136#64 = sp + 872#64 by bv_omega]
  have e0 : ((sp + 592#64) ↦ₛ blk0) ⊢ memRegion (sp + 592#64) 136 := by
    simpa only [h0] using pointsToBytes_entails_memRegion (sp + 592#64) blk0
  have e1 : ((sp + 736#64) ↦ₛ blk1) ⊢ memRegion (sp + 736#64) 136 := by
    simpa only [h1] using pointsToBytes_entails_memRegion (sp + 736#64) blk1
  rw [h288]
  exact sepConj_mono e0 (sepConj_mono (Entails.refl _) (sepConj_mono e1 (Entails.refl _)))

/-! ## Sub-segment proofs (`[0x0434 → 0x05e4]`) -/

private def PreMemcpy0Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2ShakeArgs) : Prop :=
  s.status = .Running ∧ s.spAligned = true ∧ s.sp = sp ∧ s.readReg64 .fp = sp + 944#64 ∧
  s.readReg64 .x27 = rcBase ∧ s.readReg64 .x26 = BitVec.ofNat 64 (a.in0.length % 136) ∧
  s.readReg64 .x25 = BitVec.ofNat 64 (a.in0.length / 136 * 136) ∧ s.readReg64 .x24 = a.slicesPtr ∧
  s.readReg64 .x23 = BitVec.ofNat 64 a.in0.length ∧ s.readReg64 .x22 = a.out0 ∧
  s.readReg64 .x21 = a.out1 ∧ s.readReg64 .x20 = BitVec.ofNat 64 a.outLen ∧
  s.readReg64 .x19 = sp + 592#64 ∧ s.readReg64 .x0 = sp + 592#64 ∧
  s.readReg64 .x1 = a.ptr0 + BitVec.ofNat 64 (a.in0.length / 136 * 136) ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (a.in0.length % 136)

private def PreMemcpy1Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2ShakeArgs) : Prop :=
  s.status = .Running ∧ s.spAligned = true ∧ s.sp = sp ∧ s.readReg64 .fp = sp + 944#64 ∧
  s.readReg64 .x28 = 31#64 ∧ s.readReg64 .x27 = rcBase ∧
  s.readReg64 .x26 = BitVec.ofNat 64 (a.in1.length % 136) ∧ s.readReg64 .x23 = sp + 736#64 ∧
  s.readReg64 .x22 = a.out0 ∧ s.readReg64 .x21 = a.out1 ∧
  s.readReg64 .x20 = BitVec.ofNat 64 a.outLen ∧ s.readReg64 .x0 = sp + 736#64 ∧
  s.readReg64 .x1 = a.ptr1 + BitVec.ofNat 64 (a.in1.length / 136 * 136) ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (a.in1.length % 136)

private def Pad1ReadyRegs (s : State) (sp rcBase : BitVec 64) (a : Keccak2ShakeArgs) : Prop :=
  s.status = .Running ∧ s.spAligned = true ∧ s.sp = sp ∧ s.readReg64 .fp = sp + 944#64 ∧
  s.readReg64 .x28 = 31#64 ∧ s.readReg64 .x27 = rcBase ∧
  s.readReg64 .x26 = BitVec.ofNat 64 (a.in1.length % 136) ∧ s.readReg64 .x23 = sp + 736#64 ∧
  s.readReg64 .x22 = a.out0 ∧ s.readReg64 .x21 = a.out1 ∧
  s.readReg64 .x20 = BitVec.ofNat 64 a.outLen

private theorem split288_buf0_eq (sp : BitVec 64) :
    memRegion (sp + 592#64) 288 =
      memRegion (sp + 592#64) 128 ∗ memRegion (sp + 720#64) 8 ∗ memRegion (sp + 728#64) 152 := by
  rw [memRegion_split (sp + 592#64) 128 160 (by decide),
      show (sp + 592#64) + 128#64 = sp + 720#64 by bv_omega,
      memRegion_split (sp + 720#64) 8 152 (by decide),
      show (sp + 720#64) + 8#64 = sp + 728#64 by bv_omega]

private theorem split152_buf1_eq (sp : BitVec 64) :
    memRegion (sp + 728#64) 152 =
      memRegion (sp + 728#64) 8 ∗ memRegion (sp + 736#64) 128 ∗
        memRegion (sp + 864#64) 8 ∗ memRegion (sp + 872#64) 8 := by
  rw [memRegion_split (sp + 728#64) 8 144 (by decide),
      show (sp + 728#64) + 8#64 = sp + 736#64 by bv_omega,
      memRegion_split (sp + 736#64) 128 16 (by decide),
      show (sp + 736#64) + 128#64 = sp + 864#64 by bv_omega,
      memRegion_split (sp + 864#64) 8 8 (by decide),
      show (sp + 864#64) + 8#64 = sp + 872#64 by bv_omega]

private theorem seg_0434_to_046c [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hin0 : a.in0.length < 2 ^ 32)
    (s0 : State) (sp rcBase : BitVec 64) (hsp_eq : sp = s0.sp - 1040#64) (s : State) (F : SepProp)
    (hpc : s.pc = b + 0x0434#64) (hregs : PostAbsorbRegs s s0 rcBase a) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x046c#64) s
      (memRegion (sp + 592#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)
      (sepPost (fun sm => PreMemcpy0Regs sm sp rcBase a)
        (memRegion (sp + 592#64) (a.in0.length % 136) ∗
          (((sp + 592#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
            List.replicate (136 - a.in0.length % 136) 0#8) ∗
          memRegion (sp + 728#64) 152 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx27, hx25, hx24, hx23, hx22, hx21, hx20⟩
  have hsp' : s.sp = sp := hsp.trans hsp_eq.symm
  have hfp' : s.readReg64 .fp = sp + 944#64 := hx29.trans (by subst hsp_eq; bv_omega)
  clear hsp hx29 hsp_eq
  rw [split288_buf0_eq sp]
  refine memRegion128_cells (sp + 592#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15 => ?_
  refine SepWP.memRegion8_cell (sp + 720#64) fun _c16 => ?_
  unfold Keccak2SlicesRO
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      Eq.trans (by wp_norm_lhs) (sub_div_mul136_bv a.in0.length hin0),
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      Eq.trans (by wp_norm_lhs) (sub_div_mul136_bv a.in0.length hin0)⟩, ?_⟩
    have hbuf0 :
        ((((((sp + 592#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 8#64) ↦₆₄ 0#64)) ∗
            ((((sp + 592#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 24#64) ↦₆₄ 0#64))) ∗
           (((((sp + 592#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 40#64) ↦₆₄ 0#64)) ∗
            ((((sp + 592#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 56#64) ↦₆₄ 0#64)))) ∗
          ((((((sp + 592#64) + 64#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 72#64) ↦₆₄ 0#64)) ∗
            ((((sp + 592#64) + 80#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 88#64) ↦₆₄ 0#64))) ∗
           (((((sp + 592#64) + 96#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 104#64) ↦₆₄ 0#64)) ∗
            ((((sp + 592#64) + 112#64) ↦₆₄ 0#64) ∗ (((sp + 592#64) + 120#64) ↦₆₄ 0#64))))) ∗
         ((sp + 720#64) ↦₆₄ 0#64) ⊢
        memRegion (sp + 592#64) (a.in0.length % 136) ∗
          (((sp + 592#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
            List.replicate (136 - a.in0.length % 136) 0#8) := by
      rw [show sp + 720#64 = (sp + 592#64) + 128#64 by clear * -; bv_omega,
          zero17_eq_replicate136 (sp + 592#64)]
      exact replicate136_entails_split (sp + 592#64) (a.in0.length % 136)
        (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
    exact entails_sub hbuf0 (by sep_frame) (by sep_frame)

private theorem seg_046c_to_04bc [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64) (s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x046c#64) (hregs : PreMemcpy0Regs s sp rcBase a) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x04bc#64) s
      (memRegion (sp + 592#64) (a.in0.length % 136) ∗
        (((sp + 592#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) ∗
        memRegion (sp + 728#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F)
      (sepPost (fun sm => PreMemcpy1Regs sm sp rcBase a)
        (((sp + 592#64) ↦ₛ keccakLastBlock 136 0x1f#8 a.in0) ∗
          memRegion (sp + 728#64) 8 ∗
          memRegion (sp + 736#64) (a.in1.length % 136) ∗
          (((sp + 736#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
            List.replicate (136 - a.in1.length % 136) 0#8) ∗
          memRegion (sp + 872#64) 8 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx27, hx26, hx25, hx24, hx23, hx22, hx21,
    hx20, hx19, hx0, hx1, hx2⟩
  let byteOff := a.in0.length / 136 * 136
  let tail0 := a.in0.drop byteOff
  have hrem_lt : a.in0.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail0_len : tail0.length = a.in0.length % 136 := by
    dsimp [tail0, byteOff]; rw [List.length_drop]; have := Nat.div_add_mod a.in0.length 136; omega
  have htail0_u64 : tail0.length < 2 ^ 64 := by omega
  have hx2_nat : (s.readReg64 .x2).toNat = tail0.length := by
    rw [hx2, htail0_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_fn : Unit → a.in0.length = a.in1.length := fun _ => hlen
  clear hlen
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion (sp + 592#64) tail0.length ∗
        (((sp + 592#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) ∗
        memRegion (sp + 728#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0.take byteOff) ∗ ((a.ptr0 + BitVec.ofNat 64 byteOff) ↦ᵣ tail0) ∗ F by
      rw [htail0_len, pointsToBytesRO_take_drop a.ptr0 a.in0 byteOff (Nat.div_mul_le_self _ _)]
      sep_frame) ?_
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 592#64, a.ptr0 + BitVec.ofNat 64 byteOff, tail0)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hsp'  : sf.sp = sp := hsp_sf.trans hsp
  have hfp'  : sf.readReg64 .fp = sp + 944#64 :=
    (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hfp
  have hx27' : sf.readReg64 .x27 = rcBase :=
    (by assumption : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
  have hx26' : sf.readReg64 .x26 = BitVec.ofNat 64 (a.in0.length % 136) :=
    (by assumption : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)).trans hx26
  have hx25' : sf.readReg64 .x25 = BitVec.ofNat 64 (a.in0.length / 136 * 136) :=
    (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
  have hx24' : sf.readReg64 .x24 = a.slicesPtr :=
    (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
  have hx23' : sf.readReg64 .x23 = BitVec.ofNat 64 a.in0.length :=
    (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
  have hx22' : sf.readReg64 .x22 = a.out0 :=
    (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
  have hx21' : sf.readReg64 .x21 = a.out1 :=
    (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
  have hx20' : sf.readReg64 .x20 = BitVec.ofNat 64 a.outLen :=
    (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
  have hx19' : sf.readReg64 .x19 = sp + 592#64 :=
    (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19
  have hrejoin_in0 :
      (a.ptr0 ↦ᵣ a.in0.take byteOff) ∗ ((a.ptr0 + BitVec.ofNat 64 byteOff) ↦ᵣ tail0) =
        (a.ptr0 ↦ᵣ a.in0) :=
    (pointsToBytesRO_take_drop a.ptr0 a.in0 byteOff (Nat.div_mul_le_self _ _)).symm
  have hrejoin_buf0 :
      ((sp + 592#64) ↦ₛ tail0) ∗
        (((sp + 592#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) =
        ((sp + 592#64) ↦ₛ (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)) := by
    rw [← htail0_len]
    exact (pointsToBytes_append (sp + 592#64) tail0 (List.replicate (136 - tail0.length) 0#8)).symm
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp + 592#64) ↦ₛ (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)) ∗
        memRegion (sp + 728#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F by
      rw [← hrejoin_buf0, ← hrejoin_in0]; sep_frame) ?_
  rw [split152_buf1_eq sp]
  refine memRegion128_cells (sp + 736#64) (by sep_focus)
    fun _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 _d8 _d9 _d10 _d11 _d12 _d13 _d14 _d15 => ?_
  refine SepWP.memRegion8_cell (sp + 864#64) fun _d16 => ?_
  have hbuf0_0_len : (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8).length = 136 := by
    simp [htail0_len]; omega
  have hbuf0_1_len :
      (ByteSlice.write8 (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)
        (a.in0.length % 136) 0x1f#8).length = 136 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf0_0_len]; omega), hbuf0_0_len]
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · exfalso; have hlen := hlen_fn (); simp [hlen, BitVec.ult] at hbr
  · wp_steps
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · rw [sepPost_apply]
      refine ⟨⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()]),
        Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega),
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega),
        Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()]),
        Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()])⟩, ?_⟩
      have hbuf1 :
          ((((((sp + 736#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 8#64) ↦₆₄ 0#64)) ∗
              ((((sp + 736#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 24#64) ↦₆₄ 0#64))) ∗
             (((((sp + 736#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 40#64) ↦₆₄ 0#64)) ∗
              ((((sp + 736#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 56#64) ↦₆₄ 0#64)))) ∗
            ((((((sp + 736#64) + 64#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 72#64) ↦₆₄ 0#64)) ∗
              ((((sp + 736#64) + 80#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 88#64) ↦₆₄ 0#64))) ∗
             (((((sp + 736#64) + 96#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 104#64) ↦₆₄ 0#64)) ∗
              ((((sp + 736#64) + 112#64) ↦₆₄ 0#64) ∗ (((sp + 736#64) + 120#64) ↦₆₄ 0#64))))) ∗
           ((sp + 864#64) ↦₆₄ 0#64) ⊢
          memRegion (sp + 736#64) (a.in1.length % 136) ∗
            (((sp + 736#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
              List.replicate (136 - a.in1.length % 136) 0#8) := by
        rw [show sp + 864#64 = (sp + 736#64) + 128#64 by clear * -; bv_omega,
            zero17_eq_replicate136 (sp + 736#64)]
        exact replicate136_entails_split (sp + 736#64) (a.in1.length % 136)
          (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      simp only [orr80_truncate8]
      rw [padBuf136_31_eq_lastBlock a.in0]
      exact entails_sub hbuf1 (by sep_frame) (by sep_frame)

private theorem seg_04bc_to_04c0 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (sp rcBase : BitVec 64) (s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x04bc#64) (hregs : PreMemcpy1Regs s sp rcBase a) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x04c0#64) s
      (((sp + 592#64) ↦ₛ keccakLastBlock 136 0x1f#8 a.in0) ∗
        memRegion (sp + 728#64) 8 ∗
        memRegion (sp + 736#64) (a.in1.length % 136) ∗
        (((sp + 736#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) ∗
        memRegion (sp + 872#64) 8 ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (sepPost (fun sm => Pad1ReadyRegs sm sp rcBase a)
        (((sp + 592#64) ↦ₛ keccakLastBlock 136 0x1f#8 a.in0) ∗
          memRegion (sp + 728#64) 8 ∗
          ((sp + 736#64) ↦ₛ (a.in1.drop (a.in1.length / 136 * 136) ++
            List.replicate (136 - a.in1.length % 136) 0#8)) ∗
          memRegion (sp + 872#64) 8 ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx28, hx27, hx26, hx23, hx22, hx21, hx20, hx0, hx1, hx2⟩
  let byteOff := a.in1.length / 136 * 136
  let tail1 := a.in1.drop byteOff
  have hrem_lt : a.in1.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail1_len : tail1.length = a.in1.length % 136 := by
    dsimp [tail1, byteOff]; rw [List.length_drop]; have := Nat.div_add_mod a.in1.length 136; omega
  have htail1_u64 : tail1.length < 2 ^ 64 := by omega
  have hx2_nat : (s.readReg64 .x2).toNat = tail1.length := by
    rw [hx2, htail1_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp + 592#64) ↦ₛ keccakLastBlock 136 0x1f#8 a.in0) ∗
        memRegion (sp + 728#64) 8 ∗ memRegion (sp + 736#64) tail1.length ∗
        (((sp + 736#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) ∗
        memRegion (sp + 872#64) 8 ∗
        (a.ptr1 ↦ᵣ a.in1.take byteOff) ∗ ((a.ptr1 + BitVec.ofNat 64 byteOff) ↦ᵣ tail1) ∗ F by
      rw [htail1_len, pointsToBytesRO_take_drop a.ptr1 a.in1 byteOff (Nat.div_mul_le_self _ _)]
      sep_frame) ?_
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 736#64, a.ptr1 + BitVec.ofNat 64 byteOff, tail1)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hsp'  : sf.sp = sp := hsp_sf.trans hsp
  have hfp'  : sf.readReg64 .fp = sp + 944#64 :=
    (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hfp
  have hx28' : sf.readReg64 .x28 = 31#64 :=
    (by assumption : sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)).trans hx28
  have hx27' : sf.readReg64 .x27 = rcBase :=
    (by assumption : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
  have hx26' : sf.readReg64 .x26 = BitVec.ofNat 64 (a.in1.length % 136) :=
    (by assumption : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)).trans hx26
  have hx23' : sf.readReg64 .x23 = sp + 736#64 :=
    (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
  have hx22' : sf.readReg64 .x22 = a.out0 :=
    (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
  have hx21' : sf.readReg64 .x21 = a.out1 :=
    (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
  have hx20' : sf.readReg64 .x20 = BitVec.ofNat 64 a.outLen :=
    (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
  have hrejoin_in1 :
      (a.ptr1 ↦ᵣ a.in1.take byteOff) ∗ ((a.ptr1 + BitVec.ofNat 64 byteOff) ↦ᵣ tail1) = (a.ptr1 ↦ᵣ a.in1) :=
    (pointsToBytesRO_take_drop a.ptr1 a.in1 byteOff (Nat.div_mul_le_self _ _)).symm
  have hrejoin_buf1 :
      ((sp + 736#64) ↦ₛ tail1) ∗
        (((sp + 736#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) =
        ((sp + 736#64) ↦ₛ (tail1 ++ List.replicate (136 - a.in1.length % 136) 0#8)) := by
    rw [← htail1_len]
    exact (pointsToBytes_append (sp + 736#64) tail1 (List.replicate (136 - tail1.length) 0#8)).symm
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    exact ⟨⟨by wp_norm_lhs, hsp_align_sf, hsp', hfp', hx28', hx27', hx26', hx23', hx22', hx21', hx20'⟩,
      by rw [← hrejoin_buf1, ← hrejoin_in1]; sep_frame⟩

set_option maxRecDepth 20000 in
private theorem seg_04c0_to_05e4 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (s0 : State) (sp rcBase : BitVec 64) (hsp_eq : sp = s0.sp - 1040#64)
    (st0 st1 : KeccakState) (hs0 : st0.size ≤ 25) (hs1 : st1.size ≤ 25)
    (F : SepProp) (s : State) (hpc : s.pc = b + 0x04c0#64) (hregs : Pad1ReadyRegs s sp rcBase a) :
    let blk0 := keccakLastBlock 136 0x1f#8 a.in0
    let blk1 := keccakLastBlock 136 0x1f#8 a.in1
    let xst0 := keccakXorRate17 st0 blk0
    let xst1 := keccakXorRate17 st1 blk1
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x05e4#64) s
      (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗
        ((sp + 592#64) ↦ₛ blk0) ∗ memRegion (sp + 728#64) 8 ∗
        ((sp + 736#64) ↦ₛ (a.in1.drop (a.in1.length / 136 * 136) ++
          List.replicate (136 - a.in1.length % 136) 0#8)) ∗
        memRegion (sp + 872#64) 8 ∗ F)
      (fun sm Pm =>
        TailPermuteEntryRegs sm s0 rcBase a ∧ P2RoundRegs sm xst0 xst1 ∧
        ∃ s16 s32 s48 s64 s80 s96 s112,
          Pm ⊢ Spill11 sp s16 s32 s48 s64 s80 s96 s112
            (keccak2Lane xst0 xst1 2) (keccak2Lane xst0 xst1 3)
            (keccak2Lane xst0 xst1 6) (keccak2Lane xst0 xst1 4) ∗
            memRegion (sp + 192#64) 400 ∗ memRegion (sp + 592#64) 288 ∗ F) := by
  intro blk0 blk1 xst0 xst1
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx28, hx27, hx26, hx23, hx22, hx21, hx20⟩
  have hsp_eq_fn : Unit → sp = s0.sp - 1040#64 := fun _ => hsp_eq
  clear hsp_eq
  have hblk0_len : blk0.length = 136 := keccakLastBlock_length 136 0x1f#8 a.in0
  have hblk1_len : blk1.length = 136 := keccakLastBlock_length 136 0x1f#8 a.in1
  have hrem_lt : a.in1.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail1_len : (a.in1.drop (a.in1.length / 136 * 136)).length = a.in1.length % 136 := by
    rw [List.length_drop]; have := Nat.div_add_mod a.in1.length 136; omega
  have hbuf1_0_len :
      (a.in1.drop (a.in1.length / 136 * 136) ++
        List.replicate (136 - a.in1.length % 136) 0#8).length = 136 := by
    simp [htail1_len]; omega
  have hbuf1_1_len :
      (ByteSlice.write8
        (a.in1.drop (a.in1.length / 136 * 136) ++
          List.replicate (136 - a.in1.length % 136) 0#8)
        (a.in1.length % 136) 0x1f#8).length = 136 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf1_0_len]; omega), hbuf1_0_len]
  have hread1 (off : Nat) (hoff : off + 8 ≤ 135 := by decide) :
      ByteSlice.readLE
        (ByteSlice.write8
          (a.in1.drop (a.in1.length / 136 * 136) ++
            List.replicate (136 - a.in1.length % 136) 0#8)
          (a.in1.length % 136) 0x1f#8) off 8 = packLane64 blk1 off := by
    rw [readLE_write8_135_lt _ _ off hoff hbuf1_1_len,
        padBuf136_31_eq_lastBlock a.in1, readLE_8_eq_packLane64]
  refine memRegion176_to_spill11 sp (by sep_focus)
    fun s16 s32 s48 s64 s80 s96 s112 _s128 _s144 _s160 _s176 => ?_
  unfold Spill11 Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
    Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
  wp_steps 14
  simp only [orr80_truncate8]
  rw [padBuf136_31_eq_lastBlock a.in1, show keccakLastBlock 136 0x1f#8 a.in1 = blk1 from rfl]
  wp_steps 46
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
  · refine ⟨⟨by wp_norm_lhs, by wp_norm_lhs, Eq.trans (by wp_norm_lhs) (hsp_eq_fn ()),
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        Eq.trans (by wp_norm_lhs) (by have h := hsp_eq_fn (); clear * - h; subst h; bv_omega)⟩,
      ⟨Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 24),
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 19),
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 23),
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 20),
       by refine Eq.trans (by wp_norm_lhs) ?_; rw [hread1 0, readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 0 0,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 56 7,
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 18),
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 72 9,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 112 14,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 104 13,
       by refine Eq.trans (by wp_norm_lhs) ?_; rw [hread1 8, readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 8 1,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 96 12,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 88 11,
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 17),
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 64 8,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 80 10,
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 22),
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_left st0 st1 blk0 blk1 128 16,
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 120 15,
       Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 21),
       by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]; exact lane_xor_right st0 st1 blk0 blk1 40 5⟩,
      s16, s32, s48, s64, s80, s96, s112, ?_⟩
    rw [hread1 16, hread1 24]
    simp only [readLE_8_eq_packLane64]
    rw [xor_packLane_left st0 blk0 16 2, xor_packLane_left st1 blk1 16 2,
        xor_packLane_right st0 blk0 24 3, xor_packLane_right st1 blk1 24 3,
        xor_packLane_left st0 blk0 48 6, xor_packLane_left st1 blk1 48 6,
        xor_packLane_left st0 blk0 32 4, xor_packLane_left st1 blk1 32 4]
    dsimp only [keccak2Lane]
    simp only [extractLsb_lo_append, extractLsb_hi_append]
    rw [memRegion_split (sp + 192#64) 128 272 (by decide)]
    refine entails_sub (cells128_entails_memRegion (sp + 192#64) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_frame) ?_
    refine entails_sub (rest272_entails_memRegion (sp + 192#64) st0 st1)
      (by unfold Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem; sep_frame) ?_
    exact entails_sub (padBufs_entails_memRegion288 sp blk0 blk1 hblk0_len hblk1_len)
      (by sep_frame) (by sep_frame)

public section
section
attribute [local irreducible] Keccak2Mem Keccak2SlicesRO Spill11

/-- Full tail `memcpy` + `SHAKE-256` padding + 17-lane XOR segment (`[0x0434 → 0x05e4]`). -/
theorem tail_pad_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen : a.in0.length = a.in1.length)
    (s0 : State) (rcBase : BitVec 64) (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x0434#64)
    (hregs : PostAbsorbRegs s s0 rcBase a)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let sp := s0.sp - 1040#64
    let nBlocks := a.in0.length / 136
    let st0 := keccakAbsorbPrefix17 a.in0 nBlocks
    let st1 := keccakAbsorbPrefix17 a.in1 nBlocks
    let xst0 := keccakXorRate17 st0 (keccakLastBlock 136 0x1f#8 a.in0)
    let xst1 := keccakXorRate17 st1 (keccakLastBlock 136 0x1f#8 a.in1)
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x05e4#64) s
      (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗
        memRegion (sp + 592#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (fun sm Pm =>
        TailPermuteEntryRegs sm s0 rcBase a ∧ P2RoundRegs sm xst0 xst1 ∧
        ∃ s16 s32 s48 s64 s80 s96 s112,
          Pm ⊢ Spill11 sp s16 s32 s48 s64 s80 s96 s112
            (keccak2Lane xst0 xst1 2) (keccak2Lane xst0 xst1 3)
            (keccak2Lane xst0 xst1 6) (keccak2Lane xst0 xst1 4) ∗
            memRegion (sp + 192#64) 400 ∗ memRegion (sp + 592#64) 288 ∗
            Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
            (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) := by
  intro sp nBlocks st0 st1 xst0 xst1
  have hs0 : st0.size ≤ 25 := Nat.le_of_eq (keccakAbsorbPrefix17_size a.in0 nBlocks)
  have hs1 : st1.size ≤ 25 := Nat.le_of_eq (keccakAbsorbPrefix17_size a.in1 nBlocks)
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion (sp + 592#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) by sep_frame) ?_
  refine sepWP_seq_cl hcl
    (seg_0434_to_046c b hb hbase a hin0 s0 sp rcBase rfl s
      (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) hpc hregs) ?_
  intro s1 P1 hpc1 _ hcl1 hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨hregs1, hP1⟩
  have hwp1 := seg_046c_to_04bc b hb hbase a hlen sp rcBase s1
    (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
    hcl1 hpc1 hregs1
  refine (fun h h1 => SepWP.weaken_pre h1 h) (sepWP_seq_cl hcl1 hwp1 ?_)
    (Entails.trans hP1 (by sep_frame))
  intro s2 P2 hpc2 _ hcl2 hpost2
  rw [sepPost_apply] at hpost2
  rcases hpost2 with ⟨hregs2, hP2⟩
  have hwp2 := seg_04bc_to_04c0 b hb hbase a sp rcBase s2
    (memRegion (sp + 16#64) 176 ∗ Keccak2Mem (sp + 192#64) st0 st1 ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ F) hcl2 hpc2 hregs2
  refine (fun h h2 => SepWP.weaken_pre h2 h) (sepWP_seq_cl hcl2 hwp2 ?_)
    (Entails.trans hP2 (by sep_frame))
  intro s3 P3 hpc3 _ _ hpost3
  rw [sepPost_apply] at hpost3
  rcases hpost3 with ⟨hregs3, hP3⟩
  have hwp3 := seg_04c0_to_05e4 b hb hbase a s0 sp rcBase rfl st0 st1 hs0 hs1
    (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) s3 hpc3 hregs3
  refine (fun h h3 => SepWP.weaken_pre h3 h) (SepWP.mono hwp3 ?_)
    (Entails.trans hP3 (by sep_frame))
  intro sf Pf _ _ ⟨hregsf, hrrf, s16, s32, s48, s64, s80, s96, s112, hPf⟩
  exact ⟨hregsf, hrrf, s16, s32, s48, s64, s80, s96, s112, Entails.trans hPf (by sep_frame)⟩

end
end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.TailPad
