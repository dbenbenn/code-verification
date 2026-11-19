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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B02` (`keccak2::<136, 6>`): tail `memcpy`, `SHA3-256` padding, and 17-lane XOR

Proof of segment `[0x042c → 0x05e4]` of `mlkemBlk02`:
- `[0x042c → 0x0464]`: zeroes `buf0` (`[sp + 576, sp + 712)`) and prepares `B28` `memcpy` of
  the `in0` tail.
- `[0x0464 → 0x04b4]`: calls `blk28_memcpyRO_ok` for the `in0` tail, applies `0x06`/`0x80`
  `SHA3-256` padding to `buf0` (`keccakLastBlock 136 0x06#8 a.in0`), zeroes `buf1`
  (`[sp + 720, sp + 856)`), and shows the slice-bounds panic branch `b.hi +0x0938` is not taken
  (`in0.length = in1.length`).
- `[0x04b4 → 0x04b8]`: calls `blk28_memcpyRO_ok` for the `in1` tail.
- `[0x04b8 → 0x05e4]`: applies `0x06`/`0x80` `SHA3-256` padding to `buf1` and interleaves/XORs
  all 17 64-bit rate lanes into `Loop2Regs` and `Loop2SpillMem` at loop 2 header `+0x05e4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPadXor

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2FixedArgs
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
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
  keccakXorRate17_getD_lt
  pointsToBytesRO_take_drop
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorbPrefix17_size
  keccakLastBlock
  keccakLastBlock_length
  keccakPadBuf_eq_lastBlock
  memRegion128_cells
  memRegion64_cells
  pointsTo64_16_eq_bytes
  pointsTo64_eq_unpackLane64
  readLE_8_eq_packLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  Loop2Regs
  Loop2SpillMem
  blk02_code_eq
  blk02_tree_size
  blkLib02
  blkPC02
  blkPl02
  blkPlaceable02
  blkTree02
  entails_sub
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase (
  cells128_entails_memRegion
  spAligned_of_sp_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb (
  TailEntryRegs
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x042c → 0x05e0]
end

@[local simp, local arm64_norm, local wp_norm]
private theorem blkPl02_ρ [MlKemPlacement] (sym : String) :
    blkPl02.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

public section

/-- Scalar register state at `+0x05e4` entering the 24-round tail `keccak_f1600` loop. -/
structure Loop2EntryRegs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx8       : s.readReg64 .x8 = 0#64
  hx9       : s.readReg64 .x9 = sp + 208#64
  hx19      : s.readReg64 .x19 = a.out1
  hx20      : s.readReg64 .x20 = a.out0
  hx25      : s.readReg64 .x25 = rcBase
  hfp       : s.readReg64 .fp = sp + 928#64

end

/-! ## Arithmetic, pad-buffer, and lane-XOR helpers -/

private theorem mul136_shift_bv (x : BitVec 64) :
    (x + (x <<< 4)) <<< 3 = x * 136#64 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
private theorem mul136_ofNat (k : Nat) :
    (BitVec.ofNat 64 k + (BitVec.ofNat 64 k <<< 4)) <<< 3 = BitVec.ofNat 64 (k * 136) := by
  rw [mul136_shift_bv, show (136#64 : BitVec 64) = BitVec.ofNat 64 136 from rfl, ← BitVec.ofNat_mul]

private theorem sub_div_mul136_bv (n : Nat) (_hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (n / 136 * 136) = BitVec.ofNat 64 (n % 136) := by
  have h : n = n / 136 * 136 + n % 136 := by
    have := Nat.div_add_mod n 136
    omega
  conv_lhs =>
    rw [show BitVec.ofNat 64 n = BitVec.ofNat 64 (n / 136 * 136 + n % 136) from congrArg _ h]
  rw [BitVec.ofNat_add]
  bv_omega

private theorem orr80_truncate8 (v : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v ||| 549755814016#64) = v ||| 0x80#8 := by
  bv_bits

private theorem zero17_eq_replicate136 (a : BitVec 64) :
    ((((((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64)) ∗
        (((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 24#64) ↦₆₄ 0#64))) ∗
       ((((a + 32#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
        (((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 0#64)))) ∗
      (((((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 72#64) ↦₆₄ 0#64)) ∗
        (((a + 80#64) ↦₆₄ 0#64) ∗ ((a + 88#64) ↦₆₄ 0#64))) ∗
       ((((a + 96#64) ↦₆₄ 0#64) ∗ ((a + 104#64) ↦₆₄ 0#64)) ∗
        (((a + 112#64) ↦₆₄ 0#64) ∗ ((a + 120#64) ↦₆₄ 0#64))))) ∗
     ((a + 128#64) ↦₆₄ 0#64)) =
      (a ↦ₛ List.replicate 136 0#8) := by
  rw [pointsTo64_16_eq_bytes a 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
        0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64,
      pointsTo64_eq_unpackLane64 (a + 128#64) 0#64]
  have h128 :
      unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 =
        List.replicate 128 0#8 := rfl
  have h8 : unpackLane64 0#64 = List.replicate 8 0#8 := rfl
  have h136 : List.replicate 136 (0#8 : BitVec 8) =
      List.replicate 128 0#8 ++ List.replicate 8 0#8 := rfl
  rw [h128, h8, h136, pointsToBytes_append, List.length_replicate]

private theorem replicate136_entails_split (a : BitVec 64) (remLen : Nat) (hrem : remLen ≤ 136) :
    (a ↦ₛ List.replicate 136 0#8) ⊢
      memRegion a remLen ∗ ((a + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (136 - remLen) 0#8) := by
  have hrep : List.replicate 136 (0#8 : BitVec 8) =
      List.replicate remLen 0#8 ++ List.replicate (136 - remLen) 0#8 := by
    rw [← List.replicate_add, show remLen + (136 - remLen) = 136 by omega]
  rw [hrep, pointsToBytes_append, List.length_replicate]
  refine sepConj_mono ?_ (Entails.refl _)
  simpa [List.length_replicate] using
    pointsToBytes_entails_memRegion a (List.replicate remLen (0#8 : BitVec 8))

private theorem padBuf136_eq_lastBlock (msg : List (BitVec 8)) :
    let fullCount := msg.length / 136
    let remLen := msg.length % 136
    let tail := msg.drop (fullCount * 136)
    let buf0 := tail ++ List.replicate (136 - remLen) 0#8
    let buf1 := ByteSlice.write8 buf0 remLen 0x06#8
    ByteSlice.write8 buf1 135 (buf1.getD 135 0#8 ||| 0x80#8) =
      keccakLastBlock 136 0x06#8 msg :=
  keccakPadBuf_eq_lastBlock (rateBytes := 136) 0x06#8 msg (by decide) (by decide)

private theorem packLane64_pad1_before_80 (msg : List (BitVec 8)) (off : Nat)
    (hoff : off + 8 ≤ 64 := by decide) :
    let fullCount := msg.length / 136
    let remLen := msg.length % 136
    let tail := msg.drop (fullCount * 136)
    packLane64 (ByteSlice.write8 (tail ++ List.replicate (136 - remLen) 0#8) remLen 0x06#8) off =
      packLane64 (keccakLastBlock 136 0x06#8 msg) off := by
  intro fullCount remLen tail
  set buf0 := tail ++ List.replicate (136 - remLen) 0#8
  have htail_len : tail.length = remLen := by
    dsimp [tail, fullCount, remLen]
    rw [List.length_drop]
    have hdiv := Nat.div_add_mod msg.length 136
    omega
  have hrem_lt : remLen < 136 := Nat.mod_lt _ (by decide)
  have hlen0 : buf0.length = 136 := by
    simp only [buf0, List.length_append, List.length_replicate, htail_len]; omega
  set buf1 := ByteSlice.write8 buf0 remLen 0x06#8
  have hlen1 : buf1.length = 136 := by
    unfold buf1 ByteSlice.write8
    rw [ByteSlice.write_length buf0 [0x06#8] remLen (by simp [hlen0]; omega), hlen0]
  rw [← padBuf136_eq_lastBlock msg]
  change packLane64 buf1 off =
    packLane64 (ByteSlice.write8 buf1 135 (buf1.getD 135 0#8 ||| 0x80#8)) off
  unfold packLane64
  have g (j : Nat) (hj : j < 8) :
      buf1.getD (off + j) 0#8 =
        (ByteSlice.write8 buf1 135 (buf1.getD 135 0#8 ||| 0x80#8)).getD (off + j) 0#8 := by
    rw [ByteSlice.getD_write8 buf1 135 _ (off + j) 0#8 (by omega)]
    have hne : off + j ≠ 135 := by omega
    simp only [hne, ↓reduceIte]
  rw [show buf1.getD off 0#8 = buf1.getD (off + 0) 0#8 by simp,
      g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide),
      Nat.add_zero]


private theorem xor_packLane_left (s : KeccakState) (blk : List (BitVec 8)) (off k : Nat)
    (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    packLane64 blk off ^^^ s.getD k 0#64 = (keccakXorRate17 s blk).getD k 0#64 := by
  subst hoff
  rw [BitVec.xor_comm, keccakXorRate17_getD_lt s blk hk]

private theorem xor_packLane_right (s : KeccakState) (blk : List (BitVec 8)) (off k : Nat)
    (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    s.getD k 0#64 ^^^ packLane64 blk off = (keccakXorRate17 s blk).getD k 0#64 := by
  subst hoff
  exact (keccakXorRate17_getD_lt s blk hk).symm

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

private theorem padBufs_entails_memRegion288 (sp : BitVec 64)
    (blk0 blk1 : List (BitVec 8)) (h0 : blk0.length = 136) (h1 : blk1.length = 136) :
    ((sp + 576#64) ↦ₛ blk0) ∗ memRegion (sp + 712#64) 8 ∗
      ((sp + 720#64) ↦ₛ blk1) ∗ memRegion (sp + 856#64) 8 ⊢
      memRegion (sp + 576#64) 288 := by
  have h288 : memRegion (sp + 576#64) 288 =
      memRegion (sp + 576#64) 136 ∗ memRegion (sp + 712#64) 8 ∗
        memRegion (sp + 720#64) 136 ∗ memRegion (sp + 856#64) 8 := by
    rw [memRegion_split (sp + 576#64) 136 152 (by decide),
        show (sp + 576#64) + 136#64 = sp + 712#64 by bv_omega,
        memRegion_split (sp + 712#64) 8 144 (by decide),
        show (sp + 712#64) + 8#64 = sp + 720#64 by bv_omega,
        memRegion_split (sp + 720#64) 136 8 (by decide),
        show (sp + 720#64) + 136#64 = sp + 856#64 by bv_omega]
  have e0 : ((sp + 576#64) ↦ₛ blk0) ⊢ memRegion (sp + 576#64) 136 := by
    simpa only [h0] using pointsToBytes_entails_memRegion (sp + 576#64) blk0
  have e1 : ((sp + 720#64) ↦ₛ blk1) ⊢ memRegion (sp + 720#64) 136 := by
    simpa only [h1] using pointsToBytes_entails_memRegion (sp + 720#64) blk1
  rw [h288]
  exact sepConj_mono e0 (sepConj_mono (Entails.refl _) (sepConj_mono e1 (Entails.refl _)))

private theorem rest272_entails_memRegion (ptr : BitVec 64) (st0 st1 : KeccakState) :
    (Keccak2Q2Mem ptr st0 st1 ∗ Keccak2Q3Mem ptr st0 st1) ∗
      Keccak2Vec16Mem ptr st0 st1 ∗ Keccak2Cap8Mem ptr st0 st1 ⊢
      memRegion (ptr + 128#64) 272 := by
  have hq23 : Keccak2Q2Mem ptr st0 st1 ∗ Keccak2Q3Mem ptr st0 st1 ⊢
      memRegion (ptr + 128#64) 128 := by
    unfold Keccak2Q2Mem Keccak2Q3Mem
    let b := ptr + 128#64
    rw [show ptr + 136#64 = b + 8#64 by dsimp [b]; bv_omega,
        show ptr + 144#64 = b + 16#64 by dsimp [b]; bv_omega,
        show ptr + 152#64 = b + 24#64 by dsimp [b]; bv_omega,
        show ptr + 160#64 = b + 32#64 by dsimp [b]; bv_omega,
        show ptr + 168#64 = b + 40#64 by dsimp [b]; bv_omega,
        show ptr + 176#64 = b + 48#64 by dsimp [b]; bv_omega,
        show ptr + 184#64 = b + 56#64 by dsimp [b]; bv_omega,
        show ptr + 192#64 = b + 64#64 by dsimp [b]; bv_omega,
        show ptr + 200#64 = b + 72#64 by dsimp [b]; bv_omega,
        show ptr + 208#64 = b + 80#64 by dsimp [b]; bv_omega,
        show ptr + 216#64 = b + 88#64 by dsimp [b]; bv_omega,
        show ptr + 224#64 = b + 96#64 by dsimp [b]; bv_omega,
        show ptr + 232#64 = b + 104#64 by dsimp [b]; bv_omega,
        show ptr + 240#64 = b + 112#64 by dsimp [b]; bv_omega,
        show ptr + 248#64 = b + 120#64 by dsimp [b]; bv_omega]
    exact cells128_entails_memRegion b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hv16 : Keccak2Vec16Mem ptr st0 st1 ⊢ memRegion (ptr + 256#64) 16 := by
    unfold Keccak2Vec16Mem
    rw [memRegion_split (ptr + 256#64) 8 8 (by decide),
        show ptr + 264#64 = (ptr + 256#64) + 8#64 by bv_omega]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have hc8 : Keccak2Cap8Mem ptr st0 st1 ⊢ memRegion (ptr + 272#64) 128 := by
    unfold Keccak2Cap8Mem
    let b := ptr + 272#64
    rw [show ptr + 280#64 = b + 8#64 by dsimp [b]; bv_omega,
        show ptr + 288#64 = b + 16#64 by dsimp [b]; bv_omega,
        show ptr + 296#64 = b + 24#64 by dsimp [b]; bv_omega,
        show ptr + 304#64 = b + 32#64 by dsimp [b]; bv_omega,
        show ptr + 312#64 = b + 40#64 by dsimp [b]; bv_omega,
        show ptr + 320#64 = b + 48#64 by dsimp [b]; bv_omega,
        show ptr + 328#64 = b + 56#64 by dsimp [b]; bv_omega,
        show ptr + 336#64 = b + 64#64 by dsimp [b]; bv_omega,
        show ptr + 344#64 = b + 72#64 by dsimp [b]; bv_omega,
        show ptr + 352#64 = b + 80#64 by dsimp [b]; bv_omega,
        show ptr + 360#64 = b + 88#64 by dsimp [b]; bv_omega,
        show ptr + 368#64 = b + 96#64 by dsimp [b]; bv_omega,
        show ptr + 376#64 = b + 104#64 by dsimp [b]; bv_omega,
        show ptr + 384#64 = b + 112#64 by dsimp [b]; bv_omega,
        show ptr + 392#64 = b + 120#64 by dsimp [b]; bv_omega]
    exact cells128_entails_memRegion b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [memRegion_split (ptr + 128#64) 128 144 (by decide),
      show (ptr + 128#64) + 128#64 = ptr + 256#64 by bv_omega,
      memRegion_split (ptr + 256#64) 16 128 (by decide),
      show (ptr + 256#64) + 16#64 = ptr + 272#64 by bv_omega]
  exact sepConj_mono hq23 (sepConj_mono hv16 hc8)

/-! ## Sub-segment proofs (`[0x042c → 0x05e4]`) -/

private structure PreMemcpy0Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hfp       : s.readReg64 .fp = sp + 928#64
  hx27      : s.readReg64 .x27 = sp + 576#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 (a.in0.length % 136)
  hx23      : s.readReg64 .x23 = BitVec.ofNat 64 (a.in0.length / 136 * 136)
  hx22      : s.readReg64 .x22 = BitVec.ofNat 64 a.in0.length
  hx21      : s.readReg64 .x21 = a.slicesPtr
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1
  hx0       : s.readReg64 .x0 = sp + 576#64
  hx1       : s.readReg64 .x1 = a.ptr0 + BitVec.ofNat 64 (a.in0.length / 136 * 136)
  hx2       : s.readReg64 .x2 = BitVec.ofNat 64 (a.in0.length % 136)

private structure PreMemcpy1Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hfp       : s.readReg64 .fp = sp + 928#64
  hx26      : s.readReg64 .x26 = 6#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 (a.in1.length % 136)
  hx21      : s.readReg64 .x21 = sp + 720#64
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1
  hx0       : s.readReg64 .x0 = sp + 720#64
  hx1       : s.readReg64 .x1 = a.ptr1 + BitVec.ofNat 64 (a.in1.length / 136 * 136)
  hx2       : s.readReg64 .x2 = BitVec.ofNat 64 (a.in1.length % 136)

private structure Pad1ReadyRegs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hfp       : s.readReg64 .fp = sp + 928#64
  hx26      : s.readReg64 .x26 = 6#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 (a.in1.length % 136)
  hx21      : s.readReg64 .x21 = sp + 720#64
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1

private theorem split288_buf0_eq (sp : BitVec 64) :
    memRegion (sp + 576#64) 288 =
      memRegion (sp + 576#64) 128 ∗ memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 152 := by
  rw [memRegion_split (sp + 576#64) 128 160 (by decide),
      show (sp + 576#64) + 128#64 = sp + 704#64 by bv_omega,
      memRegion_split (sp + 704#64) 8 152 (by decide),
      show (sp + 704#64) + 8#64 = sp + 712#64 by bv_omega]

private theorem split152_buf1_eq (sp : BitVec 64) :
    memRegion (sp + 712#64) 152 =
      memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 128 ∗
        memRegion (sp + 848#64) 8 ∗ memRegion (sp + 856#64) 8 := by
  rw [memRegion_split (sp + 712#64) 8 144 (by decide),
      show (sp + 712#64) + 8#64 = sp + 720#64 by bv_omega,
      memRegion_split (sp + 720#64) 128 16 (by decide),
      show (sp + 720#64) + 128#64 = sp + 848#64 by bv_omega,
      memRegion_split (sp + 848#64) 8 8 (by decide),
      show (sp + 848#64) + 8#64 = sp + 856#64 by bv_omega]

/-- Step `[0x042c → 0x0464]`: zero `buf0` (`[sp + 576, sp + 712)`) and prepare `memcpy` of `in0` tail. -/
private theorem seg_042c_to_0464 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32)
    (sp rcBase : BitVec 64) (s : State) (F : SepProp)
    (hpc : s.pc = b + 0x042c#64)
    (hregs : TailEntryRegs s sp rcBase a) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x0464#64) s
      (memRegion (sp + 576#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)
      (sepPost
        (fun sm => PreMemcpy0Regs sm sp rcBase a)
        (memRegion (sp + 576#64) (a.in0.length % 136) ∗
          (((sp + 576#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
            List.replicate (136 - a.in0.length % 136) 0#8) ∗
          memRegion (sp + 712#64) 152 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx25, hx23, hx22, hx21, hx20, hx19⟩
  rw [split288_buf0_eq sp]
  refine memRegion128_cells (sp + 576#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15 => ?_
  refine SepWP.memRegion8_cell (sp + 704#64) fun _c16 => ?_
  unfold Keccak2SlicesRO
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨?_, ?_⟩
    · exact
        { hrun      := by wp_norm_lhs
          hsp_align := by wp_norm_lhs
          hsp       := by wp_norm_lhs
          hfp       := by wp_norm_lhs
          hx27      := by wp_norm_lhs
          hx25      := by wp_norm_lhs
          hx24      := by refine Eq.trans (by wp_norm_lhs) (sub_div_mul136_bv a.in0.length hin0)
          hx23      := by wp_norm_lhs
          hx22      := by wp_norm_lhs
          hx21      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx19      := by wp_norm_lhs
          hx0       := by wp_norm_lhs
          hx1       := by wp_norm_lhs
          hx2       := by refine Eq.trans (by wp_norm_lhs) (sub_div_mul136_bv a.in0.length hin0) }
    · have hbuf0 :
          ((((((sp + 576#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 8#64) ↦₆₄ 0#64)) ∗
              ((((sp + 576#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 24#64) ↦₆₄ 0#64))) ∗
             (((((sp + 576#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 40#64) ↦₆₄ 0#64)) ∗
              ((((sp + 576#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 56#64) ↦₆₄ 0#64)))) ∗
            ((((((sp + 576#64) + 64#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 72#64) ↦₆₄ 0#64)) ∗
              ((((sp + 576#64) + 80#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 88#64) ↦₆₄ 0#64))) ∗
             (((((sp + 576#64) + 96#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 104#64) ↦₆₄ 0#64)) ∗
              ((((sp + 576#64) + 112#64) ↦₆₄ 0#64) ∗ (((sp + 576#64) + 120#64) ↦₆₄ 0#64))))) ∗
           ((sp + 704#64) ↦₆₄ 0#64) ⊢
          memRegion (sp + 576#64) (a.in0.length % 136) ∗
            (((sp + 576#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
              List.replicate (136 - a.in0.length % 136) 0#8) := by
        rw [show sp + 704#64 = (sp + 576#64) + 128#64 by clear * -; bv_omega,
            zero17_eq_replicate136 (sp + 576#64)]
        exact replicate136_entails_split (sp + 576#64) (a.in0.length % 136)
          (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      exact entails_sub hbuf0 (by sep_frame) (by sep_frame)

/-- Step `[0x0464 → 0x04b4]`: `memcpy` `in0` tail, `0x06`/`0x80` pad `buf0`, zero `buf1`, prepare
    second `memcpy`. -/
private theorem seg_0464_to_04b4 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hlen : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64) (s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x0464#64)
    (hregs : PreMemcpy0Regs s sp rcBase a) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x04b4#64) s
      (memRegion (sp + 576#64) (a.in0.length % 136) ∗
        (((sp + 576#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) ∗
        memRegion (sp + 712#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F)
      (sepPost
        (fun sm => PreMemcpy1Regs sm sp rcBase a)
        (((sp + 576#64) ↦ₛ keccakLastBlock 136 0x06#8 a.in0) ∗
          memRegion (sp + 712#64) 8 ∗
          memRegion (sp + 720#64) (a.in1.length % 136) ∗
          (((sp + 720#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
            List.replicate (136 - a.in1.length % 136) 0#8) ∗
          memRegion (sp + 856#64) 8 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx27, hx25, hx24, hx23, hx22, hx21,
    hx20, hx19, hx0, hx1, hx2⟩
  let byteOff := a.in0.length / 136 * 136
  let tail0 := a.in0.drop byteOff
  have hrem_lt : a.in0.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail0_len : tail0.length = a.in0.length % 136 := by
    dsimp [tail0, byteOff]; rw [List.length_drop]
    have := Nat.div_add_mod a.in0.length 136; omega
  have htail0_u64 : tail0.length < 2 ^ 64 := by omega
  have hx2_nat : (s.readReg64 .x2).toNat = tail0.length := by
    rw [hx2, htail0_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_fn : Unit → a.in0.length = a.in1.length := fun _ => hlen
  clear hlen
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion (sp + 576#64) tail0.length ∗
        (((sp + 576#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) ∗
        memRegion (sp + 712#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0.take byteOff) ∗
        ((a.ptr0 + BitVec.ofNat 64 byteOff) ↦ᵣ tail0) ∗ F by
      rw [htail0_len, pointsToBytesRO_take_drop a.ptr0 a.in0 byteOff (Nat.div_mul_le_self _ _)]
      sep_frame) ?_
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 576#64, a.ptr0 + BitVec.ofNat 64 byteOff, tail0)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hsp'  : sf.sp = sp := hsp_sf.trans hsp
  have hfp'  : sf.readReg64 .fp = sp + 928#64 :=
    (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hfp
  have hx27' : sf.readReg64 .x27 = sp + 576#64 :=
    (by assumption : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
  have hx25' : sf.readReg64 .x25 = rcBase :=
    (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
  have hx24' : sf.readReg64 .x24 = BitVec.ofNat 64 (a.in0.length % 136) :=
    (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
  have hx23' : sf.readReg64 .x23 = BitVec.ofNat 64 (a.in0.length / 136 * 136) :=
    (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
  have hx22' : sf.readReg64 .x22 = BitVec.ofNat 64 a.in0.length :=
    (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
  have hx21' : sf.readReg64 .x21 = a.slicesPtr :=
    (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
  have hx20' : sf.readReg64 .x20 = a.out0 :=
    (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
  have hx19' : sf.readReg64 .x19 = a.out1 :=
    (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19
  have hrejoin_in0 :
      (a.ptr0 ↦ᵣ a.in0.take byteOff) ∗ ((a.ptr0 + BitVec.ofNat 64 byteOff) ↦ᵣ tail0) =
        (a.ptr0 ↦ᵣ a.in0) :=
    (pointsToBytesRO_take_drop a.ptr0 a.in0 byteOff (Nat.div_mul_le_self _ _)).symm
  have hrejoin_buf0 :
      ((sp + 576#64) ↦ₛ tail0) ∗
        (((sp + 576#64) + BitVec.ofNat 64 (a.in0.length % 136)) ↦ₛ
          List.replicate (136 - a.in0.length % 136) 0#8) =
        ((sp + 576#64) ↦ₛ (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)) := by
    rw [← htail0_len]
    exact (pointsToBytes_append (sp + 576#64) tail0
      (List.replicate (136 - tail0.length) 0#8)).symm
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp + 576#64) ↦ₛ (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)) ∗
        memRegion (sp + 712#64) 152 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F by
      rw [← hrejoin_buf0, ← hrejoin_in0]; sep_frame) ?_
  rw [split152_buf1_eq sp]
  refine memRegion128_cells (sp + 720#64) (by sep_focus)
    fun _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 _d8 _d9 _d10 _d11 _d12 _d13 _d14 _d15 => ?_
  refine SepWP.memRegion8_cell (sp + 848#64) fun _d16 => ?_
  have hbuf0_0_len : (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8).length = 136 := by
    simp [htail0_len]; omega
  have hbuf0_1_len :
      (ByteSlice.write8 (tail0 ++ List.replicate (136 - a.in0.length % 136) 0#8)
        (a.in0.length % 136) 0x06#8).length = 136 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf0_0_len]; omega), hbuf0_0_len]
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · exfalso
    have hlen := hlen_fn ()
    simp [hlen, BitVec.ult] at hbr
  · wp_steps
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · rw [sepPost_apply]
      refine ⟨?_, ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := by wp_norm_lhs
            hsp       := by wp_norm_lhs
            hfp       := by wp_norm_lhs
            hx26      := by wp_norm_lhs
            hx25      := by wp_norm_lhs
            hx24      := by refine Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()])
            hx21      := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
            hx20      := by wp_norm_lhs
            hx19      := by wp_norm_lhs
            hx0       := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
            hx1       := by refine Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()])
            hx2       := by refine Eq.trans (by wp_norm_lhs) (by rw [hlen_fn ()]) }
      · have hbuf1 :
            ((((((sp + 720#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 8#64) ↦₆₄ 0#64)) ∗
                ((((sp + 720#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 24#64) ↦₆₄ 0#64))) ∗
               (((((sp + 720#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 40#64) ↦₆₄ 0#64)) ∗
                ((((sp + 720#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 56#64) ↦₆₄ 0#64)))) ∗
              ((((((sp + 720#64) + 64#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 72#64) ↦₆₄ 0#64)) ∗
                ((((sp + 720#64) + 80#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 88#64) ↦₆₄ 0#64))) ∗
               (((((sp + 720#64) + 96#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 104#64) ↦₆₄ 0#64)) ∗
                ((((sp + 720#64) + 112#64) ↦₆₄ 0#64) ∗ (((sp + 720#64) + 120#64) ↦₆₄ 0#64))))) ∗
             ((sp + 848#64) ↦₆₄ 0#64) ⊢
            memRegion (sp + 720#64) (a.in1.length % 136) ∗
              (((sp + 720#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
                List.replicate (136 - a.in1.length % 136) 0#8) := by
          rw [show sp + 848#64 = (sp + 720#64) + 128#64 by clear * -; bv_omega,
              zero17_eq_replicate136 (sp + 720#64)]
          exact replicate136_entails_split (sp + 720#64) (a.in1.length % 136)
            (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
        simp only [orr80_truncate8]
        rw [padBuf136_eq_lastBlock a.in0]
        exact entails_sub hbuf1 (by sep_frame) (by sep_frame)

/-- Step `[0x04b4 → 0x04b8]`: second `memcpy` (`in1` tail into `buf1`). -/
private theorem seg_04b4_to_04b8 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs)
    (sp rcBase : BitVec 64) (s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x04b4#64)
    (hregs : PreMemcpy1Regs s sp rcBase a) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x04b8#64) s
      (((sp + 576#64) ↦ₛ keccakLastBlock 136 0x06#8 a.in0) ∗
        memRegion (sp + 712#64) 8 ∗
        memRegion (sp + 720#64) (a.in1.length % 136) ∗
        (((sp + 720#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) ∗
        memRegion (sp + 856#64) 8 ∗
        (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (sepPost
        (fun sm => Pad1ReadyRegs sm sp rcBase a)
        (((sp + 576#64) ↦ₛ keccakLastBlock 136 0x06#8 a.in0) ∗
          memRegion (sp + 712#64) 8 ∗
          ((sp + 720#64) ↦ₛ (a.in1.drop (a.in1.length / 136 * 136) ++
            List.replicate (136 - a.in1.length % 136) 0#8)) ∗
          memRegion (sp + 856#64) 8 ∗
          (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx26, hx25, hx24, hx21, hx20, hx19, hx0, hx1, hx2⟩
  let byteOff := a.in1.length / 136 * 136
  let tail1 := a.in1.drop byteOff
  have hrem_lt : a.in1.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail1_len : tail1.length = a.in1.length % 136 := by
    dsimp [tail1, byteOff]; rw [List.length_drop]
    have := Nat.div_add_mod a.in1.length 136; omega
  have htail1_u64 : tail1.length < 2 ^ 64 := by omega
  have hx2_nat : (s.readReg64 .x2).toNat = tail1.length := by
    rw [hx2, htail1_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp + 576#64) ↦ₛ keccakLastBlock 136 0x06#8 a.in0) ∗
        memRegion (sp + 712#64) 8 ∗
        memRegion (sp + 720#64) tail1.length ∗
        (((sp + 720#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) ∗
        memRegion (sp + 856#64) 8 ∗
        (a.ptr1 ↦ᵣ a.in1.take byteOff) ∗
        ((a.ptr1 + BitVec.ofNat 64 byteOff) ↦ᵣ tail1) ∗ F by
      rw [htail1_len, pointsToBytesRO_take_drop a.ptr1 a.in1 byteOff (Nat.div_mul_le_self _ _)]
      sep_frame) ?_
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 720#64, a.ptr1 + BitVec.ofNat 64 byteOff, tail1)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hsp'  : sf.sp = sp := hsp_sf.trans hsp
  have hfp'  : sf.readReg64 .fp = sp + 928#64 :=
    (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hfp
  have hx26' : sf.readReg64 .x26 = 6#64 :=
    (by assumption : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)).trans hx26
  have hx25' : sf.readReg64 .x25 = rcBase :=
    (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
  have hx24' : sf.readReg64 .x24 = BitVec.ofNat 64 (a.in1.length % 136) :=
    (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
  have hx21' : sf.readReg64 .x21 = sp + 720#64 :=
    (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
  have hx20' : sf.readReg64 .x20 = a.out0 :=
    (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
  have hx19' : sf.readReg64 .x19 = a.out1 :=
    (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19
  have hrejoin_in1 :
      (a.ptr1 ↦ᵣ a.in1.take byteOff) ∗ ((a.ptr1 + BitVec.ofNat 64 byteOff) ↦ᵣ tail1) =
        (a.ptr1 ↦ᵣ a.in1) :=
    (pointsToBytesRO_take_drop a.ptr1 a.in1 byteOff (Nat.div_mul_le_self _ _)).symm
  have hrejoin_buf1 :
      ((sp + 720#64) ↦ₛ tail1) ∗
        (((sp + 720#64) + BitVec.ofNat 64 (a.in1.length % 136)) ↦ₛ
          List.replicate (136 - a.in1.length % 136) 0#8) =
        ((sp + 720#64) ↦ₛ (tail1 ++ List.replicate (136 - a.in1.length % 136) 0#8)) := by
    rw [← htail1_len]
    exact (pointsToBytes_append (sp + 720#64) tail1
      (List.replicate (136 - tail1.length) 0#8)).symm
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    exact ⟨⟨by wp_norm_lhs, hsp_align_sf, hsp', hfp', hx26', hx25', hx24', hx21', hx20', hx19'⟩,
      by rw [← hrejoin_buf1, ← hrejoin_in1]; sep_frame⟩

private theorem split176_loop2_eq (sp : BitVec 64) :
    memRegion sp 176 =
      memRegion sp 64 ∗ memRegion (sp + 64#64) 32 ∗
        memRegion (sp + 96#64) 64 ∗ memRegion (sp + 160#64) 8 ∗ memRegion (sp + 168#64) 8 := by
  rw [memRegion_split sp 64 112 (by decide),
      memRegion_split (sp + 64#64) 32 80 (by decide),
      show (sp + 64#64) + 32#64 = sp + 96#64 by bv_omega,
      memRegion_split (sp + 96#64) 64 16 (by decide),
      show (sp + 96#64) + 64#64 = sp + 160#64 by bv_omega,
      memRegion_split (sp + 160#64) 8 8 (by decide),
      show (sp + 160#64) + 8#64 = sp + 168#64 by bv_omega]

set_option maxRecDepth 20000 in
/-- Step `[0x04b8 → 0x05e4]`: `0x06`/`0x80` pad `buf1` and XOR all 17 rate lanes into
    `Loop2Regs` + `Loop2SpillMem`. -/
private theorem seg_04b8_to_05e4 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (sp rcBase : BitVec 64)
    (st0 st1 : KeccakState) (hs0 : st0.size ≤ 25) (hs1 : st1.size ≤ 25)
    (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x04b8#64)
    (hregs : Pad1ReadyRegs s sp rcBase a) :
    let blk0 := keccakLastBlock 136 0x06#8 a.in0
    let blk1 := keccakLastBlock 136 0x06#8 a.in1
    let xst0 := keccakXorRate17 st0 blk0
    let xst1 := keccakXorRate17 st1 blk1
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x05e4#64) s
      (memRegion sp 176 ∗
        Keccak2Mem (sp + 176#64) st0 st1 ∗
        ((sp + 576#64) ↦ₛ blk0) ∗
        memRegion (sp + 712#64) 8 ∗
        ((sp + 720#64) ↦ₛ (a.in1.drop (a.in1.length / 136 * 136) ++
          List.replicate (136 - a.in1.length % 136) 0#8)) ∗
        memRegion (sp + 856#64) 8 ∗ F)
      (fun sm Pm =>
        (Loop2EntryRegs sm sp rcBase a ∧ Loop2Regs sm xst0 xst1) ∧
        (Pm ⊢ Loop2SpillMem sp xst0 xst1 ∗
          memRegion (sp + 176#64) 400 ∗
          memRegion (sp + 576#64) 288 ∗ F)) := by
  intro blk0 blk1 xst0 xst1
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx26, hx25, hx24, hx21, hx20, hx19⟩
  have hblk0_len : blk0.length = 136 := keccakLastBlock_length 136 0x06#8 a.in0
  have hblk1_len : blk1.length = 136 := keccakLastBlock_length 136 0x06#8 a.in1
  have hrem_lt : a.in1.length % 136 < 136 := Nat.mod_lt _ (by decide)
  have htail1_len : (a.in1.drop (a.in1.length / 136 * 136)).length = a.in1.length % 136 := by
    rw [List.length_drop]
    have := Nat.div_add_mod a.in1.length 136; omega
  have hbuf1_0_len :
      (a.in1.drop (a.in1.length / 136 * 136) ++
        List.replicate (136 - a.in1.length % 136) 0#8).length = 136 := by
    simp [htail1_len]; omega
  have hbuf1_1_len :
      (ByteSlice.write8
        (a.in1.drop (a.in1.length / 136 * 136) ++
          List.replicate (136 - a.in1.length % 136) 0#8)
        (a.in1.length % 136) 0x06#8).length = 136 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf1_0_len]; omega), hbuf1_0_len]
  rw [split176_loop2_eq sp]
  refine memRegion64_cells (sp + 96#64) (by sep_focus)
    fun _s0 _s1 _s2 _s3 _s4 _s5 _s6 _s7 => ?_
  refine SepWP.memRegion8_cell (sp + 160#64) fun _s8 => ?_
  refine SepWP.memRegion8_cell (sp + 168#64) fun _s9 => ?_
  unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
    Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
  wp_steps 16
  simp only [orr80_truncate8]
  rw [padBuf136_eq_lastBlock a.in1, show keccakLastBlock 136 0x06#8 a.in1 = blk1 from rfl]
  wp_steps 47
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
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact
        { hrun      := by wp_norm_lhs
          hsp_align := by wp_norm_lhs
          hsp       := by wp_norm_lhs
          hx8       := by wp_norm_lhs
          hx9       := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
          hx19      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx25      := by wp_norm_lhs
          hfp       := by wp_norm_lhs }
    · refine
        ⟨by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 a.in1 0]; exact lane_xor_left st0 st1 blk0 blk1 0 0,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 a.in1 8]; exact lane_xor_right st0 st1 blk0 blk1 8 1,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 a.in1 16]; exact lane_xor_left st0 st1 blk0 blk1 16 2,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 a.in1 24]; exact lane_xor_right st0 st1 blk0 blk1 24 3,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            rw [packLane64_pad1_before_80 a.in1 40]; exact lane_xor_right st0 st1 blk0 blk1 40 5,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_left st0 st1 blk0 blk1 80 10,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_right st0 st1 blk0 blk1 88 11,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_left st0 st1 blk0 blk1 96 12,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_right st0 st1 blk0 blk1 104 13,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_left st0 st1 blk0 blk1 112 14,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_right st0 st1 blk0 blk1 120 15,
         by refine Eq.trans (by wp_norm_lhs) ?_; simp only [readLE_8_eq_packLane64]
            exact lane_xor_left st0 st1 blk0 blk1 128 16,
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 17),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 18),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 19),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 20),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 21),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 22),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 23),
         by refine Eq.trans (by wp_norm_lhs) (lane_xor_ge st0 st1 blk0 blk1 hs0 hs1 24)⟩
    · simp only [readLE_8_eq_packLane64]
      rw [packLane64_pad1_before_80 a.in1 32,
          packLane64_pad1_before_80 a.in1 48,
          packLane64_pad1_before_80 a.in1 56,
          show keccakLastBlock 136 0x06#8 a.in1 = blk1 from rfl]
      rw [xor_packLane_right st0 blk0 56 7, xor_packLane_right st1 blk1 56 7,
          xor_packLane_left st0 blk0 48 6, xor_packLane_left st1 blk1 48 6,
          xor_packLane_right st0 blk0 72 9, xor_packLane_right st1 blk1 72 9,
          xor_packLane_left st0 blk0 64 8, xor_packLane_left st1 blk1 64 8,
          xor_packLane_left st0 blk0 32 4, xor_packLane_left st1 blk1 32 4]
      have h400_split : memRegion (sp + 176#64) 400 =
          memRegion (sp + 176#64) 128 ∗ memRegion ((sp + 176#64) + 128#64) 272 :=
        memRegion_split (sp + 176#64) 128 272 (by decide)
      rw [h400_split]
      refine entails_sub (cells128_entails_memRegion (sp + 176#64) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_frame) ?_
      refine entails_sub (rest272_entails_memRegion (sp + 176#64) st0 st1)
        (by unfold Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem; sep_frame) ?_
      refine entails_sub (padBufs_entails_memRegion288 sp blk0 blk1 hblk0_len hblk1_len)
        (by sep_frame) ?_
      unfold Loop2SpillMem
      sep_entail

public section
section
attribute [local irreducible] Keccak2Mem Keccak2SlicesRO Loop2SpillMem

/-- Full tail `memcpy` + `SHA3-256` padding + 17-lane XOR segment (`[0x042c → 0x05e4]`). -/
theorem seg_tail_pad_xor [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64) (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x042c#64)
    (hregs : TailEntryRegs s sp rcBase a)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let nBlocks := a.in0.length / 136
    let st0 := keccakAbsorbPrefix17 a.in0 nBlocks
    let st1 := keccakAbsorbPrefix17 a.in1 nBlocks
    let xst0 := keccakXorRate17 st0 (keccakLastBlock 136 0x06#8 a.in0)
    let xst1 := keccakXorRate17 st1 (keccakLastBlock 136 0x06#8 a.in1)
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x05e4#64) s
      (memRegion sp 176 ∗
        Keccak2Mem (sp + 176#64) st0 st1 ∗
        memRegion (sp + 576#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (fun sm Pm =>
        (Loop2EntryRegs sm sp rcBase a ∧ Loop2Regs sm xst0 xst1) ∧
        (Pm ⊢ Loop2SpillMem sp xst0 xst1 ∗
          memRegion (sp + 176#64) 400 ∗
          memRegion (sp + 576#64) 288 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  intro nBlocks st0 st1 xst0 xst1
  have hs0 : st0.size ≤ 25 := Nat.le_of_eq (keccakAbsorbPrefix17_size a.in0 nBlocks)
  have hs1 : st1.size ≤ 25 := Nat.le_of_eq (keccakAbsorbPrefix17_size a.in1 nBlocks)
  have hpre1 :
      memRegion sp 176 ∗ Keccak2Mem (sp + 176#64) st0 st1 ∗ memRegion (sp + 576#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F ⊢
      memRegion (sp + 576#64) 288 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (memRegion sp 176 ∗ Keccak2Mem (sp + 176#64) st0 st1 ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) := by
    sep_frame
  refine SepWP.weaken_pre hpre1 ?_
  refine sepWP_seq_env hcl hro
    (seg_042c_to_0464 b hb hbase a hin0 sp rcBase s
      (memRegion sp 176 ∗ Keccak2Mem (sp + 176#64) st0 st1 ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) hpc hregs) ?_
  intro s1 P1 hpc1 _ hcl1 hro1 hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨hregs1, hP1⟩
  have hwp1 := seg_0464_to_04b4 b hb hbase a hlen sp rcBase s1
    (memRegion sp 176 ∗ Keccak2Mem (sp + 176#64) st0 st1 ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
    hcl1 hpc1 hregs1
  refine (fun h h1 => SepWP.weaken_pre h1 h) (sepWP_seq_env hcl1 hro1 hwp1 ?_)
    (Entails.trans hP1 (by sep_frame))
  intro s2 P2 hpc2 _ hcl2 hro2 hpost2
  rw [sepPost_apply] at hpost2
  rcases hpost2 with ⟨hregs2, hP2⟩
  have hwp2 := seg_04b4_to_04b8 b hb hbase a sp rcBase s2
    (memRegion sp 176 ∗ Keccak2Mem (sp + 176#64) st0 st1 ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ F)
    hcl2 hpc2 hregs2
  refine (fun h h2 => SepWP.weaken_pre h2 h) (sepWP_seq_env hcl2 hro2 hwp2 ?_)
    (Entails.trans hP2 (by sep_frame))
  intro s3 P3 hpc3 _ _ _ hpost3
  rw [sepPost_apply] at hpost3
  rcases hpost3 with ⟨hregs3, hP3⟩
  have hwp3 := seg_04b8_to_05e4 b hb hbase a sp rcBase st0 st1 hs0 hs1
    (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) s3 hpc3 hregs3
  refine (fun h h3 => SepWP.weaken_pre h3 h) (SepWP.mono hwp3 ?_)
    (Entails.trans hP3 (by sep_frame))
  intro sf Pf _ _ ⟨hregsf, hPf⟩
  exact ⟨hregsf, Entails.trans hPf (by sep_frame)⟩

end
end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPadXor
