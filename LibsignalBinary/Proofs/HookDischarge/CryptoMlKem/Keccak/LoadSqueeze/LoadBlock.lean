/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import ProofLib.ProgramReflection
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B09`: `KeccakState<2, uint64x2_t>::load_block::<136>`

Functional correctness proof for `mlkemBlk09` (`179` words, `16`-byte stack frame, leaf).
Exports `loadBlock136_block_ok : MlKemBlockConstOk 9 loadBlock136Spec`, showing that `B09` XORs
`136` bytes starting at `byteOff` from two read-only input slices `(ptr0 ↦ᵣ in0)` and
`(ptr1 ↦ᵣ in1)` into `Keccak2Rate17Mem statePtr st0 st1` while preserving `NonSyscallPreserved`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  MlKemBlockConstOk
  mlkemMpl
  mlkemLeaf_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRO
  withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockConstOk_withNonSyscallPreserved
  mlkemKeep
  stripExecOutside_eq_iff_of_perm_eq
  stripS_mem
  stripS_readReg32
  stripS_readReg64
  stripS_regs
  stripS_sp
  stripS_vregs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState packLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccakXorRate17
  keccakXorRate17_getD_lt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  readLE_8_eq_packLane64
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-! ## Placed-block fetch setup (`mlkemBlk09`, `179` words) -/

gen_block_fetches mlkem 9 mlkemMultiLib MlKemPlacement 179 [0x0 → 0x20c]

public section

/-! ## `B09` contract (`loadBlock136Spec`) -/

/-- Arguments to `B09` (`KeccakState<2, uint64x2_t>::load_block::<136>`). -/
structure LoadBlock136Args where
  statePtr  : BitVec 64
  slicesPtr : BitVec 64
  ptr0      : BitVec 64
  ptr1      : BitVec 64
  byteOff   : Nat
  in0       : List (BitVec 8)
  in1       : List (BitVec 8)
  st0       : KeccakState
  st1       : KeccakState

/-- Base `B09` (`load_block::<136>`) contract before adjoining `NonSyscallPreserved`. -/
@[expose] def loadBlock136BaseSpec : Spec LoadBlock136Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.statePtr ∧
      s0.readReg64 .x1 = a.slicesPtr ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 a.byteOff ∧
      a.byteOff + 136 ≤ a.in0.length ∧
      a.byteOff + 136 ≤ a.in1.length ∧
      a.in0.length < 2 ^ 64 ∧
      a.in1.length < 2 ^ 64⌝ ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      Keccak2Rate17Mem a.statePtr a.st0 a.st1 ∗
      stackAt s0.sp 16
  post := fun a s0 _sf =>
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      Keccak2Rate17Mem a.statePtr
        (keccakXorRate17 a.st0 ((a.in0.drop a.byteOff).take 136))
        (keccakXorRate17 a.st1 ((a.in1.drop a.byteOff).take 136)) ∗
      stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B09` (`load_block::<136>`) subroutine contract (`16`-byte stack frame, read-only inputs,
    with `NonSyscallPreserved s0 sf`). -/
@[expose] def loadBlock136Spec : Spec LoadBlock136Args :=
  withNonSyscallPreserved loadBlock136BaseSpec

/-! ## Proof of `loadBlock136_block_ok` -/

private theorem readLE_slice136 (bs : List (BitVec 8)) (byteOff off : Nat)
    (hoff : off + 8 ≤ 136 := by decide) :
    ByteSlice.readLE bs (byteOff + off) 8 =
      packLane64 ((bs.drop byteOff).take 136) off := by
  rw [readLE_8_eq_packLane64]
  unfold packLane64
  have g (j : Nat) (hj : j < 8) :
      bs.getD (byteOff + off + j) 0#8 =
        ((bs.drop byteOff).take 136).getD (off + j) 0#8 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, show off + j < 136 by omega,
      Nat.add_assoc]
  rw [show bs.getD (byteOff + off) 0#8 = bs.getD (byteOff + off + 0) 0#8 by simp,
      g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide),
      Nat.add_zero]

private theorem readLE_slice136_zero (bs : List (BitVec 8)) (byteOff : Nat) :
    ByteSlice.readLE bs byteOff 8 =
      packLane64 ((bs.drop byteOff).take 136) 0 := by
  simpa using readLE_slice136 bs byteOff 0 (by decide)

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

private theorem not_ult_of_bound {len byteOff : Nat} {off : BitVec 64}
    (h1 : byteOff + 136 ≤ len) (h2 : len < 2 ^ 64) (hk : off.toNat ≤ 136)
    (hc : (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 byteOff + off) = true) :
    False := by
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hc
  omega

set_option maxRecDepth 20000 in
private theorem loadBlock136_base_ok : MlKemBlockConstOk 9 loadBlock136BaseSpec := by
  intro _
  refine mlkemLeaf_ok mlkemPC9 mlkemPl9 rfl rfl fun b hb hbase => ?_
  change subroutine_ok _ b loadBlock136BaseSpec
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp
  dsimp only [ToBaseSpec.toSpec, loadBlock136BaseSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, h0, h1, hlen0, hlen1⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  rw [stackAt_split_bottom s0.sp 0 16 (by decide),
      show s0.sp - BitVec.ofNat 64 (0 + 16) = s0.sp - 16#64 from rfl,
      show memRegion (s0.sp - 16#64) 16 =
        memRegion (s0.sp - 16#64) 8 ∗ memRegion ((s0.sp - 16#64) + 8#64) 8 from
        memRegion_split (s0.sp - 16#64) 8 8 (by decide)]
  refine SepWP.memRegion8_cell (s0.sp - 16#64) fun wfp => ?_
  refine SepWP.memRegion8_cell ((s0.sp - 16#64) + 8#64) fun wlr => ?_
  unfold Keccak2SlicesRO Keccak2Rate17Mem Keccak2Rate16Mem
    Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem
  wp_steps
  wp_if hc1; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc1)
  wp_steps
  wp_if hc2; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc2)
  wp_steps
  wp_if hc3; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc3)
  wp_steps
  wp_if hc4; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc4)
  wp_steps
  wp_if hc5; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc5)
  wp_steps
  wp_if hc6; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc6)
  wp_steps
  wp_if hc7; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc7)
  wp_steps
  wp_if hc8; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc8)
  wp_steps
  wp_if hc9; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc9)
  wp_steps
  wp_if hc10; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc10)
  wp_steps
  wp_if hc11; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc11)
  wp_steps
  wp_if hc12; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc12)
  wp_steps
  wp_if hc13; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc13)
  wp_steps
  wp_if hc14; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc14)
  wp_steps
  wp_if hc15; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc15)
  wp_steps
  wp_if hc16; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc16)
  wp_steps
  wp_if hc17; on_goal 1 => exact False.elim (not_ult_of_bound h0 hlen0 (by decide) hc17)
  wp_steps
  wp_if hc18; on_goal 1 => exact False.elim (not_ult_of_bound h1 hlen1 (by decide) hc18)
  wp_steps 4
  apply step_simdLd1Single64
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  refine SepWP.weaken_pre (?_ : _ ⊢
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      Keccak2Rate17Mem a.statePtr
        (keccakXorRate17 a.st0 ((a.in0.drop a.byteOff).take 136))
        (keccakXorRate17 a.st1 ((a.in1.drop a.byteOff).take 136)) ∗
      stackAt s0.sp 16) ?_
  · simp only [
      readLE_slice136_zero a.in0 a.byteOff, readLE_slice136_zero a.in1 a.byteOff,
      readLE_slice136 a.in0 a.byteOff 8, readLE_slice136 a.in1 a.byteOff 8,
      readLE_slice136 a.in0 a.byteOff 16, readLE_slice136 a.in1 a.byteOff 16,
      readLE_slice136 a.in0 a.byteOff 24, readLE_slice136 a.in1 a.byteOff 24,
      readLE_slice136 a.in0 a.byteOff 32, readLE_slice136 a.in1 a.byteOff 32,
      readLE_slice136 a.in0 a.byteOff 40, readLE_slice136 a.in1 a.byteOff 40,
      readLE_slice136 a.in0 a.byteOff 48, readLE_slice136 a.in1 a.byteOff 48,
      readLE_slice136 a.in0 a.byteOff 56, readLE_slice136 a.in1 a.byteOff 56,
      readLE_slice136 a.in0 a.byteOff 64, readLE_slice136 a.in1 a.byteOff 64,
      readLE_slice136 a.in0 a.byteOff 72, readLE_slice136 a.in1 a.byteOff 72,
      readLE_slice136 a.in0 a.byteOff 80, readLE_slice136 a.in1 a.byteOff 80,
      readLE_slice136 a.in0 a.byteOff 88, readLE_slice136 a.in1 a.byteOff 88,
      readLE_slice136 a.in0 a.byteOff 96, readLE_slice136 a.in1 a.byteOff 96,
      readLE_slice136 a.in0 a.byteOff 104, readLE_slice136 a.in1 a.byteOff 104,
      readLE_slice136 a.in0 a.byteOff 112, readLE_slice136 a.in1 a.byteOff 112,
      readLE_slice136 a.in0 a.byteOff 120, readLE_slice136 a.in1 a.byteOff 120,
      readLE_slice136 a.in0 a.byteOff 128, readLE_slice136 a.in1 a.byteOff 128]
    repeat first
      | rw [xor_packLane_left _ _ 0 0]
      | rw [xor_packLane_right _ _ 8 1]
      | rw [xor_packLane_left _ _ 16 2]
      | rw [xor_packLane_right _ _ 24 3]
      | rw [xor_packLane_left _ _ 32 4]
      | rw [xor_packLane_right _ _ 40 5]
      | rw [xor_packLane_left _ _ 48 6]
      | rw [xor_packLane_right _ _ 56 7]
      | rw [xor_packLane_left _ _ 64 8]
      | rw [xor_packLane_right _ _ 72 9]
      | rw [xor_packLane_left _ _ 80 10]
      | rw [xor_packLane_right _ _ 88 11]
      | rw [xor_packLane_left _ _ 96 12]
      | rw [xor_packLane_right _ _ 104 13]
      | rw [xor_packLane_left _ _ 112 14]
      | rw [xor_packLane_right _ _ 120 15]
      | rw [xor_packLane_left _ _ 128 16]
      | rw [xor_packLane_right _ _ 128 16]
    unfold Keccak2SlicesRO Keccak2Rate17Mem Keccak2Rate16Mem
      Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem
    rw [stackAt_split_bottom s0.sp 0 16 (by decide),
        show s0.sp - BitVec.ofNat 64 (0 + 16) = s0.sp - 16#64 from rfl,
        show memRegion (s0.sp - 16#64) 16 =
          memRegion (s0.sp - 16#64) 8 ∗ memRegion ((s0.sp - 16#64) + 8#64) 8 from
          memRegion_split (s0.sp - 16#64) 8 8 (by decide)]
    sep_entail
  · dsimp only [Keccak2SlicesRO, Keccak2Rate17Mem, Keccak2Rate16Mem,
      Keccak2Q0Mem, Keccak2Q1Mem, Keccak2Q2Mem, Keccak2Q3Mem, Keccak2Vec16Mem]
    rw [stackAt_split_bottom s0.sp 0 16 (by decide),
        show s0.sp - BitVec.ofNat 64 (0 + 16) = s0.sp - 16#64 from rfl,
        show memRegion (s0.sp - 16#64) 16 =
          memRegion (s0.sp - 16#64) 8 ∗ memRegion ((s0.sp - 16#64) + 8#64) 8 from
          memRegion_split (s0.sp - 16#64) 8 8 (by decide)]
    wp_done

/-- `B09` (`load_block::<136>`) satisfies `loadBlock136Spec` at any valid `MlKemPlacement`. -/
theorem loadBlock136_block_ok : MlKemBlockConstOk 9 loadBlock136Spec :=
  mlkemBlockConstOk_withNonSyscallPreserved loadBlock136_base_ok
    (h_pre := fun mpl x R s0 h => by
      dsimp only [loadBlock136BaseSpec] at h ⊢
      simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
    (h_post := fun mpl x R s0 sf hnsp h => by
      dsimp only [loadBlock136BaseSpec] at h ⊢
      simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
        stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock
