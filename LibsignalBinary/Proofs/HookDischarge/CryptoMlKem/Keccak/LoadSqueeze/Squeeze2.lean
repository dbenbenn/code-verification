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
# `B08`: `KeccakState<2, uint64x2_t>::squeeze2::<136>`

Functional correctness proof for `mlkemBlk08` (`264` words, `96`-byte stack frame). Exports
`squeeze2_136_block_ok : MlKemBlockConstOk 8 squeeze2_136_Spec` for `outLen = 32 ∨ outLen = 128`
(exact 16-byte-multiple NEON deinterleave fast path, skipping tail `memcpy`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.Squeeze2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  MlKemBlockConstOk
  mlkemMpl
  mlkemLeaf_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakExtractRate
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd2_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakExtractRate_17_take_128
  keccakExtractRate_17_take_32
  memRegion128_cells
  memRegion32_cells
  memRegion64_cells
  pointsTo64_16_eq_bytes
  pointsTo64_4_eq_bytes
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-! ## Placed-block fetch setup (`mlkemBlk08`, `264` words, fast-path ranges) -/

gen_block_fetches mlkem 8 mlkemMultiLib MlKemPlacement 264
  [0x0 → 0x174, 0x1f4 → 0x1f4, 0x258 → 0x26c]

public section

/-! ## `B08` contract (`squeeze2_136_Spec`) -/

/-- Arguments to `B08` (`KeccakState<2, uint64x2_t>::squeeze2::<136>`). -/
structure Squeeze2Args where
  statePtr : BitVec 64
  out0     : BitVec 64
  out1     : BitVec 64
  outLen   : Nat
  st0      : KeccakState
  st1      : KeccakState

/-- Base `B08` (`squeeze2::<136>`) contract before adjoining `NonSyscallPreserved`. -/
@[expose] def squeeze2_136_BaseSpec : Spec Squeeze2Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.statePtr ∧
      s0.readReg64 .x1 = a.out0 ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 a.outLen ∧
      s0.readReg64 .x3 = a.out1 ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 a.outLen ∧
      s0.readReg64 .x5 = BitVec.ofNat 64 a.outLen ∧
      (a.outLen = 32 ∨ a.outLen = 128)⌝ ∗
      Keccak2Rate16Mem a.statePtr a.st0 a.st1 ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗
      stackAt s0.sp 96
  post := fun a s0 _sf =>
    Keccak2Rate16Mem a.statePtr a.st0 a.st1 ∗
      (a.out0 ↦ₛ (keccakExtractRate 17 a.st0).take a.outLen) ∗
      (a.out1 ↦ₛ (keccakExtractRate 17 a.st1).take a.outLen) ∗
      stackAt s0.sp 96
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B08` (`squeeze2::<136>`) subroutine contract (`96`-byte stack frame, `outLen ∈ {32, 128}`,
    with `NonSyscallPreserved s0 sf`). -/
@[expose] def squeeze2_136_Spec : Spec Squeeze2Args :=
  withNonSyscallPreserved squeeze2_136_BaseSpec

/-! ## Proof of `squeeze2_136_block_ok` -/

local macro "step_ld2_2d" : tactic => `(tactic| (
  apply step_simdLd2_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · first | wp_norm_lhs | wp_norm_goal
  · wp_norm_lhs
  · rfl
  · rfl
  · rfl
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_norm_lhs))

private theorem memRegion64_split8 (base : BitVec 64) :
    memRegion base 64 =
      (((memRegion base 8 ∗ memRegion (base + 8#64) 8) ∗
        (memRegion (base + 16#64) 8 ∗ memRegion (base + 24#64) 8)) ∗
       ((memRegion (base + 32#64) 8 ∗ memRegion (base + 40#64) 8) ∗
        (memRegion (base + 48#64) 8 ∗ memRegion (base + 56#64) 8))) := by
  have h32 (x : BitVec 64) :
      memRegion x 32 =
        ((memRegion x 8 ∗ memRegion (x + 8#64) 8) ∗
         (memRegion (x + 16#64) 8 ∗ memRegion (x + 24#64) 8)) := by
    rw [memRegion_split x 16 16 (by decide),
        memRegion_split x 8 8 (by decide),
        memRegion_split (x + 16#64) 8 8 (by decide),
        show (x + 16#64) + 8#64 = x + 24#64 by bv_omega]
  rw [memRegion_split base 32 32 (by decide), h32 base, h32 (base + 32#64),
      show (base + 32#64) + 8#64 = base + 40#64 by bv_omega,
      show (base + 32#64) + 16#64 = base + 48#64 by bv_omega,
      show (base + 32#64) + 24#64 = base + 56#64 by bv_omega]

set_option maxRecDepth 20000 in
private theorem squeeze2_136_base_ok : MlKemBlockConstOk 8 squeeze2_136_BaseSpec := by
  intro _
  refine mlkemLeaf_ok mlkemPC8 mlkemPl8 rfl rfl fun b hb hbase => ?_
  change subroutine_ok _ b squeeze2_136_BaseSpec
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp
  dsimp only [ToBaseSpec.toSpec, squeeze2_136_BaseSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hout⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  rw [stackAt_split_bottom s0.sp 0 96 (by decide),
      show s0.sp - BitVec.ofNat 64 (0 + 96) = s0.sp - 96#64 from rfl,
      memRegion_split (s0.sp - 96#64) 32 64 (by decide)]
  refine memRegion64_cells ((s0.sp - 96#64) + 32#64) (by sep_focus)
    fun ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7 => ?_
  rcases hout with hout32 | hout128
  · -- Case `outLen = 32`
    rw [hout32] at hx2 hx4 hx5 ⊢
    refine memRegion32_cells a.out0 (by sep_focus) fun o0_0 o0_1 o0_2 o0_3 => ?_
    refine memRegion32_cells a.out1 (by sep_focus) fun o1_0 o1_1 o1_2 o1_3 => ?_
    unfold Keccak2Rate16Mem Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem
    wp_steps
    step_ld2_2d
    wp_steps
    refine SepWP.weaken_pre (?_ : _ ⊢
      Keccak2Rate16Mem a.statePtr a.st0 a.st1 ∗
        (a.out0 ↦ₛ (keccakExtractRate 17 a.st0).take 32) ∗
        (a.out1 ↦ₛ (keccakExtractRate 17 a.st1).take 32) ∗
        stackAt s0.sp 96) ?_
    · unfold Keccak2Rate16Mem Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem
      rw [keccakExtractRate_17_take_32 a.st0, keccakExtractRate_17_take_32 a.st1,
          ← pointsTo64_4_eq_bytes a.out0, ← pointsTo64_4_eq_bytes a.out1,
          stackAt_split_bottom s0.sp 0 96 (by decide),
          show s0.sp - BitVec.ofNat 64 (0 + 96) = s0.sp - 96#64 from rfl,
          memRegion_split (s0.sp - 96#64) 32 64 (by decide),
          memRegion64_split8 ((s0.sp - 96#64) + 32#64)]
      sep_entail
    · dsimp only [Keccak2Rate16Mem, Keccak2Q0Mem, Keccak2Q1Mem, Keccak2Q2Mem, Keccak2Q3Mem]
      rw [stackAt_split_bottom s0.sp 0 96 (by decide),
          show s0.sp - BitVec.ofNat 64 (0 + 96) = s0.sp - 96#64 from rfl,
          memRegion_split (s0.sp - 96#64) 32 64 (by decide)]
      wp_done
  · -- Case `outLen = 128`
    rw [hout128] at hx2 hx4 hx5 ⊢
    refine memRegion128_cells a.out0 (by sep_focus)
      fun o0_0 o0_1 o0_2 o0_3 o0_4 o0_5 o0_6 o0_7
          o0_8 o0_9 o0_10 o0_11 o0_12 o0_13 o0_14 o0_15 => ?_
    refine memRegion128_cells a.out1 (by sep_focus)
      fun o1_0 o1_1 o1_2 o1_3 o1_4 o1_5 o1_6 o1_7
          o1_8 o1_9 o1_10 o1_11 o1_12 o1_13 o1_14 o1_15 => ?_
    unfold Keccak2Rate16Mem Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    step_ld2_2d
    wp_steps
    refine SepWP.weaken_pre (?_ : _ ⊢
      Keccak2Rate16Mem a.statePtr a.st0 a.st1 ∗
        (a.out0 ↦ₛ (keccakExtractRate 17 a.st0).take 128) ∗
        (a.out1 ↦ₛ (keccakExtractRate 17 a.st1).take 128) ∗
        stackAt s0.sp 96) ?_
    · unfold Keccak2Rate16Mem Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem
      rw [keccakExtractRate_17_take_128 a.st0, keccakExtractRate_17_take_128 a.st1,
          ← pointsTo64_16_eq_bytes a.out0, ← pointsTo64_16_eq_bytes a.out1,
          stackAt_split_bottom s0.sp 0 96 (by decide),
          show s0.sp - BitVec.ofNat 64 (0 + 96) = s0.sp - 96#64 from rfl,
          memRegion_split (s0.sp - 96#64) 32 64 (by decide),
          memRegion64_split8 ((s0.sp - 96#64) + 32#64)]
      sep_entail
    · dsimp only [Keccak2Rate16Mem, Keccak2Q0Mem, Keccak2Q1Mem, Keccak2Q2Mem, Keccak2Q3Mem]
      rw [stackAt_split_bottom s0.sp 0 96 (by decide),
          show s0.sp - BitVec.ofNat 64 (0 + 96) = s0.sp - 96#64 from rfl,
          memRegion_split (s0.sp - 96#64) 32 64 (by decide)]
      wp_done

/-- `B08` (`squeeze2::<136>`) satisfies `squeeze2_136_Spec` at any valid `MlKemPlacement`. -/
theorem squeeze2_136_block_ok : MlKemBlockConstOk 8 squeeze2_136_Spec :=
  mlkemBlockConstOk_withNonSyscallPreserved squeeze2_136_base_ok
    (h_pre := fun mpl x R s0 h => by
      dsimp only [squeeze2_136_BaseSpec] at h ⊢
      simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
    (h_post := fun mpl x R s0 sf hnsp h => by
      dsimp only [squeeze2_136_BaseSpec] at h ⊢
      simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
        stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.Squeeze2
