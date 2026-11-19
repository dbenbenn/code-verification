/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf1
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): round second half and 24-round loop

Proof of segment `[0x07fc → 0x09e8]` (`124` instructions) of `mlkemBlk00`, completing `θ`,
`ρ`/`π`, `χ`, and `ι` (`LD1R` from the `.rodata` round-constant table) and inductively running
all 24 rounds (`r = 0 .. 23`) from `+0x06c8` to `+0x09ec`, transforming `(st0, st1)` into
`(keccakF1600 st0, keccakF1600 st1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf2

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  keccakRcAt
  mlkemData01Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  keccakF1600Round
  keccakRhoOffset
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakD
  keccakF1600Round_getD
  keccakRhoPi
  keccakRhoPiSrc
  keccakRoundLane
  keccakRunFrom
  keccakRunFrom_24
  keccakRunFrom_step
  keccakRunFrom_zero
  keccakTheta
  rotateLeft_zero_64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base (
  LaneSlot
  LoopRegs
  LoopSpillMem
  MidRegs
  MidSpillMem
  blk00_code_eq
  blk00_tree_size
  blkLib00
  blkPC00
  blkPl00
  blkPlaceable00
  blkTree00
  keccak2D
  keccak2RhoPi
  keccak2Theta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf1 (
  round_half1_ok
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x07fc → 0x09e8]

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem d_xor_lane (st : KeccakState) (x k : Nat) (h : k % 5 = x) :
    keccakD st x ^^^ st.getD k 0#64 = keccakTheta st k := by
  subst h; exact BitVec.xor_comm _ _

private theorem hth0  (st : KeccakState) : keccakD st 0 ^^^ st.getD 0  0#64 = keccakTheta st 0  := d_xor_lane st 0 0 rfl
private theorem hth3  (st : KeccakState) : keccakD st 3 ^^^ st.getD 3  0#64 = keccakTheta st 3  := d_xor_lane st 3 3 rfl
private theorem hth4  (st : KeccakState) : keccakD st 4 ^^^ st.getD 4  0#64 = keccakTheta st 4  := d_xor_lane st 4 4 rfl
private theorem hth7  (st : KeccakState) : keccakD st 2 ^^^ st.getD 7  0#64 = keccakTheta st 7  := d_xor_lane st 2 7 rfl
private theorem hth8  (st : KeccakState) : keccakD st 3 ^^^ st.getD 8  0#64 = keccakTheta st 8  := d_xor_lane st 3 8 rfl
private theorem hth9  (st : KeccakState) : keccakD st 4 ^^^ st.getD 9  0#64 = keccakTheta st 9  := d_xor_lane st 4 9 rfl
private theorem hth13 (st : KeccakState) : keccakD st 3 ^^^ st.getD 13 0#64 = keccakTheta st 13 := d_xor_lane st 3 13 rfl
private theorem hth14 (st : KeccakState) : keccakD st 4 ^^^ st.getD 14 0#64 = keccakTheta st 14 := d_xor_lane st 4 14 rfl
private theorem hth18 (st : KeccakState) : keccakD st 3 ^^^ st.getD 18 0#64 = keccakTheta st 18 := d_xor_lane st 3 18 rfl
private theorem hth19 (st : KeccakState) : st.getD 19 0#64 ^^^ keccakD st 4 = keccakTheta st 19 := rfl
private theorem hth22 (st : KeccakState) : keccakD st 2 ^^^ st.getD 22 0#64 = keccakTheta st 22 := d_xor_lane st 2 22 rfl
private theorem hth23 (st : KeccakState) : keccakD st 3 ^^^ st.getD 23 0#64 = keccakTheta st 23 := d_xor_lane st 3 23 rfl
private theorem hth24 (st : KeccakState) : st.getD 24 0#64 ^^^ keccakD st 4 = keccakTheta st 24 := rfl

private theorem chi_xor_eq (b0 b1 b2 : BitVec 64) :
    (~~~b1 &&& b2) ^^^ b0 = b0 ^^^ (~~~b1 &&& b2) :=
  BitVec.xor_comm _ _

private theorem chi0_xor_eq (b0 b1 b2 rc : BitVec 64) :
    (~~~b1 &&& b2) ^^^ (rc ^^^ b0) = (b0 ^^^ (~~~b1 &&& b2)) ^^^ rc := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases b0[i] <;> cases b1[i] <;> cases b2[i] <;> cases rc[i] <;> rfl

private theorem chi0_xor_after_eq (b0 b1 b2 rc : BitVec 64) :
    (rc ^^^ b0) ^^^ (~~~b1 &&& b2) = (b0 ^^^ (~~~b1 &&& b2)) ^^^ rc := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases b0[i] <;> cases b1[i] <;> cases b2[i] <;> cases rc[i] <;> rfl

private theorem memRegion16_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 16 ∗ F := by sep_focus)
    (h : ∀ w0 w1 : BitVec 64,
      SepWP prog target_pc s (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, show memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 from
    memRegion_split a 8 8 (by decide)]
  refine SepWP.memRegion8_cell a fun w0 => ?_
  refine SepWP.memRegion8_cell (a + 8#64) fun w1 => ?_
  exact SepWP.congr_pre (by sep_eq) (h w0 w1)

private theorem cells2_entails_memRegion16 (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢ memRegion a 16 := by
  rw [show memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 from
    memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

private theorem cells4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
      (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ⊢ memRegion a 32 := by
  rw [show memRegion a 32 = memRegion a 16 ∗ memRegion (a + 16#64) 16 from
        memRegion_split a 16 16 (by decide),
      show a + 24#64 = (a + 16#64) + 8#64 by bv_omega]
  exact sepConj_mono (cells2_entails_memRegion16 a w0 w1)
    (cells2_entails_memRegion16 (a + 16#64) w2 w3)

private theorem cells8_entails_memRegion64 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
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

private theorem cells_to_loopSpillMem (sp rcBase : BitVec 64) (st0' st1' : KeccakState)
    {q0 q1 : BitVec 64}
    {u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64} :
    ((sp + 176#64) ↦₆₄ q0) ∗ ((sp + 184#64) ↦₆₄ q1) ∗
      ((sp + 192#64) ↦₆₄ st0'.getD 1 0#64) ∗ ((sp + 200#64) ↦₆₄ st1'.getD 1 0#64) ∗
      ((sp + 208#64) ↦₆₄ st0'.getD 6 0#64) ∗ ((sp + 216#64) ↦₆₄ st1'.getD 6 0#64) ∗
      ((sp + 224#64) ↦₆₄ st0'.getD 2 0#64) ∗ ((sp + 232#64) ↦₆₄ st1'.getD 2 0#64) ∗
      ((sp + 240#64) ↦₆₄ u0) ∗ ((sp + 248#64) ↦₆₄ u1) ∗
      ((sp + 256#64) ↦₆₄ u2) ∗ ((sp + 264#64) ↦₆₄ u3) ∗
      ((sp + 272#64) ↦₆₄ u4) ∗ ((sp + 280#64) ↦₆₄ u5) ∗
      ((sp + 288#64) ↦₆₄ u6) ∗ ((sp + 296#64) ↦₆₄ u7) ∗
      ((sp + 304#64) ↦₆₄ st0'.getD 3 0#64) ∗ ((sp + 312#64) ↦₆₄ st1'.getD 3 0#64) ∗
      ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
      ((sp + 336#64) ↦₆₄ w2) ∗ ((sp + 344#64) ↦₆₄ w3) ∗
      ((sp + 352#64) ↦₆₄ w4) ∗ ((sp + 360#64) ↦₆₄ w5) ∗
      ((sp + 368#64) ↦₆₄ w6) ∗ ((sp + 376#64) ↦₆₄ w7) ∗
      ((sp + 384#64) ↦₆₄ st0'.getD 4 0#64) ∗ ((sp + 392#64) ↦₆₄ st1'.getD 4 0#64) ∗
      (rcBase ↦ᵣ mlkemData01Bytes) ⊢
      LoopSpillMem sp st0' st1' ∗ (rcBase ↦ᵣ mlkemData01Bytes) := by
  have h16 :
      ((sp + 176#64) ↦₆₄ q0) ∗ ((sp + 184#64) ↦₆₄ q1) ⊢ memRegion (sp + 176#64) 16 := by
    rw [show sp + 184#64 = (sp + 176#64) + 8#64 by bv_omega]
    exact cells2_entails_memRegion16 (sp + 176#64) q0 q1
  have h64u :
      ((((sp + 240#64) ↦₆₄ u0) ∗ ((sp + 248#64) ↦₆₄ u1)) ∗
        (((sp + 256#64) ↦₆₄ u2) ∗ ((sp + 264#64) ↦₆₄ u3))) ∗
      ((((sp + 272#64) ↦₆₄ u4) ∗ ((sp + 280#64) ↦₆₄ u5)) ∗
        (((sp + 288#64) ↦₆₄ u6) ∗ ((sp + 296#64) ↦₆₄ u7))) ⊢ memRegion (sp + 240#64) 64 := by
    rw [show sp + 248#64 = (sp + 240#64) + 8#64 by bv_omega,
        show sp + 256#64 = (sp + 240#64) + 16#64 by bv_omega,
        show sp + 264#64 = (sp + 240#64) + 24#64 by bv_omega,
        show sp + 272#64 = (sp + 240#64) + 32#64 by bv_omega,
        show sp + 280#64 = (sp + 240#64) + 40#64 by bv_omega,
        show sp + 288#64 = (sp + 240#64) + 48#64 by bv_omega,
        show sp + 296#64 = (sp + 240#64) + 56#64 by bv_omega]
    exact cells8_entails_memRegion64 (sp + 240#64) u0 u1 u2 u3 u4 u5 u6 u7
  have h64w :
      ((((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1)) ∗
        (((sp + 336#64) ↦₆₄ w2) ∗ ((sp + 344#64) ↦₆₄ w3))) ∗
      ((((sp + 352#64) ↦₆₄ w4) ∗ ((sp + 360#64) ↦₆₄ w5)) ∗
        (((sp + 368#64) ↦₆₄ w6) ∗ ((sp + 376#64) ↦₆₄ w7))) ⊢ memRegion (sp + 320#64) 64 := by
    rw [show sp + 328#64 = (sp + 320#64) + 8#64 by bv_omega,
        show sp + 336#64 = (sp + 320#64) + 16#64 by bv_omega,
        show sp + 344#64 = (sp + 320#64) + 24#64 by bv_omega,
        show sp + 352#64 = (sp + 320#64) + 32#64 by bv_omega,
        show sp + 360#64 = (sp + 320#64) + 40#64 by bv_omega,
        show sp + 368#64 = (sp + 320#64) + 48#64 by bv_omega,
        show sp + 376#64 = (sp + 320#64) + 56#64 by bv_omega]
    exact cells8_entails_memRegion64 (sp + 320#64) w0 w1 w2 w3 w4 w5 w6 w7
  have sub : ∀ {A B P Rest Q : SepProp},
      (A ⊢ B) → (P ⊢ A ∗ Rest) → (B ∗ Rest ⊢ Q) → (P ⊢ Q) :=
    fun hAB h1 h2 => Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)
  dsimp only [LoopSpillMem, LaneSlot]
  exact sub h16 (by sep_frame) (sub h64u (by sep_frame) (sub h64w (by sep_frame) (by sep_frame)))

private theorem round_getD_of_lt {s : KeccakState} {rc : BitVec 64} {idx : Nat}
    (hidx : idx < 25) :
    (keccakF1600Round s rc).getD idx 0#64 = keccakRoundLane s rc idx :=
  keccakF1600Round_getD s rc hidx

local macro "keccak_round_vreg" idx:num : tactic => `(tactic| (
  refine Eq.trans (by wp_norm_lhs) ?_
  simp only [BitVec.or_self, keccak2Lane, round_getD_of_lt (idx := $idx) (by decide),
    hth0, hth3, hth4, hth7, hth8, hth9, hth13, hth14, hth18, hth19, hth22, hth23, hth24,
    chi_xor_eq, chi0_xor_eq, chi0_xor_after_eq,
    keccakRoundLane, keccakRhoPi, keccakRhoPiSrc, keccakRhoOffset, rotateLeft_zero_64]
  rfl))

set_option maxHeartbeats 800000 in
/-- Step `[0x07fc → 0x09e8]` (second half of round `r`, stopping at branch `+0x09e8`). -/
private theorem round_half2_body_ok [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (sp rcBase out0 out1 : BitVec 64) (r : Nat) (hr : r < 24)
    (st0 st1 : KeccakState) (s : State)
    (hpc : s.pc = b + 0x07fc#64)
    (hregs : MidRegs s sp rcBase out0 out1 r st0 st1) :
    let st0' := keccakF1600Round st0 (keccakRcAt r)
    let st1' := keccakF1600Round st1 (keccakRcAt r)
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x09e8#64) s
      (MidSpillMem sp st0 st1 ∗ (rcBase ↦ᵣ mlkemData01Bytes))
      (sepPost
        (fun sm =>
          LoopRegs sm sp rcBase out0 out1 (r + 1) st0' st1' ∧
            sm.pstate = subsPState64 (BitVec.ofNat 64 (8 * (r + 1))) 192#64)
        (LoopSpillMem sp st0' st1' ∗ (rcBase ↦ᵣ mlkemData01Bytes))) := by
  intro st0' st1'
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx25, hx20, hx19, hx8, hx9, hpstate,
    hv0, hv1, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv13,
    hv16, hv18, hv19, hv21, hv24, hv25, hv27, hv29, hv30, hv31⟩
  dsimp only [keccak2Lane, keccak2D, keccak2Theta, keccak2RhoPi] at *
  have hrc_bound : 8 * r + 8 ≤ mlkemData01Bytes.length := by
    rw [mlkemData01Bytes_length]; omega
  dsimp only [MidSpillMem, LaneSlot]
  refine memRegion16_cells (sp + 176#64) (by sep_focus) fun _q0 _q1 => ?_
  rw [show (sp + 176#64) + 8#64 = sp + 184#64 by bv_omega]
  wp_steps
  apply step_simdLd1r_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · exact (SepLoad64.of_pointsToBytes_readLE_RO (off := 8 * r)
      (by sep_focus) hrc_bound rfl).congr_val (rfl : _ = keccakRcAt r)
  · wp_norm_lhs
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨⟨?_, by wp_norm_lhs⟩, ?_⟩
    · dsimp only [st0', st1']
      refine
        { hrun      := by wp_norm_lhs
          hsp_align := by wp_norm_lhs
          hsp       := by wp_norm_lhs
          hx29      := by wp_norm_lhs
          hx25      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx19      := by wp_norm_lhs
          hx8       := by wp_norm_lhs
          hv18      := by keccak_round_vreg 0
          hv29      := by keccak_round_vreg 5
          hv20      := by keccak_round_vreg 7
          hv10      := by keccak_round_vreg 8
          hv0       := by keccak_round_vreg 9
          hv28      := by keccak_round_vreg 10
          hv12      := by keccak_round_vreg 11
          hv8       := by keccak_round_vreg 12
          hv7       := by keccak_round_vreg 13
          hv13      := by keccak_round_vreg 14
          hv6       := by keccak_round_vreg 15
          hv15      := by keccak_round_vreg 16
          hv11      := by keccak_round_vreg 17
          hv14      := by keccak_round_vreg 18
          hv30      := by keccak_round_vreg 19
          hv27      := by keccak_round_vreg 20
          hv1       := by keccak_round_vreg 21
          hv5       := by keccak_round_vreg 22
          hv25      := by keccak_round_vreg 23
          hv26      := by keccak_round_vreg 24 }
    · simp only [sepConj_assoc]
      have hlanes : ∀ (st : KeccakState) (idx : Nat), idx < 25 →
          (keccakF1600Round st (keccakRcAt r)).getD idx 0#64 =
            keccakRoundLane st (keccakRcAt r) idx :=
        fun st _ hidx => keccakF1600Round_getD st (keccakRcAt r) hidx
      refine Entails.trans ?_
        (cells_to_loopSpillMem sp rcBase st0' st1'
          (q0 := ?_) (q1 := ?_)
          (u0 := ?_) (u1 := ?_) (u2 := ?_) (u3 := ?_) (u4 := ?_) (u5 := ?_) (u6 := ?_) (u7 := ?_)
          (w0 := ?_) (w1 := ?_) (w2 := ?_) (w3 := ?_) (w4 := ?_) (w5 := ?_) (w6 := ?_) (w7 := ?_))
      apply entails_of_eq
      -- Rewrite the 10 active lane cells on LHS, leaving the 18 scratch cells untouched
      dsimp only [st0', st1']
      simp only [hth0, hth9, hth18, hth24,
        chi_xor_eq,
        hlanes st0 1 (by decide), hlanes st1 1 (by decide),
        hlanes st0 2 (by decide), hlanes st1 2 (by decide),
        hlanes st0 3 (by decide), hlanes st1 3 (by decide),
        hlanes st0 4 (by decide), hlanes st1 4 (by decide),
        hlanes st0 6 (by decide), hlanes st1 6 (by decide),
        keccakRoundLane, keccakRhoPi, keccakRhoPiSrc, keccakRhoOffset, rotateLeft_zero_64]
      rfl

private theorem loopRegs_setPC {s : State} {sp rcBase out0 out1 : BitVec 64}
    {r : Nat} {st0 st1 : KeccakState} (pc' : BitVec 64)
    (h : LoopRegs s sp rcBase out0 out1 r st0 st1) :
    LoopRegs (s.setPC pc') sp rcBase out0 out1 r st0 st1 := by
  rcases h with ⟨hrun, hsp_align, hsp, hx29, hx25, hx20, hx19, hx8,
    hv18, hv29, hv20, hv10, hv0, hv28, hv12, hv8, hv7, hv13,
    hv6, hv15, hv11, hv14, hv30, hv27, hv1, hv5, hv25, hv26⟩
  exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

/-- Countdown induction over rounds `r .. 23` (`r ≤ 23`), stepping from `+0x06c8` to `+0x09ec`. -/
private theorem loop_from_ok [MlKemPlacement] (b : BitVec 64)
    (hb : MlKemBase blkPl00 b) (hbase : blkPl00.base = b)
    (sp rcBase out0 out1 : BitVec 64) (rem : Nat) :
    ∀ (r : Nat), rem = 23 - r → r ≤ 23 →
      ∀ (st0 st1 : KeccakState) (s : State),
        s.pc = b + 0x06c8#64 →
        LoopRegs s sp rcBase out0 out1 r st0 st1 →
        SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x09ec#64) s
          (LoopSpillMem sp st0 st1 ∗ (rcBase ↦ᵣ mlkemData01Bytes))
          (sepPost
            (fun sf => LoopRegs sf sp rcBase out0 out1 24
              (keccakRunFrom r st0) (keccakRunFrom r st1))
            (LoopSpillMem sp (keccakRunFrom r st0) (keccakRunFrom r st1) ∗
              (rcBase ↦ᵣ mlkemData01Bytes))) := by
  induction rem with
  | zero =>
    intro r _hrem _hr st0 st1 s hpc hregs
    have hr23 : r = 23 := by omega
    subst hr23
    refine SepWP.bind_sepPost
      (round_half1_ok b hb hbase sp rcBase out0 out1 23 (by decide) st0 st1 s hpc hregs)
      (Entails.refl _) ?_
    intro s1 hpc1 _ hmid
    refine SepWP.bind_sepPost
      (F := emp)
      (round_half2_body_ok b hb hbase sp rcBase out0 out1 23 (by decide) st0 st1 s1 hpc1 hmid)
      (by rw [sepConj_emp]; exact Entails.refl _) ?_
    intro s2 hpc2 hrun2 ⟨hlregs2, hpstate2⟩
    rw [sepConj_emp]
    wp_step
    apply SepWP.done
    · wp_norm_lhs
    · cases s2; exact hrun2
    · rw [sepPost_apply,
          keccakRunFrom_step 23 (by decide) st0,
          keccakRunFrom_step 23 (by decide) st1,
          keccakRunFrom_24, keccakRunFrom_24]
      exact ⟨loopRegs_setPC _ hlregs2, Entails.refl _⟩
  | succ rem ih =>
    intro r _hrem _hr st0 st1 s hpc hregs
    have _hr_lt : r < 23 := by omega
    refine SepWP.bind_sepPost
      (round_half1_ok b hb hbase sp rcBase out0 out1 r (by omega) st0 st1 s hpc hregs)
      (Entails.refl _) ?_
    intro s1 hpc1 _ hmid
    refine SepWP.bind_sepPost
      (F := emp)
      (round_half2_body_ok b hb hbase sp rcBase out0 out1 r (by omega) st0 st1 s1 hpc1 hmid)
      (by rw [sepConj_emp]; exact Entails.refl _) ?_
    intro s2 hpc2 hrun2 ⟨hlregs2, hpstate2⟩
    rw [sepConj_emp]
    wp_step
    wp_if hbr
    · rw [keccakRunFrom_step r (by omega) st0, keccakRunFrom_step r (by omega) st1]
      exact ih (r + 1) (by omega) (by omega)
        (keccakF1600Round st0 (keccakRcAt r)) (keccakF1600Round st1 (keccakRcAt r))
        _ rfl (loopRegs_setPC _ hlregs2)
    · exfalso
      have hne : BitVec.ofNat 64 (8 * (r + 1)) ≠ 192#64 := by bv_omega
      simp [hne] at hbr

public section

/-- Full 24-round `Keccak-f[1600]` loop `[0x06c8 → 0x09ec]` from `r = 0` (`(st0, st1)`) to
    `r = 24` (`(keccakF1600 st0, keccakF1600 st1)`). -/
theorem loop_24_ok [MlKemPlacement] (b : BitVec 64)
    (hb : MlKemBase blkPl00 b) (hbase : blkPl00.base = b)
    (sp rcBase out0 out1 : BitVec 64)
    (st0 st1 : KeccakState) (s : State)
    (hpc : s.pc = b + 0x06c8#64)
    (hregs : LoopRegs s sp rcBase out0 out1 0 st0 st1) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x09ec#64) s
      (LoopSpillMem sp st0 st1 ∗ (rcBase ↦ᵣ mlkemData01Bytes))
      (sepPost
        (fun sf => LoopRegs sf sp rcBase out0 out1 24 (keccakF1600 st0) (keccakF1600 st1))
        (LoopSpillMem sp (keccakF1600 st0) (keccakF1600 st1) ∗
          (rcBase ↦ᵣ mlkemData01Bytes))) := by
  simpa only [keccakRunFrom_zero] using
    loop_from_ok b hb hbase sp rcBase out0 out1 23 0 rfl (by decide) st0 st1 s hpc hregs

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf2
