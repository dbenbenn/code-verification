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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): round first half (`+0x06c8 → +0x07fc`)

Proof of segment `[0x06c8 → 0x07f8]` (`77` instructions) of `mlkemBlk00`, stepping one 2-way
NEON `Keccak-f[1600]` round from loop header `+0x06c8` (`LoopRegs`, `LoopSpillMem`) to mid-round
cut `+0x07fc` (`MidRegs`, `MidSpillMem`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf1

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakRhoOffset
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC
  keccakD
  keccakRhoPi
  keccakRhoPiSrc
  keccakTheta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion64_cells
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
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x06c8 → 0x07f8]

private theorem c_col_eq (st : KeccakState) (x : Nat) :
    ((st.getD (5 + x) 0#64 ^^^ st.getD x 0#64) ^^^
      (st.getD (10 + x) 0#64 ^^^ st.getD (15 + x) 0#64)) ^^^ st.getD (20 + x) 0#64 =
      keccakC st x := by
  dsimp only [keccakC]
  ext i hi
  simp only [BitVec.getElem_xor]
  cases (st.getD x 0#64)[i] <;> cases (st.getD (5 + x) 0#64)[i] <;>
    cases (st.getD (10 + x) 0#64)[i] <;> cases (st.getD (15 + x) 0#64)[i] <;>
    cases (st.getD (20 + x) 0#64)[i] <;> rfl

private theorem hc0 (st : KeccakState) :
    ((st.getD 5 0#64 ^^^ st.getD 0 0#64) ^^^
      (st.getD 10 0#64 ^^^ st.getD 15 0#64)) ^^^ st.getD 20 0#64 = keccakC st 0 :=
  c_col_eq st 0

private theorem hc1 (st : KeccakState) :
    ((st.getD 6 0#64 ^^^ st.getD 1 0#64) ^^^
      (st.getD 11 0#64 ^^^ st.getD 16 0#64)) ^^^ st.getD 21 0#64 = keccakC st 1 :=
  c_col_eq st 1

private theorem hc2 (st : KeccakState) :
    ((st.getD 7 0#64 ^^^ st.getD 2 0#64) ^^^
      (st.getD 12 0#64 ^^^ st.getD 17 0#64)) ^^^ st.getD 22 0#64 = keccakC st 2 :=
  c_col_eq st 2

private theorem hc3 (st : KeccakState) :
    ((st.getD 8 0#64 ^^^ st.getD 3 0#64) ^^^
      (st.getD 13 0#64 ^^^ st.getD 18 0#64)) ^^^ st.getD 23 0#64 = keccakC st 3 :=
  c_col_eq st 3

private theorem hc4 (st : KeccakState) :
    ((st.getD 9 0#64 ^^^ st.getD 4 0#64) ^^^
      (st.getD 14 0#64 ^^^ st.getD 19 0#64)) ^^^ st.getD 24 0#64 = keccakC st 4 :=
  c_col_eq st 4

private theorem hd0 (st : KeccakState) :
    keccakC st 4 ^^^ (keccakC st 1).rotateLeft 1 = keccakD st 0 := rfl

private theorem hd1 (st : KeccakState) :
    (keccakC st 2).rotateLeft 1 ^^^ keccakC st 0 = keccakD st 1 :=
  BitVec.xor_comm _ _

private theorem hd2 (st : KeccakState) :
    (keccakC st 3).rotateLeft 1 ^^^ keccakC st 1 = keccakD st 2 :=
  BitVec.xor_comm _ _

private theorem hd3 (st : KeccakState) :
    (keccakC st 4).rotateLeft 1 ^^^ keccakC st 2 = keccakD st 3 :=
  BitVec.xor_comm _ _

private theorem hd4 (st : KeccakState) :
    keccakC st 3 ^^^ (keccakC st 0).rotateLeft 1 = keccakD st 4 := rfl

private theorem d_xor_lane (st : KeccakState) (x k : Nat) (h : k % 5 = x) :
    keccakD st x ^^^ st.getD k 0#64 = keccakTheta st k := by
  subst h; exact BitVec.xor_comm _ _

private theorem hth1  (st : KeccakState) : keccakD st 1 ^^^ st.getD 1  0#64 = keccakTheta st 1  := d_xor_lane st 1 1 rfl
private theorem hth2  (st : KeccakState) : keccakD st 2 ^^^ st.getD 2  0#64 = keccakTheta st 2  := d_xor_lane st 2 2 rfl
private theorem hth5  (st : KeccakState) : keccakD st 0 ^^^ st.getD 5  0#64 = keccakTheta st 5  := d_xor_lane st 0 5 rfl
private theorem hth6  (st : KeccakState) : keccakD st 1 ^^^ st.getD 6  0#64 = keccakTheta st 6  := d_xor_lane st 1 6 rfl
private theorem hth10 (st : KeccakState) : keccakD st 0 ^^^ st.getD 10 0#64 = keccakTheta st 10 := d_xor_lane st 0 10 rfl
private theorem hth11 (st : KeccakState) : keccakD st 1 ^^^ st.getD 11 0#64 = keccakTheta st 11 := d_xor_lane st 1 11 rfl
private theorem hth12 (st : KeccakState) : keccakD st 2 ^^^ st.getD 12 0#64 = keccakTheta st 12 := d_xor_lane st 2 12 rfl
private theorem hth15 (st : KeccakState) : keccakD st 0 ^^^ st.getD 15 0#64 = keccakTheta st 15 := d_xor_lane st 0 15 rfl
private theorem hth16 (st : KeccakState) : keccakD st 1 ^^^ st.getD 16 0#64 = keccakTheta st 16 := d_xor_lane st 1 16 rfl
private theorem hth17 (st : KeccakState) : keccakD st 2 ^^^ st.getD 17 0#64 = keccakTheta st 17 := d_xor_lane st 2 17 rfl
private theorem hth20 (st : KeccakState) : keccakD st 0 ^^^ st.getD 20 0#64 = keccakTheta st 20 := d_xor_lane st 0 20 rfl
private theorem hth21 (st : KeccakState) : keccakD st 1 ^^^ st.getD 21 0#64 = keccakTheta st 21 := d_xor_lane st 1 21 rfl

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

local macro "keccak_vreg" : tactic => `(tactic| (
  refine Eq.trans (by wp_norm_lhs) ?_
  simp only [BitVec.or_self, hc0, hc1, hc2, hc3, hc4, hd0, hd1, hd2, hd3, hd4,
    hth1, hth2, hth5, hth6, hth10, hth11, hth12, hth15, hth16, hth17, hth20, hth21,
    keccak2Lane, keccak2D, keccak2Theta, keccak2RhoPi,
    keccakRhoPi, keccakRhoPiSrc, keccakRhoOffset]))

public section

/-- Step `[0x06c8 → 0x07fc]` (column parities `C`, `θ` effects `D`, first `θ` XORs, and initial
    `ρ`/`π` rotations for lanes `1, 7, 14, 23`). -/
theorem round_half1_ok [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (sp rcBase out0 out1 : BitVec 64) (r : Nat) (_hr : r < 24)
    (st0 st1 : KeccakState) (s : State)
    (hpc : s.pc = b + 0x06c8#64)
    (hregs : LoopRegs s sp rcBase out0 out1 r st0 st1) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x07fc#64) s
      (LoopSpillMem sp st0 st1)
      (sepPost (fun sm => MidRegs sm sp rcBase out0 out1 r st0 st1)
        (MidSpillMem sp st0 st1)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx25, hx20, hx19, hx8,
    hv18, hv29, hv20, hv10, hv0, hv28, hv12, hv8, hv7, hv13,
    hv6, hv15, hv11, hv14, hv30, hv27, hv1, hv5, hv25, hv26⟩
  dsimp only [keccak2Lane] at *
  dsimp only [LoopSpillMem, LaneSlot]
  refine memRegion64_cells (sp + 240#64) (by sep_focus)
    fun _u0 _u1 _u2 _u3 _u4 _u5 _u6 _u7 => ?_
  refine memRegion64_cells (sp + 320#64) (by sep_focus)
    fun _w0 _w1 _w2 _w3 _w4 _w5 _w6 _w7 => ?_
  rw [show (sp + 320#64) + 8#64 = sp + 328#64 by bv_omega,
      show (sp + 320#64) + 16#64 = sp + 336#64 by bv_omega,
      show (sp + 320#64) + 24#64 = sp + 344#64 by bv_omega,
      show (sp + 320#64) + 32#64 = sp + 352#64 by bv_omega,
      show (sp + 320#64) + 40#64 = sp + 360#64 by bv_omega,
      show (sp + 320#64) + 48#64 = sp + 368#64 by bv_omega,
      show (sp + 320#64) + 56#64 = sp + 376#64 by bv_omega]
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨?_, ?_⟩
    · have hx8' : BitVec.ofNat 64 (8 * r) + 8#64 = BitVec.ofNat 64 (8 * (r + 1)) := by bv_omega
      refine
        { hrun      := by wp_norm_lhs
          hsp_align := by wp_norm_lhs
          hsp       := by wp_norm_lhs
          hx29      := by wp_norm_lhs
          hx25      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx19      := by wp_norm_lhs
          hx8       := by wp_norm_lhs
          hx9       := by wp_norm_lhs
          hpstate   := by wp_norm_lhs
          hv0       := by keccak_vreg
          hv1       := by keccak_vreg
          hv4       := by keccak_vreg
          hv5       := by keccak_vreg
          hv6       := by keccak_vreg
          hv7       := by keccak_vreg
          hv8       := by keccak_vreg
          hv9       := by keccak_vreg
          hv10      := by keccak_vreg
          hv13      := by keccak_vreg
          hv16      := by keccak_vreg
          hv18      := by keccak_vreg
          hv19      := by keccak_vreg
          hv21      := by keccak_vreg
          hv24      := by keccak_vreg
          hv25      := by keccak_vreg
          hv27      := by keccak_vreg
          hv29      := by keccak_vreg
          hv30      := by keccak_vreg
          hv31      := by keccak_vreg }
    · dsimp only [MidSpillMem, LaneSlot]
      apply entails_of_eq
      sep_eq

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf1
