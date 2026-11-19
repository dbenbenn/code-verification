/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.SepLogic.WP.Apply

/-!
# Constant-Time Slice Equality with a Read-Only Second Operand

Verifies `<[u8] as subtle::ConstantTimeEq>::ct_eq` (`0x3ecc4`, Block `213`) when the second 32-byte
slice resides in read-only `.rodata` (`p2 ↦ᵣ k2`), providing relocatable `[LibsignalPlacement]`
contracts (`ct_eq_ro_placed_ok`, `ct_eq_ro_mem_placed_ok`, `ct_eq_cells_placed_ok`,
`ct_eq_mem_placed_ok`, and `publicKey_eq_mem_placed_ok`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSession.FindReceiverChainIndex
open CryptoVerification.LibsignalTripleRatchetRepr CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet (ctEqSliceROSpec)

/-- Read-only analogue of `pointsToBytes32`: a 32-byte read-only slice as 32 `↦₈ᵣ` cells. -/
@[expose] def pointsToBytesRO32 (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₈ᵣ bs.getD 0 0#8) ∗ ((a + 1#64) ↦₈ᵣ bs.getD 1 0#8) ∗
  ((a + 2#64) ↦₈ᵣ bs.getD 2 0#8) ∗ ((a + 3#64) ↦₈ᵣ bs.getD 3 0#8) ∗
  ((a + 4#64) ↦₈ᵣ bs.getD 4 0#8) ∗ ((a + 5#64) ↦₈ᵣ bs.getD 5 0#8) ∗
  ((a + 6#64) ↦₈ᵣ bs.getD 6 0#8) ∗ ((a + 7#64) ↦₈ᵣ bs.getD 7 0#8) ∗
  ((a + 8#64) ↦₈ᵣ bs.getD 8 0#8) ∗ ((a + 9#64) ↦₈ᵣ bs.getD 9 0#8) ∗
  ((a + 10#64) ↦₈ᵣ bs.getD 10 0#8) ∗ ((a + 11#64) ↦₈ᵣ bs.getD 11 0#8) ∗
  ((a + 12#64) ↦₈ᵣ bs.getD 12 0#8) ∗ ((a + 13#64) ↦₈ᵣ bs.getD 13 0#8) ∗
  ((a + 14#64) ↦₈ᵣ bs.getD 14 0#8) ∗ ((a + 15#64) ↦₈ᵣ bs.getD 15 0#8) ∗
  ((a + 16#64) ↦₈ᵣ bs.getD 16 0#8) ∗ ((a + 17#64) ↦₈ᵣ bs.getD 17 0#8) ∗
  ((a + 18#64) ↦₈ᵣ bs.getD 18 0#8) ∗ ((a + 19#64) ↦₈ᵣ bs.getD 19 0#8) ∗
  ((a + 20#64) ↦₈ᵣ bs.getD 20 0#8) ∗ ((a + 21#64) ↦₈ᵣ bs.getD 21 0#8) ∗
  ((a + 22#64) ↦₈ᵣ bs.getD 22 0#8) ∗ ((a + 23#64) ↦₈ᵣ bs.getD 23 0#8) ∗
  ((a + 24#64) ↦₈ᵣ bs.getD 24 0#8) ∗ ((a + 25#64) ↦₈ᵣ bs.getD 25 0#8) ∗
  ((a + 26#64) ↦₈ᵣ bs.getD 26 0#8) ∗ ((a + 27#64) ↦₈ᵣ bs.getD 27 0#8) ∗
  ((a + 28#64) ↦₈ᵣ bs.getD 28 0#8) ∗ ((a + 29#64) ↦₈ᵣ bs.getD 29 0#8) ∗
  ((a + 30#64) ↦₈ᵣ bs.getD 30 0#8) ∗ ((a + 31#64) ↦₈ᵣ bs.getD 31 0#8)

theorem pointsToBytesRO_drop_step (a : BitVec 64) (bs : List (BitVec 8)) (i : Nat)
    (hi : i < bs.length) :
    ((a + BitVec.ofNat 64 i) ↦ᵣ bs.drop i) =
      ((a + BitVec.ofNat 64 i) ↦₈ᵣ bs.getD i 0#8) ∗
      ((a + BitVec.ofNat 64 (i + 1)) ↦ᵣ bs.drop (i + 1)) := by
  have hdrop : bs.drop i = bs.getD i 0#8 :: bs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    simp [List.getD, List.getElem?_eq_getElem hi]
  have hadd : a + BitVec.ofNat 64 i + 1#64 = a + BitVec.ofNat 64 (i + 1) := by bv_omega
  rw [hdrop, pointsToBytesRO_cons, hadd]

theorem pointsToBytesRO_eq_pointsToBytesRO32 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 32) :
    (a ↦ᵣ bs) = pointsToBytesRO32 a bs := by
  have h0 : (a ↦ᵣ bs) = ((a + BitVec.ofNat 64 0) ↦ᵣ bs.drop 0) := by simp
  rw [h0]
  iterate 32 (rw [pointsToBytesRO_drop_step a bs _ (by omega)])
  have h32 : bs.drop 32 = [] := by simp [h]
  rw [h32, pointsToBytesRO_nil, sepConj_emp]
  unfold pointsToBytesRO32
  simp only [BitVec.add_zero]

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

-- `ct_eq` bit-manipulation normalization lemmas (`local simp` in `CtEq.lean`).
attribute [local simp] byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0 and64_mask32_ite_1_0
  and32_ite_1_0 and32_1_ite_1_0 Bool.and_assoc

attribute [local irreducible] Program.fnOff

attribute [local simp, local wp_norm, local arm64_norm]
  setWidth8_ite_prop_1_0_ext32 setWidth8_ite_1_0_32_ext32 setWidth8_zext64_32_ext32
  setWidth8_setWidth32_ext32 setWidth8_and64_ext32 setWidth8_and32_ext32
  ite_one_zero_and_8_ext32 setWidth32_and_4294967297_ext32 ite_one_zero_and_one_8_ext32
  zeroExtend32_ite_one_zero_8_ext32 zeroExtend32_ite_prop_1_0_8_ext32

/-- Read-only second-slice `ct_eq` contract with `extHookStack32 = 16384` B below `ct_eq`'s
48-byte frame, returning 32-bit `(sf.readReg64 .x0).setWidth 32 = (if k1 = k2 then 1#32 else 0#32)`. -/
@[expose] def ctEqSliceROSpecExt :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗
      stackFrameAt sp 48 ∗
      stackAt (sp - 48#64) extHookStack32
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = (if k1 = k2 then 1#32 else 0#32) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗
      stackFrameAt sp 48 ∗
      stackAt (sp - 48#64) extHookStack32

/-- Relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`)
with a read-only second operand (`ctEqSliceROSpec`). -/
theorem ct_eq_ro_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceROSpec := by
  simp only [ctEqSliceROSpec]
  have hext : ((blkPC_213).rebase (blkPl_213).base H).externAt? (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
    (ls_externAt?_of_mem).trans h_bb
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytesRO_eq_pointsToBytesRO32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32 pointsToBytesRO32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

theorem ct_eq_ro_placed_ok_withLsCodeLoaded [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_placed_ok h_bb)

private theorem memRegion_48_eq_cells6 (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6 :=
  memRegion_cells (sp - 48#64) 6 (by decide)

/-- Image-free relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq`
(Block `213`) with a read-only second operand (`ctEqSliceROMemSpec`). -/
theorem ct_eq_ro_mem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceROMemSpec := by
  simp only [ctEqSliceROMemSpec, memRegion_48_eq_cells6]
  cells_unfold
  have hext : ((blkPC_213).rebase (blkPl_213).base H).externAt? (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
    (ls_externAt?_of_mem).trans h_bb
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytesRO_eq_pointsToBytesRO32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32 pointsToBytesRO32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

theorem ct_eq_ro_mem_placed_ok_withLsCodeLoaded [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_mem_placed_ok h_bb)

/-- Image-free read-write `ct_eq` contract with `cells (sp - 48#64) 6` frame. -/
@[expose] def ctEqSliceCellsSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6

/-- Image-free relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq`
(Block `213`) with read-write operands and `cells (sp - 48#64) 6` frame. -/
theorem ct_eq_cells_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceCellsSpec := by
  simp only [ctEqSliceCellsSpec]
  cells_unfold
  have hext : ((blkPC_213).rebase (blkPl_213).base H).externAt? (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
    (ls_externAt?_of_mem).trans h_bb
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

/-- Image-free read-write `ct_eq` contract with `memRegion (sp - 48#64) 48` frame. -/
@[expose] def ctEqSliceMemSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 48#64) 48
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 48#64) 48

/-- Image-free relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq`
(Block `213`) with `memRegion (sp - 48#64) 48` frame. -/
theorem ct_eq_mem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceMemSpec := by
  refine subroutine_ok_map (ct_eq_cells_placed_ok h_bb) ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · simpa only [ctEqSliceMemSpec, ctEqSliceCellsSpec, memRegion_48_eq_cells6] using hpre
  · intro sf hpost
    simpa only [ctEqSliceMemSpec, ctEqSliceCellsSpec, memRegion_48_eq_cells6] using hpost

private theorem memRegion_16_eq_cells2 (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 = cells (sp - 16#64) 2 :=
  memRegion_cells (sp - 16#64) 2 (by decide)

attribute [local simp] publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

/-- Image-free relocatable `[LibsignalPlacement]` contract for
`<PublicKey as PartialEq>::eq` (Block `212`) on `publicKeyEqMemSpec`. -/
theorem publicKey_eq_mem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) := by
  simp only [withLsCodeLoaded, publicKeyEqMemSpec, memRegion_16_eq_cells2]
  cells_unfold
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213) ctEqSliceMemSpec :=
    ct_eq_mem_placed_ok h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, ctEqSliceMemSpec] at hct
  wp_init x s0
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  apply sepWP_seq_lscl h (mid := lsmpl.base 213)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_call
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

