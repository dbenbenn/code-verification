/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public meta import ProofLib.GenDecodes
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Stack Layout, Prologue, and Epilogue

Stack-frame splitting helpers, prologue (`0x6a384..0x6a3e0`), OOM panic block (`+4736`), and
shared epilogue (`0x6b508..0x6b558`) for `<PolyEncoder as Encoder>::next_chunk`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local simp, local arm64_norm, local wp_norm]
theorem bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Callee stack budget below `s0.sp - 1200#64` (`848 + extHookStack = 17,232` bytes). -/
abbrev nextChunkCalleeStack : Nat := 848 + extHookStack

@[local arm64_norm, local wp_norm] theorem sp_sub_1200_add_1104 (sp : BitVec 64) :
    (sp - 1200#64) + 1104#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_968_add_8 (sp : BitVec 64) :
    (sp - 968#64) + 8#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_88_add_8 (sp : BitVec 64) : (sp - 88#64) + 8#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8 (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_72_add_8 (sp : BitVec 64) : (sp - 72#64) + 8#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_56_add_8 (sp : BitVec 64) : (sp - 56#64) + 8#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_40_add_8 (sp : BitVec 64) : (sp - 40#64) + 8#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_24_add_8 (sp : BitVec 64) : (sp - 24#64) + 8#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem setWidth16_zext64_setWidth32 (v : BitVec 64) :
    (((v.setWidth 32).zeroExtend 64).setWidth 16) = v.setWidth 16 := by
  bv_slice

@[local arm64_norm, local wp_norm]
theorem setWidth32_zext64 (x : BitVec 32) :
    (x.zeroExtend 64).setWidth 32 = x := by
  bv_slice

@[local arm64_norm, local wp_norm]
theorem setWidth32_zext64_add_one (idx : BitVec 32) :
    (((idx.zeroExtend 64).setWidth 32 + 1#32).zeroExtend 64).setWidth 32 = idx + 1#32 := by
  simp only [setWidth32_zext64]

@[local arm64_norm, local wp_norm]
theorem extractLsb_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-- The 12 saved register cells at `s0.sp - 96#64 .. s0.sp - 8#64`. -/
@[expose] def savedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_polyNextChunk_split_96 (sp : BitVec 64) :
    stackAt sp polyNextChunkStack =
      stackAt (sp - 96#64) (nextChunkCalleeStack + 1104) ∗ cells (sp - 96#64) 12 := by
  have hEq : polyNextChunkStack = (nextChunkCalleeStack + 1104) + 8 * 12 := rfl
  rw [hEq]
  exact ProofLib.stackAt_split_cells sp (nextChunkCalleeStack + 1104) 12 (by decide)

theorem stackAt_96_split_1104 (sp : BitVec 64) :
    stackAt (sp - 96#64) (nextChunkCalleeStack + 1104) =
      stackAt (sp - 1200#64) nextChunkCalleeStack ∗ memRegion (sp - 1200#64) 1104 := by
  simp only [stackAt]
  rw [memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (nextChunkCalleeStack + 1104))
    nextChunkCalleeStack 1104 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (nextChunkCalleeStack + 1104) =
      (sp - 1200#64) - BitVec.ofNat 64 nextChunkCalleeStack := by
    change (sp - 96#64) - 18336#64 = (sp - 1200#64) - 17232#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (nextChunkCalleeStack + 1104) +
      BitVec.ofNat 64 nextChunkCalleeStack = sp - 1200#64 := by
    change (sp - 96#64) - 18336#64 + 17232#64 = sp - 1200#64
    bv_omega
  rw [h2, h1]

theorem stackAt_nextChunkCallee_split_allocHook (fsp : BitVec 64) :
    stackAt fsp nextChunkCalleeStack =
      memRegion (fsp - 17232#64) 13136 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 13136 (by decide)

theorem stackAt_nextChunkCallee_split_computeAt (fsp : BitVec 64) :
    stackAt fsp nextChunkCalleeStack =
      memRegion (fsp - 17232#64) 12880 ∗ stackAt fsp computeAtStack :=
  stackAt_split_bottom fsp computeAtStack 12880 (by decide)

theorem savedCells_entails_cells12 (s0 : State) :
    savedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold savedCells
  refine cells_sub_succ_entails 96 12 ?_
  refine cells_sub_succ_entails 88 11 ?_
  refine cells_sub_succ_entails 80 10 ?_
  refine cells_sub_succ_entails 72 9 ?_
  refine cells_sub_succ_entails 64 8 ?_
  refine cells_sub_succ_entails 56 7 ?_
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)

theorem savedCells_restore_stack (s0 : State) (R : SepProp) :
    savedCells s0 ∗ stackAt (s0.sp - 96#64) (nextChunkCalleeStack + 1104) ∗ R ⊢
      R ∗ stackAt s0.sp polyNextChunkStack := by
  rw [stackAt_polyNextChunk_split_96 s0.sp]
  refine Entails.trans (sepConj_mono_left (savedCells_entails_cells12 s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem pointsTo32_eq_pointsTo16_pair (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ w) = (a ↦₁₆ w.setWidth 16) ∗ ((a + 2#64) ↦₁₆ (w >>> 16).setWidth 16) := by
  have hsplit : unpack32 w = unpack16 (w.setWidth 16) ++ unpack16 ((w >>> 16).setWidth 16) := by
    simp only [unpack32, unpack16, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩
  rw [pointsTo32_eq_pointsToBytes, hsplit,
      ProofLib.pointsToBytes_append a (unpack16 (w.setWidth 16)) (unpack16 ((w >>> 16).setWidth 16)),
      unpack16_length, ← pointsTo16_eq_pointsToBytes, ← pointsTo16_eq_pointsToBytes]

theorem pointsTo64_eq_pointsTo32_pair (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₃₂ w.setWidth 32) ∗ ((a + 4#64) ↦₃₂ (w >>> 32).setWidth 32) := by
  have hsplit : unpack64 w = unpack32 (w.setWidth 32) ++ unpack32 ((w >>> 32).setWidth 32) := by
    simp only [unpack64, unpack32, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
           by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩
  rw [pointsTo64_eq_pointsToBytes, hsplit,
      ProofLib.pointsToBytes_append a (unpack32 (w.setWidth 32)) (unpack32 ((w >>> 32).setWidth 32)),
      unpack32_length, ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

/-- Pack 8 bytes (little-endian) into a `BitVec 64`. -/
@[expose] def pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs[7]?.getD 0#8) ++ (bs[6]?.getD 0#8) ++ (bs[5]?.getD 0#8) ++ (bs[4]?.getD 0#8) ++
  (bs[3]?.getD 0#8) ++ (bs[2]?.getD 0#8) ++ (bs[1]?.getD 0#8) ++ (bs[0]?.getD 0#8)

theorem unpack64_pack64 {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  simp only [pack64, unpack64, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.cons.injEq, and_true]
  exact ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
         by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem pointsToBytes8_eq_pointsTo64 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 h]

theorem pointsToBytes16_eq_pointsTo64_pair (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 (bs.take 8)) ∗ ((a + 8#64) ↦₆₄ pack64 (bs.drop 8)) := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1,
      pointsToBytes8_eq_pointsTo64 a h1,
      pointsToBytes8_eq_pointsTo64 (a + 8#64) h2]

theorem pointsToBytes32_eq_pointsTo64_four (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 ((bs.take 16).take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 ((bs.take 16).drop 8)) ∗
      ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ pack64 ((bs.drop 16).drop 8)) := by
  have hsplit : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
  have h1 : (bs.take 16).length = 16 := by simp [h]
  have h2 : (bs.drop 16).length = 16 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [ProofLib.pointsToBytes_append a (bs.take 16) (bs.drop 16), h1,
      pointsToBytes16_eq_pointsTo64_pair a h1,
      pointsToBytes16_eq_pointsTo64_pair (a + 16#64) h2]
  have h24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  rw [h24]
  ac_rfl

theorem memRegion_chunkSize_entails_cells (outA : BitVec 64) :
    memRegion outA chunkSize ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ idx0 : BitVec 16,
        (outA ↦₆₄ w0) ∗ ((outA + 8#64) ↦₆₄ w1) ∗
        ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗
        ((outA + 32#64) ↦₁₆ idx0) := by
  unfold chunkSize
  rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 26) (b' := outA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 8) (k := 18) (b' := outA + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 10) (b' := outA + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 2) (b' := outA + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA,
      ProofLib.memRegion_eight (outA + 8#64),
      ProofLib.memRegion_eight (outA + 16#64),
      ProofLib.memRegion_eight (outA + 24#64),
      ProofLib.memRegion_two (outA + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro idx0
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right idx0 (Entails.refl _)))))

theorem sepWP_exists_left_sep {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x : α, SepWP prog target_pc s (P x ∗ Rest) post) :
    SepWP prog target_pc s ((∃∗ x : α, P x) ∗ Rest) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_left h

/-- Untouched regions of the 1,104-byte local frame at `fsp = s0.sp - 1200#64` outside
    `[fsp + 56, fsp + 64)` (`outA`) and `[fsp + 232, fsp + 256)` (`out` `Vec<u8>` header). -/
@[expose] def localFrameRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 56 ∗ memRegion (fsp + 64#64) 168 ∗ memRegion (fsp + 256#64) 848

theorem localFrame_split_prologue (fsp : BitVec 64) :
    memRegion fsp 1104 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u56 : BitVec 64, ∃∗ u232 : BitVec 64, ∃∗ u240 : BitVec 64, ∃∗ u248 : BitVec 64,
        (fsp ↦₆₄ u0) ∗
        ((fsp + 56#64) ↦₆₄ u56) ∗
        ((fsp + 232#64) ↦₆₄ u232) ∗
        ((fsp + 240#64) ↦₆₄ u240) ∗
        ((fsp + 248#64) ↦₆₄ u248) ∗
        memRegion (fsp + 8#64) 48 ∗
        memRegion (fsp + 64#64) 168 ∗
        memRegion (fsp + 256#64) 848 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 1096) (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 48) (k := 1048) (b' := fsp + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 56#64) (n := 8) (k := 1040) (b' := fsp + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 168) (k := 872) (b' := fsp + 232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 232#64) (n := 8) (k := 864) (b' := fsp + 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 240#64) (n := 8) (k := 856) (b' := fsp + 248#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 248#64) (n := 8) (k := 848) (b' := fsp + 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight fsp,
      ProofLib.memRegion_eight (fsp + 56#64),
      ProofLib.memRegion_eight (fsp + 232#64),
      ProofLib.memRegion_eight (fsp + 240#64),
      ProofLib.memRegion_eight (fsp + 248#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u248
  apply Entails.sepExists_elim; intro u240
  apply Entails.sepExists_elim; intro u232
  apply Entails.sepExists_elim; intro u56
  apply Entails.sepExists_elim; intro u0
  exact Entails.sepExists_right u0 (Entails.sepExists_right u56
    (Entails.sepExists_right u232 (Entails.sepExists_right u240
      (Entails.sepExists_right u248 (Entails.of_eq (by ac_rfl))))))

theorem localFrameRest_fold_prologue (fsp : BitVec 64) (v0 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗
    memRegion (fsp + 8#64) 48 ∗
    memRegion (fsp + 64#64) 168 ∗
    memRegion (fsp + 256#64) 848 ⊢
      localFrameRest fsp := by
  unfold localFrameRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 48) (b' := fsp + 8#64) rfl rfl (by decide)]
  rw [← sepConj_assoc]
  exact sepConj_mono_left (sepConj_mono_left (pointsTo64_entails_memRegion fsp v0))

theorem localFrame_rejoin_1104 (fsp : BitVec 64) (v56 v232 v240 v248 : BitVec 64) :
    localFrameRest fsp ∗
    ((fsp + 56#64) ↦₆₄ v56) ∗
    ((fsp + 232#64) ↦₆₄ v232) ∗
    ((fsp + 240#64) ↦₆₄ v240) ∗
    ((fsp + 248#64) ↦₆₄ v248) ⊢
      memRegion fsp 1104 := by
  unfold localFrameRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 56) (k := 1048) (b' := fsp + 56#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 56#64) (n := 8) (k := 1040) (b' := fsp + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 168) (k := 872) (b' := fsp + 232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 232#64) (n := 8) (k := 864) (b' := fsp + 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 240#64) (n := 8) (k := 856) (b' := fsp + 248#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 248#64) (n := 8) (k := 848) (b' := fsp + 256#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show
    (memRegion fsp 56 ∗ memRegion (fsp + 64#64) 168 ∗ memRegion (fsp + 256#64) 848) ∗
      ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 232#64) ↦₆₄ v232) ∗
      ((fsp + 240#64) ↦₆₄ v240) ∗ ((fsp + 248#64) ↦₆₄ v248) =
    memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ memRegion (fsp + 64#64) 168 ∗
      ((fsp + 232#64) ↦₆₄ v232) ∗ ((fsp + 240#64) ↦₆₄ v240) ∗
      ((fsp + 248#64) ↦₆₄ v248) ∗ memRegion (fsp + 256#64) 848 by ac_rfl)) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion (fsp + 56#64) v56) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion (fsp + 232#64) v232) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion (fsp + 240#64) v240) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion (fsp + 248#64) v248) (Entails.refl _)

theorem restore_full_stack (s0 : State) (v56 v232 v240 v248 : BitVec 64) (R : SepProp) :
    savedCells s0 ∗
    memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
    stackAt (s0.sp - 1200#64) allocHookStack ∗
    localFrameRest (s0.sp - 1200#64) ∗
    (((s0.sp - 1200#64) + 56#64) ↦₆₄ v56) ∗
    (((s0.sp - 1200#64) + 232#64) ↦₆₄ v232) ∗
    (((s0.sp - 1200#64) + 240#64) ↦₆₄ v240) ∗
    (((s0.sp - 1200#64) + 248#64) ↦₆₄ v248) ∗ R ⊢
      R ∗ stackAt s0.sp polyNextChunkStack := by
  have hcallee :
      memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗ stackAt (s0.sp - 1200#64) allocHookStack =
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack :=
    (stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64)).symm
  refine Entails.trans (Entails.of_eq (show
    savedCells s0 ∗ memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
      stackAt (s0.sp - 1200#64) allocHookStack ∗ localFrameRest (s0.sp - 1200#64) ∗
      (((s0.sp - 1200#64) + 56#64) ↦₆₄ v56) ∗ (((s0.sp - 1200#64) + 232#64) ↦₆₄ v232) ∗
      (((s0.sp - 1200#64) + 240#64) ↦₆₄ v240) ∗ (((s0.sp - 1200#64) + 248#64) ↦₆₄ v248) ∗ R =
    savedCells s0 ∗
      (memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗ stackAt (s0.sp - 1200#64) allocHookStack) ∗
      (localFrameRest (s0.sp - 1200#64) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ v56) ∗ (((s0.sp - 1200#64) + 232#64) ↦₆₄ v232) ∗
        (((s0.sp - 1200#64) + 240#64) ↦₆₄ v240) ∗ (((s0.sp - 1200#64) + 248#64) ↦₆₄ v248)) ∗ R by ac_rfl)) ?_
  rw [hcallee]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (localFrame_rejoin_1104 (s0.sp - 1200#64) v56 v232 v240 v248)))) ?_
  have h1104 := (stackAt_96_split_1104 s0.sp).symm
  refine Entails.trans (Entails.of_eq (show
    savedCells s0 ∗ stackAt (s0.sp - 1200#64) nextChunkCalleeStack ∗
      memRegion (s0.sp - 1200#64) 1104 ∗ R =
    savedCells s0 ∗
      (stackAt (s0.sp - 1200#64) nextChunkCalleeStack ∗ memRegion (s0.sp - 1200#64) 1104) ∗ R by ac_rfl)) ?_
  rw [h1104]
  exact savedCells_restore_stack s0 R

/-! ## 2. Shared Epilogue (`0x6b508..0x6b558`, offset `+4484`, 21 insns) -/

/-- Common `onPanic` postcondition for `polyNextChunkSpec`. -/
abbrev nextChunkOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem sepWPp_pure_mid {prog : Program} {target_pc : BitVec 64}
    {s : State} {L1 L2 R : SepProp} {φ : Prop}
    {Q Q_panic : State → SepProp → Prop}
    (h : φ → SepWPp prog target_pc s (L1 ∗ L2 ∗ R) Q Q_panic) :
    SepWPp prog target_pc s (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) Q Q_panic := by
  have heq : (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) = (⌜φ⌝ ∗ (L1 ∗ L2 ∗ R)) := by ac_rfl
  rw [heq]
  exact SepWPp.pure_left h

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_one :
    (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_1104 (sp : BitVec 64) :
    (sp - 96#64) - 1104#64 = sp - 1200#64 := by bv_omega

theorem prologue_stack_split (s0 : State) :
    stackAt s0.sp polyNextChunkStack ⊢
      ∃∗ v29 : BitVec 64, ∃∗ v30 : BitVec 64, ∃∗ v28 : BitVec 64, ∃∗ v27 : BitVec 64,
      ∃∗ v26 : BitVec 64, ∃∗ v25 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v23 : BitVec 64,
      ∃∗ v22 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v19 : BitVec 64,
      ∃∗ u0 : BitVec 64, ∃∗ u56 : BitVec 64, ∃∗ u232 : BitVec 64, ∃∗ u240 : BitVec 64, ∃∗ u248 : BitVec 64,
        ((s0.sp - 96#64) ↦₆₄ v29) ∗ ((s0.sp - 88#64) ↦₆₄ v30) ∗
        ((s0.sp - 80#64) ↦₆₄ v28) ∗ ((s0.sp - 72#64) ↦₆₄ v27) ∗
        ((s0.sp - 64#64) ↦₆₄ v26) ∗ ((s0.sp - 56#64) ↦₆₄ v25) ∗
        ((s0.sp - 48#64) ↦₆₄ v24) ∗ ((s0.sp - 40#64) ↦₆₄ v23) ∗
        ((s0.sp - 32#64) ↦₆₄ v22) ∗ ((s0.sp - 24#64) ↦₆₄ v21) ∗
        ((s0.sp - 16#64) ↦₆₄ v20) ∗ ((s0.sp - 8#64) ↦₆₄ v19) ∗
        ((s0.sp - 1200#64) ↦₆₄ u0) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ u56) ∗
        (((s0.sp - 1200#64) + 232#64) ↦₆₄ u232) ∗
        (((s0.sp - 1200#64) + 240#64) ↦₆₄ u240) ∗
        (((s0.sp - 1200#64) + 248#64) ↦₆₄ u248) ∗
        memRegion ((s0.sp - 1200#64) + 8#64) 48 ∗
        memRegion ((s0.sp - 1200#64) + 64#64) 168 ∗
        memRegion ((s0.sp - 1200#64) + 256#64) 848 ∗
        memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
        stackAt (s0.sp - 1200#64) allocHookStack := by
  rw [stackAt_polyNextChunk_split_96 s0.sp,
      stackAt_96_split_1104 s0.sp,
      stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64),
      cells_sub_succ s0.sp 96 12 (by decide) (by decide),
      cells_sub_succ s0.sp 88 11 (by decide) (by decide),
      cells_sub_succ s0.sp 80 10 (by decide) (by decide),
      cells_sub_succ s0.sp 72 9 (by decide) (by decide),
      cells_sub_succ s0.sp 64 8 (by decide) (by decide),
      cells_sub_succ s0.sp 56 7 (by decide) (by decide),
      cells_sub_succ s0.sp 48 6 (by decide) (by decide),
      cells_sub_succ s0.sp 40 5 (by decide) (by decide),
      cells_sub_succ s0.sp 32 4 (by decide) (by decide),
      cells_sub_succ s0.sp 24 3 (by decide) (by decide),
      cells_sub_succ s0.sp 16 2 (by decide) (by decide),
      cells_sub_succ s0.sp 8 1 (by decide) (by decide),
      cells_zero]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right
    (localFrame_split_prologue (s0.sp - 1200#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]
  apply Entails.sepExists_elim; intro v29
  apply Entails.sepExists_elim; intro v30
  apply Entails.sepExists_elim; intro v28
  apply Entails.sepExists_elim; intro v27
  apply Entails.sepExists_elim; intro v26
  apply Entails.sepExists_elim; intro v25
  apply Entails.sepExists_elim; intro v24
  apply Entails.sepExists_elim; intro v23
  apply Entails.sepExists_elim; intro v22
  apply Entails.sepExists_elim; intro v21
  apply Entails.sepExists_elim; intro v20
  apply Entails.sepExists_elim; intro v19
  apply Entails.sepExists_elim; intro u0
  apply Entails.sepExists_elim; intro u56
  apply Entails.sepExists_elim; intro u232
  apply Entails.sepExists_elim; intro u240
  apply Entails.sepExists_elim; intro u248
  exact Entails.sepExists_right v29 (Entails.sepExists_right v30
    (Entails.sepExists_right v28 (Entails.sepExists_right v27
      (Entails.sepExists_right v26 (Entails.sepExists_right v25
        (Entails.sepExists_right v24 (Entails.sepExists_right v23
          (Entails.sepExists_right v22 (Entails.sepExists_right v21
            (Entails.sepExists_right v20 (Entails.sepExists_right v19
              (Entails.sepExists_right u0 (Entails.sepExists_right u56
                (Entails.sepExists_right u232 (Entails.sepExists_right u240
                  (Entails.sepExists_right u248 (Entails.of_eq (by ac_rfl))))))))))))))))))

end CryptoVerification.SpqrV1.Poly.NextChunk
