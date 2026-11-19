/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

/-!
# `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x5e730`, `85` instructions)

**Checked by Lean.** Verifies `send_ct2_encoder_ok_4K` under `AllocContracts4K`,
`send_ct2_encoder_ok_ext` under `AllocContracts`, and `.inImage img` / `StatesRecvContractsAx` lifts.
-/

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Recv (growToCalleeExt)
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x63b28..0x63c78`) -/

@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_432 (sp : BitVec 64) :
    (sp - 80#64) - 432#64 = sp - 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_432 (sp : BitVec 64) :
    (sp - 512#64) + 432#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_8 (sp : BitVec 64) :
    (sp - 512#64) + 8#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_16 (sp : BitVec 64) :
    (sp - 512#64) + 16#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_24 (sp : BitVec 64) :
    (sp - 512#64) + 24#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_32 (sp : BitVec 64) :
    (sp - 512#64) + 32#64 = sp - 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_504_add_8 (sp : BitVec 64) :
    (sp - 504#64) + 8#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_504_add_16 (sp : BitVec 64) :
    (sp - 504#64) + 16#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_496_add_8 (sp : BitVec 64) :
    (sp - 496#64) + 8#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8 (sp : BitVec 64) :
    (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_16 (sp : BitVec 64) :
    (sp - 80#64) + 16#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_24 (sp : BitVec 64) :
    (sp - 80#64) + 24#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_32 (sp : BitVec 64) :
    (sp - 80#64) + 32#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_40 (sp : BitVec 64) :
    (sp - 80#64) + 40#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_48 (sp : BitVec 64) :
    (sp - 80#64) + 48#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_56 (sp : BitVec 64) :
    (sp - 80#64) + 56#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_64 (sp : BitVec 64) :
    (sp - 80#64) + 64#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_72 (sp : BitVec 64) :
    (sp - 80#64) + 72#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_80 (sp : BitVec 64) :
    (sp - 80#64) + 80#64 = sp := by bv_omega

/-- Saved callee-saved registers at `s0.sp - 80#64 .. s0.sp - 8#64` (`[s0.sp - 56#64]` holds `d56`). -/
@[expose] def sendCt2SavedCells (s0 : State) (d56 : BitVec 64) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ d56) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem fold_sendCt2SavedCells (s0 : State) (d56 : BitVec 64) :
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ d56) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    sendCt2SavedCells s0 d56 :=
  Entails.refl _

theorem sendCt2SavedCells_entails_memRegion_80 (s0 : State) (d56 : BitVec 64) :
    sendCt2SavedCells s0 d56 ⊢ memRegion (s0.sp - 80#64) 80 := by
  have heq : sendCt2SavedCells s0 d56 =
      wordsAt (s0.sp - 80#64)
        [s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x28, d56,
         s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
         s0.readReg64 .x20, s0.readReg64 .x19] := by
    unfold sendCt2SavedCells
    simp only [wordsAt_10, arm64_norm]
  rw [heq]
  exact wordsAt_entails_memRegion _ (s0.sp - 80#64) 80 rfl

theorem stackAt_sendCt2Encoder_split (sp : BitVec 64) :
    stackAt sp sendCt2EncoderStack =
      stackAt (sp - 512#64) encodeBytesStackX ∗
      memRegion (sp - 512#64) 8 ∗
      cells (sp - 504#64) 3 ∗
      memRegion (sp - 480#64) 400 ∗
      cells (sp - 80#64) 10 := by
  change memRegion (sp - 17456#64) 17456 =
    memRegion (sp - 512#64 - 16944#64) 16944 ∗
    memRegion (sp - 512#64) 8 ∗
    cells (sp - 504#64) 3 ∗
    memRegion (sp - 480#64) 400 ∗
    cells (sp - 80#64) 10
  have hsub : sp - 512#64 - 16944#64 = sp - 17456#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_cells (sp - 504#64) 3 (by decide),
      ← ProofLib.memRegion_cells (sp - 80#64) 10 (by decide),
      ProofLib.memRegion_split' (b := sp - 17456#64) (n := 16944) (k := 512) (b' := sp - 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 512#64) (n := 8) (k := 504) (b' := sp - 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 504#64) (n := 24) (k := 480) (b' := sp - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 400) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]

theorem stackAt_512_recompose (s0 : State) (w0 w1 w2 d56 : BitVec 64) :
    stackAt (s0.sp - 512#64) encodeBytesStackX ∗
      memRegion (s0.sp - 512#64) 8 ∗
      (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) ∗
      memRegion (s0.sp - 480#64) 400 ∗
      sendCt2SavedCells s0 d56 ⊢
    stackAt s0.sp sendCt2EncoderStack := by
  have h3 :
      (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) ⊢
      memRegion (s0.sp - 504#64) 24 := by
    have heq :
        (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) =
        wordsAt (s0.sp - 504#64) [w0, w1, w2] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2] (s0.sp - 504#64) 24 rfl
  have h10 := sendCt2SavedCells_entails_memRegion_80 s0 d56
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono h3 (sepConj_mono_right h10)))) ?_
  change memRegion (s0.sp - 512#64 - 16944#64) 16944 ∗
      (memRegion (s0.sp - 512#64) 8 ∗ (memRegion (s0.sp - 504#64) 24 ∗
        (memRegion (s0.sp - 480#64) 400 ∗ memRegion (s0.sp - 80#64) 80))) ⊢
    memRegion (s0.sp - 17456#64) 17456
  have hsub : s0.sp - 512#64 - 16944#64 = s0.sp - 17456#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 400) (k := 80) (b' := s0.sp - 80#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 504#64) (n := 24) (k := 480) (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 512#64) (n := 8) (k := 504) (b' := s0.sp - 504#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17456#64) (n := 16944) (k := 512) (b' := s0.sp - 512#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encodeBytesStackX ⊢
    memRegion (fsp - 16944#64) 12848 ∗ stackAt fsp allocHookStack := by
  change memRegion (fsp - 16944#64) 16944 ⊢
    memRegion (fsp - 16944#64) 12848 ∗ memRegion (fsp - 4096#64) 4096
  rw [ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12848) (k := 4096) (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_from_allocHook (fsp : BitVec 64) :
    memRegion (fsp - 16944#64) 12848 ∗ stackAt fsp allocHookStack ⊢
    stackAt fsp encodeBytesStackX := by
  change memRegion (fsp - 16944#64) 12848 ∗ memRegion (fsp - 4096#64) 4096 ⊢
    memRegion (fsp - 16944#64) 16944
  rw [← ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12848) (k := 4096) (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_to_doReserve (fsp : BitVec 64) :
    stackAt fsp encodeBytesStackX ⊢
    memRegion (fsp - 16944#64) 12736 ∗ stackAt fsp doReserveStack := by
  change memRegion (fsp - 16944#64) 16944 ⊢
    memRegion (fsp - 16944#64) 12736 ∗ memRegion (fsp - 4208#64) 4208
  rw [ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12736) (k := 4208) (b' := fsp - 4208#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_from_doReserve (fsp : BitVec 64) :
    memRegion (fsp - 16944#64) 12736 ∗ stackAt fsp doReserveStack ⊢
    stackAt fsp encodeBytesStackX := by
  change memRegion (fsp - 16944#64) 12736 ∗ memRegion (fsp - 4208#64) 4208 ⊢
    memRegion (fsp - 16944#64) 16944
  rw [← ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12736) (k := 4208) (b' := fsp - 4208#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_sendCt2Encoder_to_allocHook (sp : BitVec 64) :
    stackAt sp sendCt2EncoderStack ⊢
    memRegion (sp - 17456#64) 13360 ∗ stackAt sp allocHookStack := by
  change memRegion (sp - 17456#64) 17456 ⊢
    memRegion (sp - 17456#64) 13360 ∗ memRegion (sp - 4096#64) 4096
  rw [ProofLib.memRegion_split' (b := sp - 17456#64) (n := 13360) (k := 4096) (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_sendCt2Encoder_from_allocHook (sp : BitVec 64) :
    memRegion (sp - 17456#64) 13360 ∗ stackAt sp allocHookStack ⊢
    stackAt sp sendCt2EncoderStack := by
  change memRegion (sp - 17456#64) 13360 ∗ memRegion (sp - 4096#64) 4096 ⊢
    memRegion (sp - 17456#64) 17456
  rw [← ProofLib.memRegion_split' (b := sp - 17456#64) (n := 13360) (k := 4096) (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- `encodeBytesSpec A` entails `encodeBytesSpecX A` by framing the unused bottom stack region. -/
theorem encodeBytesSpecX_of_encodeBytesSpec' {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (encodeBytesSpec A)) :
    subroutine_ok P addr (encodeBytesSpecX A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre' : s0.mem ⊨ (encodeBytesSpec A).pre x s0 ∗ R' := by
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
          (encodeBytesStackX - encodeBytesStack) ∗ R) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc anyHeap]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [encodeBytesSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem slice_and_vecU8Tail_eq_doReserveBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (h0 : cap = 0#64 → bs = []) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs =
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Tail
  by_cases hc : cap = 0#64
  · subst hc
    rw [h0 rfl]
    simp [pointsToBytes_nil]
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcb, Bool.false_eq_true, ↓reduceIte]
    ac_rfl

theorem polyEncoderAt_split_tag (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    ∃ tag : BitVec 64, (tag = 0#64 ∨ tag = 1#64) ∧
      ∃ rest : SepProp, polyEncoderAt A a enc = (a ↦₆₄ tag) ∗ rest := by
  unfold polyEncoderAt encoderStateAt
  cases enc.s with
  | points pts =>
    dsimp only [polyEncoderPointsTag]
    exact ⟨0#64, Or.inl rfl,
      ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
        pointListOf A (a + polyEncoderVecsOff) pts ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize, by ac_rfl⟩
  | polys polys =>
    dsimp only [polyEncoderPolysTag]
    exact ⟨1#64, Or.inr rfl,
      ⌜polys.length = NUM_POLYS⌝ ∗ polyListOf A (a + polyEncoderVecsOff) polys ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize, by ac_rfl⟩

/-! ## 3. Framed Call Rules (`call_memcpy_relocate_cs`, `call_doReserve7Raw`, `call_encodeBytesX`) -/

/-- Framed `memcpy` call rule that relocates any `Relocatable n F` predicate from `src` to `dst`,
leaving `memRegion src n` at `src`, and forwards `CalleeSavedPreserved s sf`. -/
theorem call_memcpy_relocate_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `doReserveRawSpec A` (`0x530a0`). -/
theorem call_doReserve7Raw {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (doReserveRawSpec A))
    (v cap ptr : BitVec 64) (bs : Bytes) (additional : Nat)
    (hlen : bs.length ≤ cap.toNat) (hptr : ptr ≠ 0#64)
    (h0 : cap = 0#64 → bs = [])
    (hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = v)
    (hx1 : (s.readReg64 Reg.x1).toNat = bs.length)
    (hx2 : (s.readReg64 Reg.x2).toNat = additional)
    (hx3 : s.readReg64 Reg.x3 = 1#64)
    (hx4 : s.readReg64 Reg.x4 = 1#64)
    (hsplit : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ∗
      A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      let newCap := reserveCap cap.toNat bs.length additional
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      p' ≠ 0#64 →
      SepWP prog next_pc sf
        (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' newCap 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨v, cap, ptr, bs, additional⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [doReserveRawSpec]
    rw [hsp, ← slice_and_vecU8Tail_eq_doReserveBuf A cap ptr bs h0]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [doReserveRawSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    wp_pull_exists; rename_i p'
    wp_focus_pure; intro hp'
    have hassoc :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame =
        (v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf p' hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hp'

/-- Framed call rule for `encodeBytesSpecX A` (`0x6b6b8`) when `encodeBytesResult msg = .ok outEnc`. -/
theorem call_encodeBytesX {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (encodeBytesSpecX A))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = out)
    (hx0 : s.readReg64 Reg.x0 = msgA)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨out, false, msgA, msg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encodeBytesSpecX, polyEncoderSize, bytesAt]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [encodeBytesSpecX]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    change SepWPp prog (s0.readReg64 Reg.lr) sf
      (⌜sf.trace = s.trace⌝ ∗
        ((polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame)) post _
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
        (polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `rustAllocSpec A` (`__rust_alloc`). -/
theorem call_rustAlloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustAllocSpec A))
    (size align : Nat) (hlay : LayoutOk size align)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((if sf.readReg64 .x0 = 0 then
            ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else
            ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [rustAllocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustAllocSpec]
    rw [hsp, htrace]
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack ∗
          (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)) ∗ Frame =
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf

private theorem call_memcpy_relocate_cs_4K {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withStack sessionMemcpyRegionSpec encodeBytesStackX))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((F dst ∗ memRegion src n) ∗ (stackAt sp_call encodeBytesStackX ∗ Frame)) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit, show (memRegion dst n ∗ F src ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
      (memRegion dst n ∗ F src) ∗ (stackAt sp_call encodeBytesStackX ∗ Frame) by sep_frame]
  refine SepWP.fold
    (relocate_pre_entails hrel dst src (stackAt sp_call encodeBytesStackX ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec] at h
      exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using h)).1)
    (fun _ _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec] at h
      exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using h)).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp, hlen, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_frame)) hm⟩
  · dsimp only [withStack, sessionMemcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt sp_call encodeBytesStackX ∗
          (relocatedHeap F bs ∗ Frame) =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ relocatedHeap F bs ∗
          (stackAt sp_call encodeBytesStackX ∗ Frame) := by sep_frame
    rw [hreord]
    refine SepWP.fold
      (relocate_post_entails dst src hlen (stackAt sp_call encodeBytesStackX ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 4. Encoder Generation & Buffer Deallocation (`entry + 100#64` = `0x5e6b0`) -/

end CryptoVerification.SpqrV1.States.Leaves
