/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment: Basic-Block `SepWP` Stepping Lemmas

Instruction-level `SepWP` stepping lemmas (`commit_step1_wp` .. `commit_step5_wp`) and relocatable
`[LibsignalPlacement]` `DhCommitBlockWp` instances for blocks `130` (`159`) and `433` (`549`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DhCommitFacts

theorem writeReg64_trace (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := rfl
theorem writeReg32_trace (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := rfl
theorem setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl
theorem setPState_trace (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl
theorem setMem_trace (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl

@[simp, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl

end DhCommitFacts

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    DhCommitFacts.writeReg64_trace, DhCommitFacts.writeReg32_trace, DhCommitFacts.setPC_trace,
    DhCommitFacts.setPState_trace, DhCommitFacts.setMem_trace, State.trace_writeVReg128,
    *])

/-! ## 7. Sub-Segment 1: `+0x8ac .. +0x8f8` (`commit_step1_wp`) -/

local macro "wp_done_reg" hsp_al:ident : tactic =>
  `(tactic| (
    wp_steps
    refine SepWP.done (by rfl) (by wp_reg) ?_
    refine And.intro (by wp_reg) (And.intro (DhCommitFacts.spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
    repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
    try rw [← saturating_sub_one_u32 _]
    exact Entails.refl _))

set_option maxHeartbeats 1600000 in
theorem dhCommitBlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base (lsmpl.base 142) where
  step1 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28; wp_done_reg hsp_align
  step2_pre_shim := by intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24; wp_done_reg hsp_align
  step2_pre_alloc := by intro _ s hpc hrun hsp hsp_align hx26; wp_done_reg hsp_align
  step2_oom := by intro _ s hpc hrun _hsp _hsp_align hx0; wp_steps; exact SepWP.done (by rfl) (by wp_reg) ⟨by wp_reg, Entails.refl _⟩
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne; wp_done_reg hsp_align
  step2_to_pb := by intro _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_reg hsp_align
  step3a_grow := by intro _ _ s hpc hrun hsp hsp_align; wp_done_reg hsp_align
  step3b := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28; wp_done_reg hsp_align
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_reg hsp_align
  step4b_pre_memmove := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28; wp_done_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne; wp_done_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_reg hsp_align
  step5 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align

set_option maxHeartbeats 1600000 in
theorem dhCommitBlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base (lsmpl.base 445) where
  step1 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28; wp_done_reg hsp_align
  step2_pre_shim := by intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24; wp_done_reg hsp_align
  step2_pre_alloc := by intro _ s hpc hrun hsp hsp_align hx26; wp_done_reg hsp_align
  step2_oom := by intro _ s hpc hrun _hsp _hsp_align hx0; wp_steps; exact SepWP.done (by rfl) (by wp_reg) ⟨by wp_reg, Entails.refl _⟩
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne; wp_done_reg hsp_align
  step2_to_pb := by intro _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_reg hsp_align
  step3a_grow := by intro _ _ s hpc hrun hsp hsp_align; wp_done_reg hsp_align
  step3b := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28; wp_done_reg hsp_align
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_reg hsp_align
  step4b_pre_memmove := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28; wp_done_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne; wp_done_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_reg hsp_align
  step5 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
