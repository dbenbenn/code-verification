/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Relocatable Stage P2 Basic Blocks — Substage P2.3d2 Allocation and P2.4

Relocatable `[LibsignalPlacement]` basic-block lemmas for Substage P2.3d2 allocation (`+0x0d04 →
+0x0d08`) and Substage P2.4 (`+0x0d5c → +0x36a8`) on Block `518`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Substage P2.3d2 `bl __rust_alloc(21, 1)` + OOM Panic (`+0xd04 -> +0xd08`) -/

theorem p2_seg3d2_bl_alloc_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running) :
    SepWP (stageP1ProgPlaced ext) (lsρ lsRustAllocSym) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xd08#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsρ, lsRustAllocSym] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p2_seg3d2_oom_branch_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = stageP1EntryPlaced + 0xd08#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (stageP1ProgPlaced ext) (lsρ lsHandleErrorSym) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.trace = s.trace) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsρ, lsHandleErrorSym] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩


/-! ## 2. Substage P2.4 Basic Blocks (`+0xd5c -> getIdKpShimAddr` at `+0x36a8`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg4_none_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
    ctSlicePtr v_b0 u_488 : BitVec 64)
    (opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (stageP1ProgPlaced ext) getIdKpShimAddr s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x36ac#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsLogFilterAddr, lsρ]
    at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = ctSlicePtr := hx21
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p2_seg4b_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkPollAddr v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xdec#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = opkFutPtr)
    (hx1 : s.readReg64 .x1 = opkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) opkPollAddr s
      (((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x9c4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = opkFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = opkFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p2_seg4c_gen_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkDropAddr
    opkPubCap opkPubPtr opkSecCap opkSecPtr opkIdWord u_ac8
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (hpub_ne_neg2 : opkPubCap ≠ 0xfffffffffffffffe#64)
    (hpub_ne_neg3 : opkPubCap ≠ 0xfffffffffffffffd#64)
    (hdrop_nz : opkDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x9c4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) opkDropAddr s
      (preKeyRecordOut64At (s.sp + 0xa90#64) opkPubCap opkPubPtr 33#64 opkSecCap
         opkSecPtr 32#64 opkIdWord u_ac8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
       ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗ ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0xa90#64) opkPubCap opkPubPtr 33#64 opkSecCap
            opkSecPtr 32#64 opkIdWord u_ac8 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = opkPubCap ∧ s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧ s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xe40#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ne2 : ConditionHolds CondCode.NE (addsPState64 opkPubCap 2#64) = true :=
    p2_cond_ne_adds64_of_ne_neg2 hpub_ne_neg2
  have hcond_eq2 : ConditionHolds CondCode.EQ (addsPState64 opkPubCap 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact beq_eq_false_iff_ne.mpr (by bv_omega)
  have hcond_ne3 : ConditionHolds CondCode.NE (addsPState64 opkPubCap 3#64) = true :=
    p2_cond_ne_adds64_of_ne_neg3 hpub_ne_neg3
  have hcond_eq3 : ConditionHolds CondCode.EQ (addsPState64 opkPubCap 3#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact beq_eq_false_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (opkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, preKeyRecordOut64At] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p2_seg4a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
    ctSlicePtr u_488 : BitVec 64)
    (opkId : BitVec 32)
    (hpc : s.pc = stageP1EntryPlaced + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (stageP1ProgPlaced ext) opkLoadShimAddr s
      (((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xdec#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsLogFilterAddr, lsρ]
    at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = ctSlicePtr := hx21
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg4d_hooks_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (s : State) (coroPtr opkFutPtr opkFutVt opkPubCap opkPubPtr opkSecCap opkSecPtr opkIdWord
    r0 r1 r2 r3 r4 r5 r6 : BitVec 64)
    (opkBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg1 : opkPubCap ≠ 0xffffffffffffffff#64)
    (hbs_nz : BitVec.ofNat 64 opkBoxSize ≠ 0#64)
    (hbs_lt : opkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = opkPubCap)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = opkPubPtr)
    (hx27 : s.readReg64 .x27 = opkIdWord) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair") s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 opkBoxSize) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr opkBoxSize 8 ∗
       memRegion opkFutPtr opkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xb8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ r0) ∗
       ((s.sp + 0x938#64) ↦₆₄ r1) ∗
       ((s.sp + 0x940#64) ↦₆₄ r2) ∗
       ((s.sp + 0x948#64) ↦₆₄ r3) ∗
       ((s.sp + 0x950#64) ↦₆₄ r4) ∗
       ((s.sp + 0x958#64) ↦₆₄ r5) ∗
       ((s.sp + 0x960#64) ↦₆₄ r6))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 opkBoxSize) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0x938#64) ↦₆₄ opkPubPtr) ∗
          ((s.sp + 0x940#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x948#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0x950#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x958#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x960#64) ↦₆₄ opkIdWord)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = opkPubCap ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xe90#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hcond_eq1 : ConditionHolds CondCode.EQ (addsPState64 opkPubCap 1#64) = false :=
    p2_cond_eq_adds64_of_ne_neg1 hpub_ne_neg1
  have hcond_ne1 : ConditionHolds CondCode.NE (addsPState64 opkPubCap 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact bne_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 opkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 opkBoxSize).toNat = opkBoxSize := Nat.mod_eq_of_lt hbs_lt
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = opkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = opkPubCap := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 33#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = opkPubPtr := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = opkIdWord := hx27
  wp_steps
  wp_call hdealloc (opkFutPtr, opkBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev p2_seg4d_gen_placed_wp := @p2_seg4d_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg4e_hooks_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (s : State) (coroPtr msgPtr ctxPtr opkPubCap opkPubPtr opkSecCap opkSecPtr
    idStorePtr idStoreVt getIdKpShimAddr
    v_98 v_a0 v_b0 u_270 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_4b0 b_278 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xe90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : opkPubCap ≠ 0#64)
    (hsec_nz : opkSecCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = opkPubCap)
    (hx26 : s.readReg64 .x26 = opkPubPtr) :
    SepWP (stageP1ProgPlaced ext) getIdKpShimAddr s
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3b0#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt
         (coroPtr + 0x4b1#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗ ((s.sp + 0x278#64) ↦₈ b_278) ∗
       A.live opkPubPtr opkPubCap.toNat 1 ∗ memRegion opkPubPtr opkPubCap.toNat ∗
       A.live opkSecPtr opkSecCap.toNat 1 ∗ memRegion opkSecPtr opkSecCap.toNat ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗ ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
          keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ w6) ∗ ((s.sp + 0x278#64) ↦₈ b63) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗ ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x36ac#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hpub_beq : (opkPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hsec_beq : (opkSecCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsec_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym,
    keyPair64UnalignedAt, bytes7At] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = opkPubCap := hx22
  have hx26' : s.readReg64 (Reg.gpr 26#5) = opkPubPtr := hx26
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (opkPubPtr, opkPubCap.toNat, 1)
  wp_steps
  wp_call hdealloc (opkSecPtr, opkSecCap.toNat, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

abbrev p2_seg4e_gen_placed_wp := @p2_seg4e_hooks_placed_wp

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
