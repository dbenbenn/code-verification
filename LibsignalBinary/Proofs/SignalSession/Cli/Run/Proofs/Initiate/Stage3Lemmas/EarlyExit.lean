/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Shared Non-Contributory Zero-DH Unwind Exit

Verifies the shared zero-DH unwind tail (`+0x1544` / `+0x1548 → +0x0350 → ret`) freeing
`secretsPtr` (`192` B) and `pqspkPtr` (`1568` B), writing `SpeOwned.plain 10` at `x.ret`,
restoring callee-saved registers, and reassembling `InitExitPost`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

theorem s3_done_in {prog : Program} {target : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = target := by wp_norm_goal)
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm]) :
    SepWP prog target sm P (fun s' P'' =>
      s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htr, hent, hsp, hfp, hx19, hvregs, hphi⟩

theorem s3_done_call {prog : Program} {callee lr_out : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = callee := by wp_norm_goal)
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm])
    (hlr : sm.readReg64 .lr = lr_out := by wp_norm_goal) :
    SepWP prog callee sm P (fun s' P'' =>
      s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ s'.readReg64 .lr = lr_out ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htr, hent, hsp, hfp, hx19, hvregs, hlr, hphi⟩

private theorem unwind_locals_collapse {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (pqspkPtr : BitVec 64) (u0 u1 u2 u3 : BitVec 64) (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    initSaved s0 ∗
      memRegion fsp 0x128 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x2e0 ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      memRegion (fsp + 0x438#64) 0x181 ∗
      ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 0x37e ∗
      ((fsp + 0x938#64) ↦₆₄ u0) ∗ ((fsp + 0x940#64) ↦₆₄ u1) ∗
      ((fsp + 0x948#64) ↦₆₄ u2) ∗ ((fsp + 0x950#64) ↦₆₄ u3) ∗
      memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  dsimp only
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine Entails.trans
    (sepConj_mono (initSaved_entails_memRegion96 s0)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (initFreshRecAt_collapse fsp)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (Entails.refl _)))))))))))))) ?_
  have hloc :
      memRegion fsp 0x128 ∗ memRegion (fsp + 0x128#64) 0x20 ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗ memRegion (fsp + 0x428#64) 8 ∗
        memRegion (fsp + 0x430#64) 8 ∗ memRegion (fsp + 0x438#64) 0x181 ∗
        memRegion (fsp + 0x5b9#64) 1 ∗ memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
        memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 ∗
        memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) =
      memRegion fsp initLocalsSize := by
    simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
    rw [memRegion_merge_at (fsp + 0x950#64) 8 4920 (fsp + 0x958#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x948#64) 8 4928 (fsp + 0x950#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x940#64) 8 4936 (fsp + 0x948#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x938#64) 8 4944 (fsp + 0x940#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5ba#64) 0x37e 4952 (fsp + 0x938#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5b9#64) 1 5846 (fsp + 0x5ba#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x438#64) 0x181 5847 (fsp + 0x5b9#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x430#64) 8 6232 (fsp + 0x438#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x428#64) 8 6240 (fsp + 0x430#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x148#64) 0x2e0 6248 (fsp + 0x428#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x128#64) 0x20 6984 (fsp + 0x148#64) (by bv_omega) (by decide),
      memRegion_merge_at fsp 0x128 7016 (fsp + 0x128#64) (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq ?_) (stack_frame_reassemble hstk hstk64 s0)
  dsimp only [fsp] at hloc ⊢
  rw [← hloc]
  ac_rfl

theorem sep_replace {P R A B F : SepProp}
    (h : A ⊢ B) (h1 : P ⊢ A ∗ F) (h2 : B ∗ F ⊢ R) : P ⊢ R :=
  Entails.trans h1 (Entails.trans (sepConj_mono h (Entails.refl F)) h2)

namespace Ext

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
