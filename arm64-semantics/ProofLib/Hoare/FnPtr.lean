/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.CoreLemmas
public import ProofLib.PlacedHelpers
public import ProofLib.Hoare.Safety
public import ProofLib.SepLogic.WP.Structural
import Arm64.Trusted.Spec.SepLogic

/-!
# Indirect Call Rules (`BLR`) and Little-Endian Pointer Words

Provides `SepWP` composition rules for indirect subroutine calls (`BLR`) via `FnPtrSpec`
(`wp_blr_of_fnPtrSpec`) and little-endian 64-bit word decoding (`word64LE`).
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Read a 64-bit little-endian word from byte list `bs` starting at index `idx`. -/
def word64LE (bs : List (BitVec 8)) (idx : Nat) : BitVec 64 :=
  (bs.getD idx 0#8).zeroExtend 64 |||
  ((bs.getD (idx + 1) 0#8).zeroExtend 64 <<< 8) |||
  ((bs.getD (idx + 2) 0#8).zeroExtend 64 <<< 16) |||
  ((bs.getD (idx + 3) 0#8).zeroExtend 64 <<< 24) |||
  ((bs.getD (idx + 4) 0#8).zeroExtend 64 <<< 32) |||
  ((bs.getD (idx + 5) 0#8).zeroExtend 64 <<< 40) |||
  ((bs.getD (idx + 6) 0#8).zeroExtend 64 <<< 48) |||
  ((bs.getD (idx + 7) 0#8).zeroExtend 64 <<< 56)

private theorem calleeSavedPreserved_of_blr_step {s sf : State} {lrVal pcVal : BitVec 64}
    (hcs : CalleeSavedPreserved ((s.writeReg64 Reg.lr lrVal).setPC pcVal) sf) :
    CalleeSavedPreserved s sf := by
  simpa [CalleeSavedPreserved, State.setPC, State.writeReg64, State.readReg64] using hcs

/-- Compositional `SepWP` rule for an indirect subroutine call (`BLR rn`) discharged via
    `FnPtrSpec prog (s.readReg64 rn) spec`. Advances from `pc` to `pc + 4#64`,
    preserving the caller frame `F`, stack pointer `s.sp`, and `CalleeSavedPreserved s sf`. -/
theorem wp_blr_of_fnPtrSpec {α : Type} {prog : Program} {pc target_pc : BitVec 64}
    {rn : Reg} {spec : Spec α} {s : State}
    (hfn : FnPtrSpec prog (s.readReg64 rn) spec)
    {x : α} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hfetch : prog.fetch pc = some (.blr rn))
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) →
      (s.mem ⊨ spec.pre x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked →
      ¬(sf.mem ⊨ spec.onPanic x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = pc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (spec.post x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ F) post oom)
    (h_oom : ∀ R sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ (F ∗ R)) →
      (sf.mem ⊨ oom sf ∗ R) := by
      intro _ _ _ ho
      try simp only [wp_unfold, Spec.noPanic, Spec.allowPanicWhen, Spec.allowPanic, Spec.panicsOr, Spec.allowOom] at ho ⊢
      first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc s P post oom := by
  have hs_pc : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hexec : prog.evalInst (.blr rn) (s.setPC pc) =
      (s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn) := by
    rw [hs_pc]; simp only [Program.evalInst, execInstWithSvc, hpc]
  refine SepWP.step_pure (s' := (s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn))
    hpc hrun hfetch hexec rfl ?_
  refine SepWP.call_subroutine_frame (entry := s.readReg64 rn) (ret_pc := pc + 4#64)
    hfn rfl hrun hsp_align (by simp [State.setPC, State.writeReg64, State.readReg64])
    hpre h_no_panic h_no_exit ?_ h_oom
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  exact hnext sf hpc_sf hrun_sf hsp_sf (calleeSavedPreserved_of_blr_step hcs_sf)

end ProofLib
