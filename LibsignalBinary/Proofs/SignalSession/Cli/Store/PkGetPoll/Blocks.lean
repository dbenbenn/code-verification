/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Epilogue and Branch Helpers for `get_pre_key::{closure#0}`

Stack-frame decomposition (32 cells), shared return epilogue (`+348 .. +404`), and branch lemmas
for `Dir::get` errors, `PreKeyRecord::deserialize` errors, missing files, and decoded records.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace CliPkGetPollNorm

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPState_pre (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPState_pre (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPState_pre (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_writeVReg128_zero (s : State) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 val

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm, wp_norm]
theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[arm64_norm, wp_norm]
theorem sp_restore_256 (sp0 : BitVec 64) :
    sp0 - 256#64 + 256#64 = sp0 := by
  bv_bits

@[arm64_norm, wp_norm]
theorem cond_eq_adds64 (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x y false).2 = (x + y == 0#64) := by
  have hw : BitVec.setWidth 64 (BitVec.setWidth 65 y + BitVec.setWidth 65 x) = x + y := by
    bv_bits
  show (AddWithCarry64 x y false).2.z = (x + y == 0#64)
  simp [AddWithCarry64, hw]

@[arm64_norm, wp_norm]
theorem cond_ne_adds64 (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x y false).2 = (x + y != 0#64) := by
  change (!(ConditionHolds .EQ (AddWithCarry64 x y false).2)) = (x + y != 0#64)
  rw [cond_eq_adds64]
  rfl

@[arm64_norm, wp_norm]
theorem cond_eq_addsPState64 (x y : BitVec 64) :
    ConditionHolds .EQ (addsPState64 x y) = (x + y == 0#64) := by
  have h : addsPState64 x y = (AddWithCarry64 x y false).2 := by
    with_unfolding_all rfl
  rw [h, cond_eq_adds64]

@[arm64_norm, wp_norm]
theorem cond_ne_addsPState64 (x y : BitVec 64) :
    ConditionHolds .NE (addsPState64 x y) = (x + y != 0#64) := by
  have h : addsPState64 x y = (AddWithCarry64 x y false).2 := by
    with_unfolding_all rfl
  rw [h, cond_ne_adds64]

end CliPkGetPollNorm

open CliPkGetPollNorm

theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (F := F) ?_ (by simpa only [sepConj_assoc] using hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem bytes_zero_elim {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ptr : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = ((ptr ↦ₛ bs) ∗ vecU8BufRest A 0#64 ptr bs) ∗ Rest)
    (h : SepWP prog ret s Rest Q) :
    SepWP prog ret s P Q := by
  rw [heq, bytes_sep_vecU8BufRest_zero]
  exact SepWP.pure_elim fun _ => h

/-! ## Stack frame layout (`sp - 256` .. `sp - 8`, 32 cells) -/

@[expose] def pkPollSlack (sp : BitVec 64) : SepProp :=
  cells (sp - 208#64) 1 ∗ cells (sp - 160#64) 1

@[expose] def pkSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)

@[expose] def pkBoxKeep (x : PkPollGhost) (s0 : State) : SepProp :=
  pkPollSlack s0.sp ∗ pkSavedRegs s0.sp s0 ∗
    (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
    memRegion x.out 56

theorem cells_32_split (sp : BitVec 64) :
    cells (sp - 256#64) 32 =
      pkPollSlack sp ∗
        cells (sp - 256#64) 6 ∗ cells (sp - 200#64) 3 ∗
        cells (sp - 176#64) 2 ∗ cells (sp - 152#64) 7 ∗
        cells (sp - 96#64) 12 := by
  rw [show (32 : Nat) = 6 + 26 from rfl, cells_split_sub sp 256 208 6 26,
    show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 3 + 22 from rfl, cells_split_sub sp 200 176 3 22,
    show (22 : Nat) = 2 + 20 from rfl, cells_split_sub sp 176 160 2 20,
    show (20 : Nat) = 1 + 19 from rfl, cells_split_sub sp 160 152 1 19,
    show (19 : Nat) = 7 + 12 from rfl, cells_split_sub sp 152 96 7 12]
  dsimp only [pkPollSlack]
  ac_rfl

theorem cells_sub_6_256_eq (sp : BitVec 64) :
    cells (sp - 256#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 256#64) ↦₆₄ v0) ∗ ((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 240#64) ↦₆₄ v2) ∗
        ((sp - 232#64) ↦₆₄ v3) ∗ ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) := by
  cells_unfold

theorem cells_sub_3_200_eq (sp : BitVec 64) :
    cells (sp - 200#64) 3 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) := by
  cells_unfold

theorem cells_sub_2_176_eq (sp : BitVec 64) :
    cells (sp - 176#64) 2 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 176#64) ↦₆₄ v0) ∗ ((sp - 168#64) ↦₆₄ v1) := by
  cells_unfold

theorem cells_sub_7_152_eq (sp : BitVec 64) :
    cells (sp - 152#64) 7 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64,
        ((sp - 152#64) ↦₆₄ v0) ∗ ((sp - 144#64) ↦₆₄ v1) ∗ ((sp - 136#64) ↦₆₄ v2) ∗
        ((sp - 128#64) ↦₆₄ v3) ∗ ((sp - 120#64) ↦₆₄ v4) ∗ ((sp - 112#64) ↦₆₄ v5) ∗
        ((sp - 104#64) ↦₆₄ v6) := by
  cells_unfold

theorem cells_sub_12_96_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) := by
  cells_unfold

private theorem pkFrame_pack (sp : BitVec 64) (s0 : State)
    (u0 u1 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64) :
    (pkPollSlack sp ∗ pkSavedRegs sp s0 ∗
      ((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗
      ((sp - 240#64) ↦₆₄ u2) ∗ ((sp - 232#64) ↦₆₄ u3) ∗
      ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5) ∗
      ((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2) ∗
      ((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1) ∗
      ((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗
      ((sp - 136#64) ↦₆₄ g2) ∗ ((sp - 128#64) ↦₆₄ g3) ∗
      ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗ ((sp - 104#64) ↦₆₄ g6)) ⊢
      cells (sp - 256#64) 32 := by
  rw [cells_32_split]
  have h6 : (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
      ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ⊢
      cells (sp - 256#64) 6 := by
    rw [cells_sub_6_256_eq]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
        (Entails.sepExists_right u5 (Entails.refl _))))))
  have h3 : (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ⊢
      cells (sp - 200#64) 3 := by
    rw [cells_sub_3_200_eq]
    exact Entails.sepExists_right n0 (Entails.sepExists_right n1
      (Entails.sepExists_right n2 (Entails.refl _)))
  have h2 : (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ⊢ cells (sp - 176#64) 2 := by
    rw [cells_sub_2_176_eq]
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))
  have h7 : (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
      ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
      ((sp - 104#64) ↦₆₄ g6)) ⊢ cells (sp - 152#64) 7 := by
    rw [cells_sub_7_152_eq]
    exact Entails.sepExists_right g0 (Entails.sepExists_right g1 (Entails.sepExists_right g2
      (Entails.sepExists_right g3 (Entails.sepExists_right g4 (Entails.sepExists_right g5
        (Entails.sepExists_right g6 (Entails.refl _)))))))
  have h12 : pkSavedRegs sp s0 ⊢ cells (sp - 96#64) 12 := by
    unfold pkSavedRegs
    rw [cells_sub_12_96_eq]
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
          (Entails.sepExists_right _ (Entails.sepExists_right _
            (Entails.sepExists_right _ (Entails.refl _))))))))))))
  refine Entails.trans (Q :=
    pkPollSlack sp ∗
      (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
        ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ∗
      (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ∗
      (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ∗
      (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
        ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
        ((sp - 104#64) ↦₆₄ g6)) ∗
      pkSavedRegs sp s0) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono h6
    (sepConj_mono h3 (sepConj_mono h2 (sepConj_mono h7 h12))))

/-! ## Shared epilogue helper (`+348` .. `+404` `ret`) -/

@[expose] def pkEpiloguePost (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) (x : PkPollGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (pkGetPollInnerSpec rd pathOk A calleeStk).post x s0 sf)

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
