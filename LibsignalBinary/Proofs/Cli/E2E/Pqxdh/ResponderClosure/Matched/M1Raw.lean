/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Constant-Time Loop and Raw Subroutine Proof for `promote_matching_session`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cond_ne_subs64_one {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  omega

structure PromoteRawGhost where
  recPtr : BitVec 64
  locCap : BitVec 64
  alicePtr : BitVec 64
  sessVer : BitVec 32
  msgVer : BitVec 8
  serPtr : BitVec 64
  serBytes : List (BitVec 8)
  outPtr : BitVec 64

@[expose] def promoteMatchingSessionRawSpec : Spec PromoteRawGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.locCap.toNat < 2 ^ 63 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    (∃∗ w4a0 : BitVec 64, (st.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (st.sp - 1136#64) ↦₆₄ w470) ∗
    cells (st.sp - 96#64) 12
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
    cells (s0.sp - 96#64) 12

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_self (a : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 a) = false :=
  bne_self_eq_false _

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0 (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0 (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 1#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

private theorem ofNat64_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

private theorem promote_ct_eq_loop_prog_wp
    (prog : Program) (loopPc exitPc outPtr : BitVec 64)
    (hlast : ∀ (b0 : BitVec 8) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog exitPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun sf Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs))
    (hstep : ∀ (b0 : BitVec 8) (m : Nat), 0 < m → m + 1 < 2 ^ 64 →
      ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog loopPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun s1 Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧ s1.readReg64 .x25 = 1#64 ∧ s1.vregs = s.vregs))
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loopPc) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP prog exitPc s ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0])) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact hlast b0 serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (hstep b0 (b1 :: rest').length hm_pos hm_lt serPtr alicePtr s
          hpc hrun hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      refine SepWP.bind_seq_readOnly
        (ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
          hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1)
        (by sep_focus)
        fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      ac_rfl

@[expose] def promoteMatchingSessionRawSpecExt32 : Spec PromoteRawGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.locCap.toNat < 2 ^ 63 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    (∃∗ w4a0 : BitVec 64, (st.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (st.sp - 1136#64) ↦₆₄ w470) ∗
    cells (st.sp - 96#64) 12 ∗
    stackAt (st.sp - 1184#64) extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((x.recPtr + 0x18#64) ↦₆₄ x.locCap) ∗
    ((x.recPtr + 0x80#64) ↦₆₄ x.alicePtr) ∗
    ((x.recPtr + 0x88#64) ↦₆₄ 33#64) ∗
    ((x.recPtr + 0x160#64) ↦₃₂ x.sessVer) ∗
    (x.alicePtr ↦ₛ x.serBytes) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
    (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
    cells (s0.sp - 96#64) 12 ∗
    stackAt (s0.sp - 1184#64) extHookStack

private theorem sp_sub_1184_aligned_m1 {sp : BitVec 64}
    (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 1184#64) &&& 15#64 == 0#64) = true := by
  have heq : ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
  rw [heq]; exact h

private theorem sp_sub_96_align_m1 (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

private theorem sp_add_1088_align_m1 (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

private theorem extractLsb32_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    v.extractLsb' 0 32 = 1#32 := by
  bv_slice

private theorem and64_mask8_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    (v &&& 255#64) = 1#64 := by
  bv_slice

private theorem step_blackBox_ext32_m1 {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      (sf.readReg64 .x0).setWidth 32 = 1#32 →
      sf.trace = s.trace →
      SepWP prog target_pc sf (stackAt sf.sp extHookStack ∗ F) post) :
    SepWP prog target_pc s (stackAt s.sp extHookStack ∗ F) post := by
  refine SepWP.call_subroutine_frame_auto (x := 1#64) (F := F) hbb hpc hrun hsp_align hlr
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcf hrunf hspf hcsf => ?_)
    (fun R hm => ?_)
  · dsimp only [CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    rw [sepConj_assoc, ← hspf]
    refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
    exact hnext sf hpcf hrunf hspf hcsf hpure.1 hpure.2
  · dsimp only [CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩

private theorem cells_96_12_eq_m1 (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗
      ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
      ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗
      ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
      ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗
      ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
      ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗
      ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
      ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗
      ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
      ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗
      ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

private theorem promote_ct_eq_loop_prog_ext32_wp
    (prog : Program) (loopPc exitPc outPtr : BitVec 64)
    (hlast : ∀ (b0 : BitVec 8) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog exitPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
        (fun sf Pf =>
          Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          (sf.readReg64 .x0).setWidth 32 = 1#32 ∧ sf.readReg64 .x23 = outPtr ∧
          calleeSavedVRegs sf = calleeSavedVRegs s))
    (hstep : ∀ (b0 : BitVec 8) (m : Nat), 0 < m → m + 1 < 2 ^ 64 →
      ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog loopPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)))
        (fun s1 Pf =>
          Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧ s1.readReg64 .x25 = 1#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s))
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loopPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP prog exitPc s (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)))
      (fun sf Pf =>
        Pf = (stackAt s.sp extHookStack ∗ ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = 1#32 ∧ sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0])) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact hlast b0 serPtr alicePtr s hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (hstep b0 (b1 :: rest').length hm_pos hm_lt serPtr alicePtr s
          hpc hrun hsp_al hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_al
      have hstk1 : stackAt s.sp extHookStack = stackAt s1.sp extHookStack := by rw [hsp1]
      conv => arg 4; rw [hstk1]
      refine SepWP.bind_seq_readOnly
        (ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
          hpc1 hrun1 hsp1_al hx19_1 hx21_1 hx22_1 hx23_1 hx25_1)
        (by sep_focus)
        fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [← hstk1, pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      ac_rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
