/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

theorem sepWP_drop_left_receiverChains {prog : Program} {target_pc : BitVec 64} {s : State}
    {A P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) :
    SepWP prog target_pc s (A ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm)

theorem chunks104_6QWAt_stack_eq_receiverChains (sp0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp0 - 232#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((sp0 - 224#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 216#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((sp0 - 208#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((sp0 - 200#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((sp0 - 192#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((sp0 - 184#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((sp0 - 176#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((sp0 - 168#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((sp0 - 160#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((sp0 - 152#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((sp0 - 144#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((sp0 - 136#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, sepConj_assoc]
  rfl

theorem chunks104_6QWAt_dst_eq_receiverChains (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 =
      (a ↦₆₄ q0.truncate 64) ∗ ((a + 8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((a + 16#64) ↦₆₄ q1.truncate 64) ∗ ((a + 24#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((a + 32#64) ↦₆₄ q2.truncate 64) ∗ ((a + 40#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((a + 48#64) ↦₆₄ q3.truncate 64) ∗ ((a + 56#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((a + 64#64) ↦₆₄ q4.truncate 64) ∗ ((a + 72#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((a + 80#64) ↦₆₄ q5.truncate 64) ∗ ((a + 88#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((a + 96#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  have h0 (q : BitVec 128) : q.extractLsb' 0 64 = q.truncate 64 := by bv_bits
  simp only [h0, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem prostSSAt_fold_apply_recv_receiverChains (ss cap ptr : BitVec 64) (v : SSV) (c : ChainV)
    (hrecv : v.recv = [])
    (hcap1 : 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64) ∗
      prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104) ∗
      prostSSRest_receiverChains A0 ss v) ⊢
    prostSSAt A0 ss (v.apply (.recv c)) := by
  rw [prostSSAt_eq_recv_sep_rest_receiverChains A0 ss (v.apply (.recv c)),
      prostSSRest_apply_recv_receiverChains A0 ss v c]
  have h1 : (v.apply (.recv c)).recv = [c] := by
    simp [SSV.apply, hrecv]
  rw [h1]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64) ∗
        prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104) ∗
        prostSSRest_receiverChains A0 ss v) =
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64) ∗
        prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104)) ∗
      prostSSRest_receiverChains A0 ss v := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_left (vecAt_recv_singleton_fold_receiverChains ss cap ptr c hcap1 hcap_lt hptr)

theorem stackAt_receiverChains_epilogue_fold_receiverChains (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    (stackAt (sp0 - 240#64) mfSubStack_receiverChains ∗
      mfFramePad_receiverChains sp0 ∗
      RawByteMove.chunks104_6QWAt (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6 ∗
      mfSavedRegs_receiverChains sp0 s0 w56) ⊢
    stackAt sp0 mergeFieldStack := by
  rw [← stackAt_mergeFieldStack_join_receiverChains sp0]
  have h1 := chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6
  have h2 : mfSavedRegs_receiverChains sp0 s0 w56 ⊢ memRegion (sp0 - 80#64) 80 :=
    cells10_entails_memRegion80_receiverChains sp0
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) w56
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono h1 h2))

theorem beq_zero_of_ne_receiverChains {cap : BitVec 64} (h : cap ≠ 0#64) : (0#64 == cap) = false := by
  cases hb : (0#64 == cap)
  · rfl
  · exact False.elim (h (eq_of_beq hb).symm)

theorem allocFailedIn_trans_receiverChains {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

attribute [local irreducible] prostSSRest_receiverChains prostChainAt prostSSAt mfFramePad_receiverChains
  Prost.sliceCursorAfter

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem sepWP_intro_rodata_tag7_placed_receiverChains [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 6#64) ↦₈ᵣ 0x8d#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_mfJumpTable_tag7_placed_intro_receiverChains hcrl.2 hm)

theorem call_frame_lscro_receiverChains {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intros _ _ _ h
      first
        | exact not_satisfies_false_sepConj h
        | (dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at h; exact not_satisfies_false_sepConj h)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hmid : SepWPp prog ret_pc s P
      (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
      Qp (fun _ => ⌜False⌝) :=
    ProofLib.SepWPp.call_frame hcall hpc hrun hsp hlr hspec hφ hP hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' hst hm' => (hoom sm (F ∗ R') hst hm').elim)
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | ⟨hpan, P_m, hpost, hqp⟩ | ⟨_, hm_oom⟩⟩ :=
    hmid R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m, hpost, hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hm_oom).elim

theorem step_receiverChains_from_0x45c_to_ret_placed_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (P : SeedField → Prop) (x : MergeFieldGhost) (c : ChainV)
    (s0 s : State) (Fr : SepProp) (w56 cap' ptr' : BitVec 64)
    (hrecv : x.v.recv = [])
    (hfld : x.fld = .recv c)
    (hcap1 : 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (blkPl_15).base + 1116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = x.ss)
    (hx19 : s.readReg64 .x19 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28) :
    SepWP (lsProg_15 H) (s0.readReg64 Reg.lr) s
      (((x.ss + 0x48#64) ↦₆₄ cap') ∗ ((x.ss + 0x50#64) ↦₆₄ ptr') ∗ ((x.ss + 0x58#64) ↦₆₄ 0#64) ∗
        memRegion ptr' 104 ∗ memRegion (ptr' + 104#64) ((cap'.toNat - 1) * 104) ∗
        prostSSRest_receiverChains A0 x.ss x.v ∗
        prostChainAt A0 (s0.sp - 232#64) c ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗ mfFramePad_receiverChains s0.sp ∗
        stackAt (s0.sp - 240#64) mfSubStack_receiverChains ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldSeedPlacedSpec P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  apply SepWP.fold (prostChainAt_move_chunks104_receiverChains A0 (s0.sp - 232#64) c) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0
  apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2
  apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4
  apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro Hmov
  apply SepWP.pure_elim; intro hmov
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains ptr')) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0
  apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4
  apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains ptr' d0 d1 d2 d3 d4 d5 dw6, mfSavedRegs_receiverChains]
  wp_steps
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains ptr' q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    ← mfSavedRegs_receiverChains]
  apply SepWP.fold (hmov ptr') (by sep_frame)
  apply SepWP.fold (prostSSAt_fold_apply_recv_receiverChains x.ss cap' ptr' x.v c hrecv hcap1 hcap_lt hptr) (by sep_frame)
  apply SepWP.fold (stackAt_receiverChains_epilogue_fold_receiverChains s0.sp s0 w56 q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  simp only [mergeFieldSeedRawSpec, hfld]
  wp_done

theorem step_receiverChains_from_0x2bc_to_ret_placed_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hG : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A0)))
    (P : SeedField → Prop) (x : MergeFieldGhost) (c : ChainV)
    (s0 s : State) (Fr : SepProp) (w56 : BitVec 64)
    (hrecv : x.v.recv = [])
    (hfld : x.fld = .recv c)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_15).base + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = x.ss)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28) :
    SepWPp (lsProg_15 H) (s0.readReg64 Reg.lr) s
      (prostChainAt A0 (s0.sp - 232#64) c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        stackAt (s0.sp - 240#64) chainMergeStack ∗
        memRegion ((s0.sp - 240#64) - 16144#64) 3856 ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp ∗
        prostSSAt A0 x.ss x.v)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldSeedPlacedSpec P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldSeedPlacedSpec P).onPanic x s0 sf ∗ Fr)) := by
  have hG' := growOneChain_placed_ok_sub_receiverChains hG
  have h45c := @step_receiverChains_from_0x45c_to_ret_placed_receiverChains _ H P x c s0
  apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains (s0.sp - 240#64)).symm) (by sep_frame)
  rw [prostSSAt_eq_recv_sep_rest_receiverChains A0 x.ss x.v, hrecv]
  apply SepWPp.fold (vecAt_recv_nil_open_receiverChains x.ss) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_lt, hptr⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    simp only [↓reduceIte, emp_sepConj]
    rw [stackAt_sub_to_growOne_receiverChains (s0.sp - 240#64)]
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 43) hcrl
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
    intro hcrl1
    refine SepWPp.call_frame (x := (x.ss + 0x48#64, 0#64, ptr, []))
      (ret_pc := (blkPl_15).base + 2480#64) hG'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
      (by simp only [arm64_norm])
      (growOne_placed_cap0_pre_eq_receiverChains x.ss ptr (s0.sp - 240#64) _ (by simp only [arm64_norm, hsp]))
      ⟨hcrl1, rfl, by simp only [arm64_norm], hptr, by decide⟩
      (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm, htr])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hx20, hx26, hx27, hx28, hsp, hvregs] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
    have hsp_align_m : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rw [hspm, ← hsp]
      exact hsp_align
    refine SepWPp.fold (growOne_placed_cap0_post_elim_sp_receiverChains x.ss ptr (s0.sp - 240#64) _ sm ?_) rfl ?_
    · simp only [arm64_norm, hsp]
    simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm, htr] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_left; rintro ⟨hcap1', hcap_lt', hp'⟩
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_receiverChains (s0.sp - 240#64)).symm) (by sep_frame)
    apply SepWPp.of_sepWP (mid := (blkPl_15).base + 1116#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 4#64 p' hrecv hfld hcap1' hcap_lt' hp' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · simp only [arm64_norm, hspm]
    · simp only [State.spAligned, arm64_norm] at hsp_align_m ⊢; exact hsp_align_m
    · simp only [arm64_norm, htr_m']
    · simp only [arm64_norm, hvregsm]
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx19m]
    · simp only [arm64_norm, hx26m]
    · simp only [arm64_norm, hx27m]
    · simp only [arm64_norm, hx28m]
  · have hcap1 : 1 ≤ cap.toNat := by
      have : cap.toNat ≠ 0 := fun h => hcap0 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hbeq0 : (0#64 == cap) = false := beq_zero_of_ne_receiverChains hcap0
    rw [memRegion_cap_nonzero_split_receiverChains cap ptr hcap0 hcap_lt]
    apply SepWPp.of_sepWP (mid := (blkPl_15).base + 1116#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 cap ptr hrecv hfld hcap1 hcap_lt hptr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · simp only [arm64_norm, hsp]
    · simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align
    · simp only [arm64_norm, htr]
    · simp only [arm64_norm, hvregs]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx26]
    · simp only [arm64_norm, hx27]
    · simp only [arm64_norm, hx28]

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
