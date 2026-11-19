/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
public import ProofLib.StdStartup.StdDetect
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing

/-!
# Shared Step Lemmas, `0xf80` Stack Frame & Return Epilogue (`CbcDec.Common`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (adrpOff decodeWords hasInstrs pageLo12)
open VerifiedLibraries.RustStd (allocCallPreserved_trans fetch_instr_at fetch_instr_at0)
open CryptoGames.CBC (bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved VmPreserved
   OomPreserved FitsEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoDataSep)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 FsKeys256 aes256DecryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved adrpAddPair fsKeys256At blocks4Bytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec (aes256DecryptSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords (cbcRetEpilogueWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents aesDecBudgetCondSpec aesDecBudgetCondSpecErrRo)

/-! ## 1. Calls & `adrpAddPair` -/

theorem pureStepPreserved_bl {s sf : State} {retPc calleeAddr : BitVec 64}
    (h : PureStepPreserved ((s.writeReg64 .lr retPc).setPC calleeAddr) sf) :
    PureStepPreserved s sf :=
  (PureStepPreserved.of_proj_perm (by simp [arm64_norm]) (by simp [arm64_norm])).trans h

theorem pool_setMem_perm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {m : Memory} (hm : m.perm = s.mem.perm) :
    A.pool lim st (s.setMem m) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl,
    fun a => by cases s; exact congrFun hm a,
    by cases s; exact LibsignalBinary.Heap.FdsHiFrame.refl _⟩

theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

theorem sepWPp_exists_left {α : Type} {P : Program} {ret : BitVec 64} {s : State}
    {Q : α → SepProp} {Rest : SepProp}
    {post panic : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp P ret s (Q a ∗ Rest) post panic oom) :
    SepWPp P ret s ((∃∗ a : α, Q a) ∗ Rest) post panic oom := by
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem step_bl_call {α : Type} {P : Program}
    {blPc calleeAddr target_pc : BitVec 64} {spec : Spec α}
    (hbl : hasInstrs P blPc [ .bl (calleeAddr - blPc) ]) (hcall : subroutine_ok P calleeAddr spec) (x : α)
    {s : State} {Full A A' F : SepProp} {φ : Prop} {ψ : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hpre_eq : spec.pre x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) = (⌜φ⌝ ∗ A))
    (hpost_eq : ∀ sf, spec.post x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf = (⌜ψ sf⌝ ∗ A'))
    (hFull : Full = A ∗ F) (hφ : φ)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ψ sf → SepWP P target_pc sf (A' ∗ F) post oom)
    (hno : ∀ se, spec.onPanic x se = (fun _ => ⌜False⌝) := by intro _; exact rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by exact rfl)
    (h_no_oom : ∀ se sf, spec.onOom x se sf = ⌜False⌝ := by intro _ _; exact rfl) :
    SepWP P target_pc s Full post oom := by
  have hf : P.fetch s.pc = some (.bl (calleeAddr - blPc)) := by
    rw [hpc]; simpa [hasInstrs] using hbl 0 (Nat.zero_lt_succ 0)
  apply SepWP.of_reaches_pc; intro R hm; apply reaches_pc_step hrun hf
  let s' : State := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  have hadd : blPc + (calleeAddr - blPc) = calleeAddr := by bv_lin
  have heval : P.evalInst (.bl (calleeAddr - blPc)) s = s' := by
    simp [Program.evalInst, execInstWithSvc, State.setPC, State.writeReg64, hpc, hadd, s']
  rw [heval]
  have hm' : s'.mem ⊨ Full ∗ R := by
    have : s'.mem = s.mem := by cases s; rfl
    rw [this]; exact hm
  refine SepWP.to_reaches_pc ?_ hm'
  refine SepWP.call_framed_mut hcall x hpre_eq hpost_eq hFull hφ
    (by cases s; rfl) (by cases s; exact hrun) (by cases s; exact hsp_al) (by cases s; rfl)
    ?_ (hno s') h_no_exit ?_
  · intro sf hpc' hrun' hsp' hcs' hψ
    have hsp_s : sf.sp = s.sp := hsp'.trans (by cases s; rfl)
    have hcs_s : CalleeSavedPreserved s sf :=
      (show CalleeSavedPreserved s' sf ↔ CalleeSavedPreserved s sf by cases s; rfl).mp hcs'
    exact hnext sf hpc' hrun' hsp_s hcs_s hψ
  · intro R' sf _ hsat; rw [h_no_oom s' sf] at hsat; exact False.elim (not_satisfies_false_sepConj hsat)

theorem step_bl_memcpy {P : Program} {blPc calleeAddr target_pc sp dst src : BitVec 64}
    {bs : List (BitVec 8)}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr allocMemcpyVmSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hlen : bs.length < 2 ^ 64)
    (hFull : Full = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) post oom) :
    SepWP P target_pc s Full post oom :=
  let s' := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  step_bl_call hbl hcall (dst, src, bs)
    (φ := s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64)
    (ψ := fun sf => sf.readReg64 .x0 = dst ∧ AllocCallPreserved s' sf ∧ VmPreserved s' sf)
    hpc hrun hsp_al rfl (fun _ => rfl) hFull
    ⟨by simp [s', arm64_norm, hx0], by simp [s', arm64_norm, hx1],
     by simp [s', arm64_norm, hx2], hlen⟩
    fun sf hpc' hrun' hsp' hcs ⟨_, ha, hv⟩ =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl ⟨ha, hv⟩)

theorem step_bl_decrypt {P : Program}
    {blPc calleeAddr target_pc sp outPtr keysPtr inPtr : BitVec 64}
    {ks : FsKeys256} {bs : Blocks4}
    (hbl : hasInstrs P blPc [ .bl (calleeAddr - blPc) ])
    (hcall : subroutine_ok P calleeAddr aes256DecryptSpec)
    {s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = keysPtr) (hx1 : s.readReg64 .x1 = inPtr) (hx8 : s.readReg64 .x8 = outPtr)
    (hwf : Blocks4.Wf bs)
    (hFull : Full = (fsKeys256At keysPtr ks ∗ (inPtr ↦ₛ blocks4Bytes bs) ∗
                     memRegion outPtr 64 ∗ stackFrameAt sp 208) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((fsKeys256At keysPtr ks ∗ (inPtr ↦ₛ blocks4Bytes bs) ∗
          (outPtr ↦ₛ blocks4Bytes (aes256DecryptFs ks bs)) ∗ stackFrameAt sp 208) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom := by
  have hsp_cal : ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).sp = sp := by
    simp [arm64_norm, hsp]
  exact step_bl_call hbl hcall (false, outPtr, keysPtr, inPtr, ks, bs)
    (φ := ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x0 = keysPtr ∧
          ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x1 = inPtr ∧
          ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x8 = outPtr ∧
          Blocks4.Wf bs)
    (ψ := fun sf => PureStepPreserved ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf)
    hpc hrun hsp_al
    (by dsimp only [aes256DecryptSpec, bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte, hsp_cal])
    (fun sf => by dsimp only [aes256DecryptSpec, bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte, hsp_cal])
    hFull
    ⟨by simp [arm64_norm, hx0], by simp [arm64_norm, hx1], by simp [arm64_norm, hx8], hwf⟩
    fun sf hpc' hrun' hsp' hcs hpure =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl hpure)

theorem adrp_add_lo12_eq (pc target : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc target +
      (target.truncate 12).zeroExtend 64 = target := by
  unfold adrpOff
  bv_bits

theorem adrp_pageLo12_eq (pc target : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc target +
      (pageLo12 target).signExtend 64 = target := by
  unfold adrpOff pageLo12
  bv_bits

theorem step_adrpAddPair {prog : Program} {target_pc adrpPc target : BitVec 64}
    {r : BitVec 5} {relax : Bool} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpair : hasInstrs prog adrpPc (adrpAddPair (.gpr r) adrpPc target relax))
    (hr : r ≠ 31#5) (hpc : s.pc = adrpPc) (hrun : s.status = .Running)
    (hnext : SepWP prog target_pc ((s.writeReg64 (.gpr r) target).setPC (adrpPc + 8#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  have hadd := adrp_add_lo12_eq adrpPc target
  have hrel : adrpPc + 4#64 + (target - (adrpPc + 4#64)) = target := by bv_lin
  have hpc8 : adrpPc + 4#64 + 4#64 = adrpPc + 8#64 := by bv_lin
  cases relax
  · change hasInstrs prog adrpPc
      [ .adr true (.gpr r) (adrpOff adrpPc target),
        .addSubImm .W64 .ADD (.gpr r) (.gpr r) (target.truncate 12) false ] at hpair
    have hf0 := fetch_instr_at0 hpair; have hf1 := fetch_instr_at 1 hpair
    wp_step; wp_step
    convert hnext using 2
    simp [wp_norm, arm64_norm, hr]
  · change hasInstrs prog adrpPc [ .nop, .adr false (.gpr r) (target - (adrpPc + 4#64)) ] at hpair
    have hf0 := fetch_instr_at0 hpair; have hf1 := fetch_instr_at 1 hpair
    wp_step; wp_step
    convert hnext using 2

/-! ## 2. `3968`-Byte (`0xf80`) Stack Frame Layout & Shared Return Epilogue -/

theorem extHookStack_split_3968 (sp0 : BitVec 64) :
    stackAt sp0 extHookStack =
      stackFrameAt sp0 3968 ∗
        (stackAt (sp0 - 3968#64) allocHookStack ∗
          stackFrameAt (sp0 - 3968#64 - 4096#64) 8320) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp0 - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp0 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp0 - 3968#64) 4096 (by decide),
      show (16384 : Nat) = 3968 + 12416 from rfl,
      stackFrameAt_split sp0 3968 12416 (by decide),
      show (12416 : Nat) = 4096 + 8320 from rfl,
      stackFrameAt_split (sp0 - 3968#64) 4096 8320 (by decide)]

theorem stackAt_allocHook_split16 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 16 ∗ stackFrameAt (sp - 16#64) 4080 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 16 + 4080 from rfl,
      stackFrameAt_split sp 16 4080 (by decide)]

theorem stackAt_allocHook_split208 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 208 ∗ stackFrameAt (sp - 208#64) 3888 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 208 + 3888 from rfl,
      stackFrameAt_split sp 208 3888 (by decide)]

theorem stackAt_allocHook_split256 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 0x100 ∗ stackFrameAt (sp - 256#64) 3840 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 256 + 3840 from rfl,
      stackFrameAt_split sp 256 3840 (by decide)]

theorem stackAt_allocHook_split1120 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 1120 ∗ stackFrameAt (sp - 1120#64) 2976 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 1120 + 2976 from rfl,
      stackFrameAt_split sp 1120 2976 (by decide)]

theorem spAligned_sub3968 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 3968#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp0 &&& 15#64 = 0#64 := beq_iff_eq.mp h
  exact beq_iff_eq.mpr (by revert h0; bv_bits)

theorem memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

theorem memRegion16_eq_exists_pts (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1)) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split p 8 8 (by decide),
      memRegion_eight, memRegion_eight, sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right]

theorem vecU8_cbc_pack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ret newPtr : BitVec 64) (rawBs : List (BitVec 8)) (ctLen ptLen : Nat)
    (hlen : rawBs.length = ctLen) (hpos : 0 < ctLen) (hle : ptLen ≤ ctLen)
    (hlt63 : ctLen < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let capBv := BitVec.ofNat 64 ctLen
    let lenBv := BitVec.ofNat 64 ptLen
    (((ret ↦₆₄ capBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr ctLen 1 ∗ (newPtr ↦ₛ rawBs)) ⊢
      vecU8 A.repAlloc ret (rawBs.take ptLen) := by
  intro capBv lenBv
  have hcapNat : capBv.toNat = ctLen := by
    dsimp only [capBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : capBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hcapNat] at this; change ctLen = 0 at this; omega
  have htakeLen : (rawBs.take ptLen).length = ptLen := List.length_take_of_le (by omega)
  have hdropLen : (rawBs.drop ptLen).length = ctLen - ptLen := by rw [List.length_drop]; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right capBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hcapNat, htakeLen]
  have hLiveEq : A.repAlloc.live newPtr ctLen 1 = A.live newPtr ctLen 1 := rfl
  rw [hLiveEq, pointsToBytes_take_drop newPtr ptLen rawBs (by omega)]
  have hTail :
      ((newPtr + BitVec.ofNat 64 ptLen) ↦ₛ rawBs.drop ptLen) ⊢
        memRegion (newPtr + BitVec.ofNat 64 ptLen) (ctLen - ptLen) := by
    rw [← hdropLen]
    exact pointsToBytes_entails_memRegion _ _
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hTail))) ?_
  refine Entails.trans
    (Entails.pure_right (φ := ptLen ≤ ctLen ∧ ctLen < 2 ^ 63 ∧ newPtr ≠ 0)
      ⟨hle, hlt63, hne0⟩ (Entails.refl _))
    (Entails.of_eq (by dsimp only [lenBv]; sep_ac_rfl))

abbrev cbcSlack (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 3968#64 - 4096#64) 8320

abbrev cbcPost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (rconAddr errStr1Addr errStr2Addr : BitVec 64)
    (x : AesCall) (st : M.σ) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (cbcSlack s0 ∗ R)) →
      sf.mem ⊨
        (withRoDataSep rconAddr aesRconBytes
          (aesDecBudgetCondSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)).post
          (x, st) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev cbcPanic {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : AesCall) (st : M.σ) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ (cbcSlack s0 ∗ R)) →
      sf.mem ⊨ (aesDecBudgetCondSpec Spec.Aes256.aes256Dec M A lim).onPanic (x, st) s0 sf ∗ R

abbrev cbcOom (M : AllocCostModel) (lim : BudgetLimits)
    (x : AesCall) (st : M.σ) (s0 : State) : State → SepProp :=
  fun sf => ⌜¬ FitsEvents M lim st (aesDecEvents Spec.Aes256.aes256Dec x) ∧ OomPreserved s0 sf⌝

abbrev savedCells96 (sp0 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ c0) ∗ ((sp0 - 88#64) ↦₆₄ c1) ∗
  ((sp0 - 80#64) ↦₆₄ c2) ∗ ((sp0 - 72#64) ↦₆₄ c3) ∗
  ((sp0 - 64#64) ↦₆₄ c4) ∗ ((sp0 - 56#64) ↦₆₄ c5) ∗
  ((sp0 - 48#64) ↦₆₄ c6) ∗ ((sp0 - 40#64) ↦₆₄ c7) ∗
  ((sp0 - 32#64) ↦₆₄ c8) ∗ ((sp0 - 24#64) ↦₆₄ c9) ∗
  ((sp0 - 16#64) ↦₆₄ c10) ∗ ((sp0 - 8#64) ↦₆₄ c11)

abbrev savedStack96 (s0 : State) : SepProp :=
  savedCells96 s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .lr)
    (s0.readReg64 .x28) (s0.readReg64 .x27)
    (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

abbrev slots56 (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : SepProp :=
  (sp ↦₆₄ w0) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 16#64) ↦₆₄ w2) ∗
  ((sp + 24#64) ↦₆₄ w3) ∗ ((sp + 32#64) ↦₆₄ w4) ∗
  ((sp + 40#64) ↦₆₄ w5) ∗ ((sp + 48#64) ↦₆₄ w6)

theorem stackFrameAt96_eq_savedCells (sp0 : BitVec 64) :
    stackFrameAt sp0 96 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
        ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        savedCells96 sp0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) := by
  simp only [reduceStackFrameAt]

theorem stackFrameAt56_eq_slots (sp0 : BitVec 64) :
    stackFrameAt (sp0 - 3912#64) 56 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        slots56 (sp0 - 3968#64) w0 w1 w2 w3 w4 w5 w6) := by
  simp only [reduceStackFrameAt]
  have h0 : sp0 - 3912#64 - 56#64 = sp0 - 3968#64 := by bv_lin
  have h1 : sp0 - 3912#64 - 48#64 = sp0 - 3968#64 + 8#64 := by bv_lin
  have h2 : sp0 - 3912#64 - 40#64 = sp0 - 3968#64 + 16#64 := by bv_lin
  have h3 : sp0 - 3912#64 - 32#64 = sp0 - 3968#64 + 24#64 := by bv_lin
  have h4 : sp0 - 3912#64 - 24#64 = sp0 - 3968#64 + 32#64 := by bv_lin
  have h5 : sp0 - 3912#64 - 16#64 = sp0 - 3968#64 + 40#64 := by bv_lin
  have h6 : sp0 - 3912#64 - 8#64 = sp0 - 3968#64 + 48#64 := by bv_lin
  simp only [slots56, h0, h1, h2, h3, h4, h5, h6]

theorem slots56_pack (sp0 w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    slots56 (sp0 - 3968#64) w0 w1 w2 w3 w4 w5 w6 ⊢ stackFrameAt (sp0 - 3912#64) 56 := by
  rw [stackFrameAt56_eq_slots sp0]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
        (Entails.sepExists_right w6 (Entails.refl _)))))))

theorem savedCells96_pack (sp0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) :
    savedCells96 sp0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 ⊢ stackFrameAt sp0 96 := by
  simp only [reduceStackFrameAt]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right c2 (Entails.sepExists_right c3
    (Entails.sepExists_right c4 (Entails.sepExists_right c5
    (Entails.sepExists_right c6 (Entails.sepExists_right c7
    (Entails.sepExists_right c8 (Entails.sepExists_right c9
    (Entails.sepExists_right c10 (Entails.sepExists_right c11 (Entails.refl _))))))))))))

theorem stackFrame3968_split (sp0 : BitVec 64) :
    stackFrameAt sp0 3968 =
      stackFrameAt sp0 96 ∗
        memRegion (sp0 - 3968#64 + 56#64) 3816 ∗
        stackFrameAt (sp0 - 3912#64) 56 := by
  rw [show (3968 : Nat) = 96 + 3872 from rfl,
      stackFrameAt_split sp0 96 3872 (by decide),
      show (3872 : Nat) = 3816 + 56 from rfl,
      stackFrameAt_split (sp0 - 96#64) 3816 56 (by decide),
      stackFrameAt_eq_memRegion (sp0 - 96#64) 3816 (by decide)]
  have ha : sp0 - 96#64 - 3816#64 = sp0 - 3912#64 := by bv_lin
  have hb : sp0 - 3912#64 = sp0 - 3968#64 + 56#64 := by bv_lin
  rw [ha, ← hb]

theorem pack_stackFrame3968 (s0 : State) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
      memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
      savedStack96 s0) ⊢ stackFrameAt s0.sp 3968 := by
  rw [stackFrame3968_split s0.sp]
  refine Entails.trans
    (sepConj_mono (slots56_pack s0.sp w0 w1 w2 w3 w4 w5 w6)
      (sepConj_mono_right (savedCells96_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Shared 8-instruction return epilogue at `fnAddr + 0x65c#64` (`0x4c97b0..0x4c97cc`):
    deallocates `0xf20` bytes, restores `x19..x30` from `savedStack96 s0` (post-incrementing `sp`
    by `0x60`), and returns to `s0.readReg64 .lr`. -/
theorem cbc_common_ret {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (rconAddr errStr1Addr errStr2Addr : BitVec 64)
    {P : Program} {fnAddr : BitVec 64}
    (hEpi : hasInstrs P (fnAddr + 0x65c#64) (decodeWords cbcRetEpilogueWords))
    (x : AesCall) (st st' : M.σ) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (OutProp R : SepProp) (s0 sm : State)
    (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x65c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 3968#64)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres : AllocCallPreserved s0 sm)
    (hst' : st' = M.stepEvents (aesDecEvents Spec.Aes256.aes256Dec x) st)
    (hOut : OutProp ⊢
      x.frame ∗
        (match aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
         | some pt => vecU8 A.repAlloc x.ret pt
         | none => (x.ret ↦₆₄ errTag) ∗
             (∃∗ p : BitVec 64, ∃∗ len : BitVec 64,
               ⌜(p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)⌝ ∗
               ((x.ret + 8#64) ↦₆₄ p) ∗ ((x.ret + 16#64) ↦₆₄ len)))) :
    SepWPp P (s0.readReg64 .lr) sm
      ((rconAddr ↦ᵣ aesRconBytes) ∗
        OutProp ∗
        slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
        memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
        savedStack96 s0 ∗
        A.pool lim st' sm ∗
        stackAt (s0.sp - 3968#64) allocHookStack)
      (cbcPost A lim rconAddr errStr1Addr errStr2Addr x st R s0)
      (cbcPanic A lim x st R s0)
      (cbcOom M lim x st s0) := by
  have_instrs hEpi 0 8
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl96 : decide ((s0.sp - 96#64) &&& 15#64 = 0#64) = true := by
    have h0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hspAl0
    exact decide_eq_true (by revert h0; bv_bits)
  have hspAdd : s0.sp - 3968#64 + 3872#64 = s0.sp - 96#64 := by bv_lin
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [savedStack96, savedCells96]
  wp_step
  try simp only [hspAdd]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [wp_norm, arm64_norm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  have hpresf : AllocCallPreserved s0 sf := by
    rw [hsf]; exact allocCallPreserved_trans hpres
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpoolf : A.pool lim st' sf = A.pool lim st' sm := by
    rw [hsf]; exact (PureStepPreserved.of_proj_perm (by simp [arm64_norm]) (by simp [arm64_norm])).pool_eq A lim st'
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  dsimp only [cbcPost, cbcSlack, withRoDataSep, aesDecBudgetCondSpecErrRo] at hmf ⊢
  rw [← hst', hpoolf, extHookStack_split_3968 s0.sp]
  have hmf1 : sf.mem ⊨
      ((rconAddr ↦ᵣ aesRconBytes) ∗ OutProp ∗
        A.pool lim st' sm ∗
        ((slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
          memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
          savedStack96 s0) ∗
         (stackAt (s0.sp - 3968#64) allocHookStack ∗ cbcSlack s0))) ∗ R :=
    Satisfies.mono (Entails.of_eq (by dsimp only [savedStack96, savedCells96]; sep_ac_rfl)) hmf
  have hmf2 := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono hOut
          (sepConj_mono_right (sepConj_mono_left (pack_stackFrame3968 s0 w0 w1 w2 w3 w4 w5 w6)))))) hmf1
  let OutVal := match aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
    | some pt => vecU8 A.repAlloc x.ret pt
    | none => (x.ret ↦₆₄ errTag) ∗
        (∃∗ p : BitVec 64, ∃∗ len : BitVec 64,
          ⌜(p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)⌝ ∗
          ((x.ret + 8#64) ↦₆₄ p) ∗ ((x.ret + 16#64) ↦₆₄ len))
  change sf.mem ⊨
    ((rconAddr ↦ᵣ aesRconBytes) ∗
      (⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗ OutVal ∗ A.pool lim st' sm ∗
        (stackFrameAt s0.sp 3968 ∗
          (stackAt (s0.sp - 3968#64) allocHookStack ∗ stackFrameAt (s0.sp - 3968#64 - 4096#64) 8320)))) ∗ R
  have hGoalEq :
      ((rconAddr ↦ᵣ aesRconBytes) ∗
        (⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗ OutVal ∗ A.pool lim st' sm ∗
          (stackFrameAt s0.sp 3968 ∗
            (stackAt (s0.sp - 3968#64) allocHookStack ∗ stackFrameAt (s0.sp - 3968#64 - 4096#64) 8320)))) ∗ R =
      ⌜AllocCallPreserved s0 sf⌝ ∗
        (((rconAddr ↦ᵣ aesRconBytes) ∗ (x.frame ∗ OutVal) ∗ A.pool lim st' sm ∗
          (stackFrameAt s0.sp 3968 ∗
            (stackAt (s0.sp - 3968#64) allocHookStack ∗ stackFrameAt (s0.sp - 3968#64 - 4096#64) 8320))) ∗ R) := by
    sep_ac_rfl
  rw [hGoalEq, satisfies_pure_sepConj]
  exact ⟨hpresf, Satisfies.mono (Entails.of_eq (by dsimp only [OutVal, cbcSlack]; try sep_ac_rfl)) hmf2⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
