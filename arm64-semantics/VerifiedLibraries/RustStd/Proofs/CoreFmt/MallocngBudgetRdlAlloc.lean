/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.MallocngBudgetRdlCommon

/-!
# Placed Budgeted `__rdl_alloc`

Proves `rdlAlloc_budget_placed_ok`, showing that the placed 22-instruction `__rustc::__rdl_alloc`
(`rdlAllocInstrs`) satisfies
`rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)` under
`MallocngBudgetCContracts M I extra P mAddrs cAddrs`, splitting `Rust.hookFrame` across the
`malloc` fast path (`align ≤ 16 ∧ align ≤ size`) and `posix_memalign` slow path. Also derives
`rustBudgetAlloc_of_b_thunk` and `rdlAlloc_budget_thunk_ok` for the 1-instruction `B` thunk
`__rustc::__rust_alloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Local helpers -/

private theorem stackFrameAt32_eq' (sp : BitVec 64) :
    stackFrameAt sp 32 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack32' (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
     ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢ stackFrameAt sp 32 := by
  rw [stackFrameAt32_eq' sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem spAligned_sub32' {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 32#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem Satisfies.focus_weaken' {m : Memory} {Full T Q F : SepProp}
    (h : m ⊨ Full) (hEnt : T ⊢ Q) (hf : Full = T ∗ F := by sep_focus) : m ⊨ Q ∗ F := by
  rw [hf] at h
  exact Satisfies.mono (sepConj_mono_left hEnt) h

private theorem Entails.focus' {Full T Q F : SepProp}
    (hEnt : T ⊢ Q) (hf : Full = T ∗ F := by sep_focus) : Full ⊢ Q ∗ F := by
  rw [hf]; exact sepConj_mono_left hEnt

private theorem vmOk_of_eqs {lim : MallocngBudgetLimits} {staticIvs ivs : List (BitVec 64 × Nat)}
    {s s' : State} (h : MallocngBudgetVmOk lim staticIvs ivs s)
    (hBs : s'.brkStart = s.brkStart) (hBrk : s'.brk = s.brk) (hTp : s'.tpidrEl0 = s.tpidrEl0)
    (hPhys : s'.physMemAvail = s.physMemAvail) (hPerm : ∀ a, s'.mem.perm a = s.mem.perm a) :
    MallocngBudgetVmOk lim staticIvs ivs s' :=
  (MallocngBudgetVmOk.transport ⟨⟨hBs, hBrk, hTp⟩, hPhys, hPerm⟩).mpr h

private theorem step_str64_perm' {prog : Program} {target_pc pc ea val : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm
  let m' := s.mem.write64 ea val
  have hm' := hstore.store hm
  have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write64 s.mem ea val)
  unfold SepWP at hn; exact hn R hm'

private theorem step_stp64_perm' {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm
  have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm
  have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))
  unfold SepWP at hn; exact hn R hm2

/-! ## `malloc` fast path (`align ≤ 16 ∧ align ≤ size`) -/

private theorem rdlBudgetAlloc_fast_path {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {mallocAddr : BitVec 64}
    (hMalloc : subroutine_ok P mallocAddr
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelMallocSpec M I ProofLib.allocMallocng γ mAddrs) P.base)))
    (sizeBv alignBv : BitVec 64) (st : M.σ)
    (staticIvs ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAl16 : alignBv.toNat ≤ 16)
    (hAlSz : alignBv.toNat ≤ sizeBv.toNat)
    (hVmOk1 : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hpc1 : s1.pc = mallocAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp) (hx0_1 : s1.readReg64 .x0 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hbrk1 : s1.brk = s0.brk) :
    let A := mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs
    let xR : Nat × Nat × A.σ := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustBudgetAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustBudgetAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hEff : mallocngAlignedEffSize alignBv.toNat sizeBv.toNat = sizeBv.toNat := by
    unfold mallocngAlignedEffSize; simp [hAl16]
  have hEvs : rustAllocEvents sizeBv.toNat alignBv.toNat = [.alloc sizeBv.toNat] := by
    simp [rustAllocEvents, hAl16, hAlSz]
  have hEnv1 :
      MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 =
        MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s1 := by
    unfold MallocngModelEnv; rw [hpres01.2.2.2.1, hpres01.2.2.2.2.1, hbrk1]
  let F := stackFrameAt (s0.sp - 1024#64) 3072
  let xM := (sizeBv, s0.sp, s0.tpidrEl0, s0.brkStart, st, ivs0)
  refine SepWP.call_subroutine_frame (F := F) (x := xM) hMalloc
    (ret_pc := s0.readReg64 Reg.lr)
    hpc1 hrun1 (by simpa [State.spAligned, hsp1] using hsp_align) hlr1
    (fun R' hsat => ?_)
    (fun _ _ _ hp => by
      dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelMallocSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelMallocSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelMallocSpec, xM, F]
    rw [hookFrame_eq_stack1024 s0.sp, hEnv1] at hsat
    have hsat' : s1.mem ⊨
        ((MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s1 ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗ extra) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R') :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hsat
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hsat'
    exact Entails.pure_right ⟨hx0_1, hsp1, trivial⟩ (Entails.refl _)
  · refine SepWP.done hpc_f hrun_f
      ⟨fun hsat => ?_, hsp_f.trans hsp1, calleeSavedPreserved_trans hcs1 hcs_f⟩
    dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelMallocSpec, xM, F] at hsat
    dsimp only [rustBudgetAllocSpec, xR, A, mallocngRustAllocBudget]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsat
    obtain ⟨hPhysEq, hsat⟩ := hsat
    by_cases hFit : sizeBv.toNat ≤ MallocngMaxAllocSize
    · have hOkT : decide (sizeBv.toNat ≤ MallocngMaxAllocSize) = true := decide_eq_true hFit
      simp only [hOkT, ↓reduceIte, OptOwn] at hsat
      obtain ⟨⟨⟨hNe, _, h16, _⟩, hAcc1⟩, hsat⟩ := extract_pure hsat
      have hNe0 : sf.readReg64 .x0 ≠ 0 := hNe
      have hMod : (sf.readReg64 .x0).toNat % alignBv.toNat = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (pow2_dvd_16_of_le_16 hPow2 hAl16) h16)
      have hPres : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hpres01 (allocCallPreserved_of_mallocngProcPreserved hAcc1.1)
      have hMax : max alignBv.toNat 16 = 16 := Nat.max_eq_right hAl16
      simp only [hNe0, ↓reduceIte, hEvs, RustAllocBudget.stepEvents_singleton, mallocngBudgetLive,
        hMax]
      rw [hookFrame_eq_stack1024 s0.sp, pure_sepConj_of_true hPres, pure_sepConj_of_true hMod,
        pure_sepConj_of_true ⟨hMod, hLayout⟩]
      have hPool := modelPostEnv_entails_budgetPool (I := I) lim extra γ mAddrs
        (tp := s0.tpidrEl0) (brkStart := s0.brkStart) (stf := M.step (.alloc sizeBv.toNat) st)
        hVmOk1 hPhysEq
      have h2 := Satisfies.focus_weaken' hsat hPool
      exact Satisfies.mono (by sep_entail) h2
    · have hOkF : decide (sizeBv.toNat ≤ MallocngMaxAllocSize) = false := decide_eq_false hFit
      simp only [hOkF, Bool.false_eq_true, ↓reduceIte, OptOwn] at hsat
      obtain ⟨⟨_, hAcc1⟩, hsat⟩ := extract_pure hsat
      obtain ⟨hret0, hsat⟩ := extract_pure hsat
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      have hPres : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hpres01 (allocCallPreserved_of_mallocngProcPreserved hAcc1.1)
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := by
        refine not_layoutFit_imp_gt_2pow62 ?_
        unfold MallocngLayoutFit; rw [hEff]; exact hFit
      simp only [hret0', ↓reduceIte]
      have hN : ∀ Q : SepProp, Q ∗ ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ = Q := fun Q => by
        rw [sepConj_comm, pure_sepConj_of_true hNull]
      rw [hN, hookFrame_eq_stack1024 s0.sp, pure_sepConj_of_true hPres]
      have hPool := modelPostEnv_entails_budgetPool (I := I) lim extra γ mAddrs
        (tp := s0.tpidrEl0) (brkStart := s0.brkStart) (stf := st) hVmOk1 hPhysEq
      have h2 := Satisfies.focus_weaken' hsat hPool
      exact Satisfies.mono (by sep_entail) h2
  · dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelMallocSpec, xM] at ho
    dsimp only [rustBudgetAllocSpec, xR]
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at ho
    obtain ⟨hPhysEq, hOom, hFR⟩ := ho
    rw [satisfies_pure_sepConj]
    refine ⟨⟨?_, oomPreserved_of_allocCall_stepOom hpres01 hOom⟩, Satisfies.drop_left hFR⟩
    rw [hEvs]
    exact fun hF => mallocngBudget_not_fits_of_oom (ev := .alloc sizeBv.toNat)
      (ok := decide (sizeBv.toNat ≤ MallocngMaxAllocSize)) hVmOk1 hHeapLen hHeapSum
      (fun hW => decide_eq_true hW) rfl hPhysEq hOom hF.1

/-! ## Shared epilogue (`ldr x0, [sp, #8]; ldp x29, x30; csel; add sp; ret`) -/

private theorem rdlBudgetAlloc_epilogue {P : Program}
    {allocAddr mallocAddr posixMemalignAddr : BitVec 64}
    (hCode : hasInstrs P allocAddr (rdlAllocInstrs allocAddr mallocAddr posixMemalignAddr))
    (s0 s3 : State) (w0 q : BitVec 64) (Rest : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = allocAddr + 0x40#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 32#64)
    (hcs3 : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s3.readReg64 r = s0.readReg64 r)
    (hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 =
        (if ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) then q else 0#64) →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s3 sf →
      VmPreserved s3 sf →
      post sf (Rust.hookFrame s0.sp ∗ Rest)) :
    SepWP P (s0.readReg64 Reg.lr) s3
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest)
      post oom := by
  have hf16 := fetch_instr_at 16 hCode
  have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode
  have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode
  have hf21 := fetch_instr_at 21 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub32' hspAl0))
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hRepack :
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest) ⊢
      Rust.hookFrame s0.sp ∗ Rest := by
    rw [hookFrame_eq_stack32_1024 s0.sp, ← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_left (pack_stack32' s0.sp w0 q _ _))
  refine SepWP.weaken_pre hRepack ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun3]) ?_
  refine hpost _ (by simp [arm64_norm]) (by simp [arm64_norm]) ?_
    ⟨by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩, by simp [arm64_norm],
     fun _ => by simp [arm64_norm]⟩
  refine ⟨by simpa [arm64_norm] using hcs3 .x19 (by simp),
    by simpa [arm64_norm] using hcs3 .x20 (by simp),
    by simpa [arm64_norm] using hcs3 .x21 (by simp),
    by simpa [arm64_norm] using hcs3 .x22 (by simp),
    by simpa [arm64_norm] using hcs3 .x23 (by simp),
    by simpa [arm64_norm] using hcs3 .x24 (by simp),
    by simpa [arm64_norm] using hcs3 .x25 (by simp),
    by simpa [arm64_norm] using hcs3 .x26 (by simp),
    by simpa [arm64_norm] using hcs3 .x27 (by simp),
    by simpa [arm64_norm] using hcs3 .x28 (by simp),
    by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hv3⟩

/-! ## `posix_memalign` call and collapse -/

private theorem rdlBudgetAlloc_posix_call {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelPosixMemalignSpec M I ProofLib.allocMallocng γ mAddrs)
          P.base)))
    (sizeBv alignBv w0 : BitVec 64) (st : M.σ)
    (staticIvs ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬(alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st) :
    let effAlign := if ConditionHolds .HI (subsPState64 alignBv 8#64) then alignBv else 8#64
    let retPC := allocAddr + 0x40#64
    let A := mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs
    let xR : Nat × Nat × A.σ := (sizeBv.toNat, alignBv.toNat, st)
    MallocngBudgetVmOk lim staticIvs ivs0 s2 →
    s2.pc = cAddrs.posixMemalign →
    s2.status = .Running →
    s2.sp = s0.sp - 32#64 →
    s2.readReg64 .x0 = s0.sp - 24#64 →
    s2.readReg64 .x1 = effAlign →
    s2.readReg64 .x2 = sizeBv →
    s2.readReg64 Reg.lr = retPC →
    (∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s2.readReg64 r = s0.readReg64 r) →
    calleeSavedVRegs s2 = calleeSavedVRegs s0 →
    AllocCallPreserved s0 s2 →
    s2.brk = s0.brk →
    SepWP P (s0.readReg64 Reg.lr) s2
      (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustBudgetAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustBudgetAllocSpec A).onOom xR s0 sf) := by
  intro effAlign retPC A xR hVmOk2 hpc2 hrun2 hsp2 hx0_2 hx1_2 hx2_2 hlr2 hcs2 hv2 hpres02 hbrk2
  obtain ⟨hEffNat, _hEffGe8, hEffMax, _hPowEff, hEffMax16, hEffSz, hPosixOk, hPosixRet⟩ :=
    effAlign_props (size := sizeBv) hPow2 hAlMax
  change effAlign.toNat = max alignBv.toNat 8 at hEffNat
  change effAlign.toNat ≤ MaxAlignedAllocAlign at hEffMax
  change max effAlign.toNat 16 = max alignBv.toNat 16 at hEffMax16
  change mallocngAlignedEffSize effAlign.toNat sizeBv.toNat = _ at hEffSz
  change mallocngPosixMemalignOk effAlign sizeBv = _ at hPosixOk
  change mallocngPosixMemalignRet effAlign sizeBv = _ at hPosixRet
  have hEvs : rustAllocEvents sizeBv.toNat alignBv.toNat =
      [.aligned effAlign.toNat sizeBv.toNat] := by
    unfold rustAllocEvents
    split
    · exact absurd ‹_› hSlow
    · rw [hEffNat]
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32' hspAl0
  let FrameF := stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
    ((s0.sp - 32#64) ↦₆₄ w0) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  let xP := (s0.sp - 24#64, effAlign, sizeBv, s0.sp - 32#64, s0.tpidrEl0, s0.brkStart, st, ivs0)
  refine SepWP.call_subroutine_frame (F := FrameF) (x := xP) hPosix (ret_pc := retPC)
    hpc2 hrun2 (by simpa [State.spAligned, hsp2] using hspAl32b) hlr2
    (fun R' hsat => ?_)
    (fun _ _ _ hp => by
      dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun s3 hpc3 hrun3 hsp3 hcs3 => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec, xP, OptOutPtr,
      FrameF]
    have hEnv2 :
        MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 =
          MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s2 := by
      unfold MallocngModelEnv; rw [hpres02.2.2.2.1, hpres02.2.2.2.2.1, hbrk2]
    rw [hEnv2] at hsat
    have h1 := Satisfies.focus_weaken' hsat (pointsTo64_entails_memRegion8 (s0.sp - 24#64) 0#64)
    rw [pure_sepConj_of_true]
    · exact Satisfies.mono (by sep_entail) h1
    · exact ⟨hx0_2, hx1_2, hx2_2, hsp2, trivial, trivial, trivial, hEffMax⟩
  · dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec, xP, OptOutPtr]
    rw [hPosixOk, hPosixRet]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hPhysEq
    apply SepWP.pure_elim; rintro ⟨_, hw0_3, hAcc23⟩
    have hcs3_regs : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
        s3.readReg64 r = s0.readReg64 r := by
      obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, _, _⟩ := hcs3
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d19.trans (hcs2 .x19 (by simp))
      · exact d20.trans (hcs2 .x20 (by simp))
      · exact d21.trans (hcs2 .x21 (by simp))
      · exact d22.trans (hcs2 .x22 (by simp))
      · exact d23.trans (hcs2 .x23 (by simp))
      · exact d24.trans (hcs2 .x24 (by simp))
      · exact d25.trans (hcs2 .x25 (by simp))
      · exact d26.trans (hcs2 .x26 (by simp))
      · exact d27.trans (hcs2 .x27 (by simp))
      · exact d28.trans (hcs2 .x28 (by simp))
    have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hcs3.2.2.2.2.2.2.2.2.2.2.2.trans hv2
    have hsp3' : s3.sp = s0.sp - 32#64 := hsp3.trans hsp2
    have hpres03 : AllocCallPreserved s0 s3 :=
      allocCallPreserved_trans hpres02 (allocCallPreserved_of_mallocngProcPreserved hAcc23.1)
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · have hOkT : decide (MallocngLayoutFit sizeBv alignBv) = true := decide_eq_true hFit
      rw [hOkT]
      simp only [hFit, ↓reduceIte] at hw0_3
      unfold outPtrPost
      simp only [↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro q
      apply SepWP.pure_elim; rintro ⟨hqNe, hqDvd, _⟩
      let stT := M.step (.aligned effAlign.toNat sizeBv.toNat) st
      let RestOk := mallocngBudgetPool M I lim extra γ mAddrs stT s3 ∗
        I.BlockM γ q sizeBv.toNat (max effAlign.toNat 16) ∗ memRegion q sizeBv.toNat
      refine SepWP.weaken_pre (P' :=
        (((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
         (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestOk) ?_ ?_
      · refine Entails.trans (Entails.focus' (modelPostEnv_entails_budgetPool (I := I) lim extra γ
          mAddrs (tp := s0.tpidrEl0) (brkStart := s0.brkStart) (stf := stT) hVmOk2 hPhysEq)) ?_
        dsimp only [FrameF, RestOk, MallocngModelBlock]
        sep_entail
      refine rdlBudgetAlloc_epilogue hCode s0 s3 w0 q RestOk _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hvmf => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqTrue : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = true := by
        rw [hw0_3]; exact (cond_eq_subs32_iff_eq 0#32 0#32).mpr rfl
      have hx0_q : sf.readReg64 .x0 = q := by rw [hx0f, hEqTrue]; rfl
      have hqNe0 : q ≠ 0 := hqNe
      have hMod : q.toNat % alignBv.toNat = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (pow2_dvd_max16 hPow2) (hEffMax16 ▸ hqDvd))
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf := (A.pool_transport stT s3 sf hvmf).symm
      dsimp only [rustBudgetAllocSpec, A, xR, RestOk, mallocngRustAllocBudget] at hsat hPoolSf ⊢
      simp only [hx0_q, hqNe0, ↓reduceIte, hEvs, RustAllocBudget.stepEvents_singleton,
        mallocngBudgetLive]
      rw [hPoolSf, hEffMax16] at hsat
      rw [pure_sepConj_of_true hPres0f, pure_sepConj_of_true hMod,
        pure_sepConj_of_true ⟨hMod, hLayout⟩]
      exact Satisfies.mono (by sep_entail) hsat
    · have hOkF : decide (MallocngLayoutFit sizeBv alignBv) = false := decide_eq_false hFit
      rw [hOkF]
      simp only [hFit, ↓reduceIte] at hw0_3
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      apply SepWP.weaken_pre
        (sepConj_mono_left (RdlAllocH.memRegion8_entails_exists_pointsTo64 (s0.sp - 24#64)))
      simp only [sepExists_sepConj_left]
      apply SepWP.exists_elim; intro q
      let RestFail := mallocngBudgetPool M I lim extra γ mAddrs st s3
      refine SepWP.weaken_pre (P' :=
        (((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
         (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestFail) ?_ ?_
      · refine Entails.trans (Entails.focus' (modelPostEnv_entails_budgetPool (I := I) lim extra γ
          mAddrs (tp := s0.tpidrEl0) (brkStart := s0.brkStart) (stf := st) hVmOk2 hPhysEq)) ?_
        dsimp only [FrameF, RestFail]
        sep_entail
      refine rdlBudgetAlloc_epilogue hCode s0 s3 w0 q RestFail _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hvmf => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqFalse : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = false := by
        rw [hw0_3]; exact Bool.eq_false_iff.mpr fun h =>
          absurd ((cond_eq_subs32_iff_eq 12#32 0#32).mp h) (by decide)
      have hx0_0 : sf.readReg64 .x0 = 0 := by rw [hx0f, hEqFalse]; rfl
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf := (A.pool_transport st s3 sf hvmf).symm
      dsimp only [rustBudgetAllocSpec, A, xR, RestFail, mallocngRustAllocBudget] at hsat hPoolSf ⊢
      simp only [hx0_0, ↓reduceIte]
      rw [hPoolSf] at hsat
      have hN : ∀ Q : SepProp, Q ∗ ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ = Q := fun Q => by
        rw [sepConj_comm, pure_sepConj_of_true hNull]
      rw [hN, pure_sepConj_of_true hPres0f]
      exact Satisfies.mono (by sep_entail) hsat
  · dsimp only [withPhysAndExtra, ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec, xP] at ho
    dsimp only [rustBudgetAllocSpec, xR]
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at ho
    obtain ⟨hPhysEq, hOom, hFR⟩ := ho
    rw [satisfies_pure_sepConj]
    refine ⟨⟨?_, oomPreserved_of_allocCall_stepOom hpres02 hOom⟩, Satisfies.drop_left hFR⟩
    rw [hEvs]
    exact fun hF => mallocngBudget_not_fits_of_oom (ev := .aligned effAlign.toNat sizeBv.toNat)
      (ok := mallocngPosixMemalignOk effAlign sizeBv) hVmOk2 hHeapLen hHeapSum
      (fun hW => by
        rw [hPosixOk]; apply decide_eq_true; unfold MallocngLayoutFit; rw [← hEffSz]; exact hW)
      rfl hPhysEq hOom hF.1

/-! ## `posix_memalign` argument setup and slow path -/

private theorem rdlBudgetAlloc_posix_args {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelPosixMemalignSpec M I ProofLib.allocMallocng γ mAddrs)
          P.base)))
    (sizeBv alignBv w0 w1 : BitVec 64) (st : M.σ)
    (staticIvs ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 sm : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬(alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hVmOkm : MallocngBudgetVmOk lim staticIvs ivs0 sm)
    (hpcm : sm.pc = allocAddr + 0x2c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 32#64)
    (hpstm : sm.pstate = subsPState64 alignBv 8#64)
    (hx1_m : sm.readReg64 .x1 = alignBv) (hx2_m : sm.readReg64 .x2 = sizeBv)
    (hcsm : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      sm.readReg64 r = s0.readReg64 r)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres0m : AllocCallPreserved s0 sm) (hbrkm : sm.brk = s0.brk) :
    let A := mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs
    let xR : Nat × Nat × A.σ := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) sm
      (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustBudgetAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustBudgetAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hf11 := fetch_instr_at 11 hCode
  have hf12 := fetch_instr_at 12 hCode
  have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode
  have hf15 := fetch_instr_at 15 hCode
  have ha_sp8 : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hspm]; bv_omega
  wp_step; wp_step; wp_step
  apply step_str64_perm'
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  exact hf14
  wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_sep_access
  intro m hperm
  try wp_norm_state
  simp only [arm64_norm] at hperm
  wp_step
  exact rdlBudgetAlloc_posix_call hSound hReqLe lim extra γ allocAddr hCode hPosix
    sizeBv alignBv w0 st staticIvs ivs0 R s0 _
    hsp_align hLayout hPow2 hAlMax hSlow hHeapLen hHeapSum
    (vmOk_of_eqs hVmOkm (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (fun a => by simp [arm64_norm, hperm]))
    (by simp only [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrunm])
    (by simp [arm64_norm, hspm])
    (by simp only [arm64_norm])
    (by simp [arm64_norm])
    (by simp only [arm64_norm, hx2_m])
    (by simp only [arm64_norm])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa only [arm64_norm] using hcsm _ (by simp))
    (by simpa only [calleeSavedVRegs, arm64_norm] using hvm)
    (allocCallPreserved_trans hpres0m
      ⟨by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm]⟩)
    (by simp [arm64_norm, hbrkm])

private theorem rdlBudgetAlloc_posix_path {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelPosixMemalignSpec M I ProofLib.allocMallocng γ mAddrs)
          P.base)))
    (sizeBv alignBv : BitVec 64) (st : M.σ)
    (staticIvs ivs0 : List (BitVec 64 × Nat))
    (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬(alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hHeapLen : ivs0.length ≤ M.maxDynIvs st)
    (hHeapSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hVmOk1 : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hpc1 : s1.pc = allocAddr + 0x1c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp)
    (hx1_1 : s1.readReg64 .x1 = alignBv) (hx2_1 : s1.readReg64 .x2 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hbrk1 : s1.brk = s0.brk) :
    let A := mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs
    let xR : Nat × Nat × A.σ := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustBudgetAllocSpec A).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustBudgetAllocSpec A).onOom xR s0 sf) := by
  intro A xR
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32' hspAl0
  have hspAl32 : decide ((s0.sp - 32#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp hspAl32b)
  have hUnpack :
      MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗ extra ∗
          stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
          ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    rw [hookFrame_eq_stack32_1024 s0.sp, stackFrameAt32_eq' s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ => by ac_rfl))))
  rw [hUnpack]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have hf7 := fetch_instr_at 7 hCode
  have hf8 := fetch_instr_at 8 hCode
  have hf9 := fetch_instr_at 9 hCode
  have hf10 := fetch_instr_at 10 hCode
  have ha_sp : s1.sp + (-32#64) = s0.sp - 32#64 := by rw [hsp1]; bv_omega
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcs1
  have _ : s1.readReg64 (.gpr 29#5) = s0.readReg64 .x29 := c29
  wp_step
  apply step_stp64_perm'
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  exact hf8
  wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_norm_lhs
  wp_focus_close wp_sep_access
  wp_focus_close wp_sep_access
  intro m hperm
  try wp_norm_state
  simp only [arm64_norm] at hperm
  wp_step; wp_step
  exact rdlBudgetAlloc_posix_args hSound hReqLe lim extra γ allocAddr hCode hPosix
    sizeBv alignBv w0 w1 st staticIvs ivs0 R s0 _
    hsp_align hLayout hPow2 hAlMax hSlow hHeapLen hHeapSum
    (vmOk_of_eqs hVmOk1 (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (fun a => by simp [arm64_norm, hperm]))
    (by simp [arm64_norm])
    (by simp [arm64_norm, hrun1])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx1_1])
    (by simp [arm64_norm, hx2_1])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [arm64_norm] using c19
      · simpa only [arm64_norm] using c20
      · simpa only [arm64_norm] using c21
      · simpa only [arm64_norm] using c22
      · simpa only [arm64_norm] using c23
      · simpa only [arm64_norm] using c24
      · simpa only [arm64_norm] using c25
      · simpa only [arm64_norm] using c26
      · simpa only [arm64_norm] using c27
      · simpa only [arm64_norm] using c28)
    (by simpa only [calleeSavedVRegs, arm64_norm] using cv)
    (allocCallPreserved_trans hpres01
      ⟨by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm]⟩)
    (by simp [arm64_norm, hbrk1])

/-! ## Main theorem -/

/-- Placed `rustc 1.98.1` `__rustc::__rdl_alloc` (`22` instructions: `rdlAllocInstrs`) satisfies
    `rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)`. -/
theorem rdlAlloc_budget_placed_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hC : MallocngBudgetCContracts M I extra P mAddrs cAddrs) :
    subroutine_ok P allocAddr
      (rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [rustBudgetAllocSpec] at hpre
  obtain ⟨⟨hx0, hx1, hLayout⟩, hpreR⟩ := extract_pure hpre
  let sizeBv := s0.readReg64 .x0
  let alignBv := s0.readReg64 .x1
  have hx0_bv : s0.readReg64 .x0 = sizeBv := rfl
  have hx1_bv : s0.readReg64 .x1 = alignBv := rfl
  change sizeBv.toNat = size at hx0
  change alignBv.toNat = align at hx1
  subst hx0; subst hx1
  have ⟨_hSzPos, ⟨k, hk⟩, _hSum63, hAlMax⟩ := hLayout
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 hk
  have hAlMax' : alignBv.toNat ≤ MaxAlignedAllocAlign := hAlMax
  have hpre' : s0.mem ⊨ mallocngBudgetPool M I lim extra γ mAddrs st s0 ∗
      (Rust.hookFrame s0.sp ∗ R) := Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreR
  obtain ⟨ivs0, staticIvs, hVmOk0, hHeapLen, hHeapSum, hEnv⟩ :=
    mallocngBudgetPool_elim hSound hpre'
  have hEnvPre : s0.mem ⊨
      (MallocngModelEnv M I γ mAddrs s0.tpidrEl0 s0.brkStart st ivs0 s0 ∗
        extra ∗ Rust.hookFrame s0.sp) ∗ R :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hEnv
  refine ⟨_, hEnvPre, ?_⟩
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode
  have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode
  have hf5 := fetch_instr_at 5 hCode
  have hf6 := fetch_instr_at 6 hCode
  wp_step; wp_step
  by_cases hAl16 : alignBv.toNat ≤ 16
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = false :=
      Bool.eq_false_iff.mpr fun h => by
        have := (RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mp h
        change 16 < alignBv.toNat at this; omega
    wp_step; wp_step
    by_cases hAlSz : alignBv.toNat ≤ sizeBv.toNat
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := (RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mp h; omega
      wp_step; wp_step; wp_step
      exact rdlBudgetAlloc_fast_path hSound hReqLe lim extra γ (hC.malloc_ok γ)
        sizeBv alignBv st staticIvs ivs0 R s0 _
        hsp_align hLayout hPow2 hAl16 hAlSz
        (vmOk_of_eqs hVmOk0 (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (fun _ => by simp [arm64_norm]))
        hHeapLen hHeapSum
        (by simp only [State.pc_setPC]; bv_omega)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        (by simp [arm64_norm])
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = true :=
        (RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mpr (by omega)
      have hcond : (s0.readReg64 (Reg.gpr 0#5)).ult alignBv = true := by
        unfold BitVec.ult; exact decide_eq_true (by change sizeBv.toNat < alignBv.toNat; omega)
      wp_step
      exact rdlBudgetAlloc_posix_path hSound hReqLe lim extra γ allocAddr hCode
        (hC.posixMemalign_ok γ) sizeBv alignBv st staticIvs ivs0 R s0 _
        hsp_align hLayout hPow2 hAlMax' (fun h => hAlSz h.2) hHeapLen hHeapSum
        (vmOk_of_eqs hVmOk0 (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (fun _ => by simp [arm64_norm]))
        (by simp)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1_bv])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        (by simp [arm64_norm])
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = true :=
      (RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mpr (by change 16 < alignBv.toNat; omega)
    wp_step
    exact rdlBudgetAlloc_posix_path hSound hReqLe lim extra γ allocAddr hCode
      (hC.posixMemalign_ok γ) sizeBv alignBv st staticIvs ivs0 R s0 _
      hsp_align hLayout hPow2 hAlMax' (fun h => hAl16 h.1) hHeapLen hHeapSum
      (vmOk_of_eqs hVmOk0 (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (fun _ => by simp [arm64_norm]))
      (by simp only [State.pc_setPC])
      (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_bv])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      (by simp [arm64_norm])

/-! ## 1-instruction `B`-thunk corollaries (`__rustc::__rust_alloc`) -/

/-- Lift `subroutine_ok P targetAddr (rustBudgetAllocSpec A)` across a 1-instruction
    unconditional branch thunk `hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ]`. -/
theorem rustBudgetAlloc_of_b_thunk (A : RustAllocBudget)
    {P : Program} (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hTarget : subroutine_ok P targetAddr (rustBudgetAllocSpec A)) :
    subroutine_ok P thunkAddr (rustBudgetAllocSpec A) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨size, align, st⟩ s pc'
      dsimp only [rustBudgetAllocSpec]
      rw [A.pool_transport st s (s.setPC pc') ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩]
      rfl)
    (hpost_pc := by rintro ⟨_, _, _⟩ _ _ _; rfl)
    (hoom_pc := by rintro ⟨_, _, _⟩ _ _ _; rfl)
    (hok := hTarget)

/-- Placed 1-instruction `B` thunk (`__rustc::__rust_alloc` to `__rustc::__rdl_alloc`) satisfies
    `rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)`. -/
theorem rdlAlloc_budget_thunk_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (thunkAddr targetAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hCode : hasInstrs P targetAddr
      (rdlAllocInstrs targetAddr cAddrs.malloc cAddrs.posixMemalign))
    (hC : MallocngBudgetCContracts M I extra P mAddrs cAddrs) :
    subroutine_ok P thunkAddr
      (rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)) :=
  rustBudgetAlloc_of_b_thunk _ thunkAddr targetAddr hThunk
    (rdlAlloc_budget_placed_ok hSound hReqLe lim extra γ targetAddr hCode hC)

end VerifiedLibraries.RustStd
