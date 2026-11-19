/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.SubLink -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric

/-!
# Stage-B `GhostRowOk` & `HookOk` Glue for `lsFmtWriteSym` and `lsFormatInnerSym` (`C2RowLayoutFacts.CliFmtRow`)

Supplies the concrete 0-hook stock-ELF (`0d6227d2…`) `W`-independent `(γ, tp)`-independent ghost
hooks `c2FmtWriteGhost` (`lsFmtWriteSym`) and `c2FormatInnerGhost` (`lsFormatInnerSym`) along with:
1. Unconditional `HookOk` witnesses (`c2_fmtWriteGhost_ok`, `c2_formatInnerGhost_ok`).
2. `GhostRowSpecOk` witnesses (`c2_fmtWriteGhost_rowSpecOk`, `c2_formatInnerGhost_rowSpecOk`).
3. Trajectory-aware `GhostRowOk` witnesses (`c2_fmtWriteGhost_rowOk_guardOf`,
   `c2_formatInnerGhost_rowOk_guardOf`) via the contiguous `seg[1] ++ seg[2]` real-ELF RX program
   `c2FmtProg` and caller-`lr` trap `c2FmtProgTrap lr` on unstripped memory.
4. Unconditional `HookNoAllocFailed` witnesses (`c2_fmtWriteGhost_noAllocFailed`,
   `c2_formatInnerGhost_noAllocFailed`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.RustStd
  (allocFormatInnerSym allocMultiLib coreFmtWriteSym coreMultiLib)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocEvent BudgetLimits zeroBudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (lsFmtWriteSym lsFormatInnerSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (perm_writeVecHeader)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen keepFsTrace standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed traceDeltaNoAllocFailed_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc (keepRxSeg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
  (c2AllocMpl c2FormatInnerAddr c2_resolve_formatInner_eq c2_resolve_formatInner_fnAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
  (c2CoreFmtMpl c2CoreMpl c2FmtWriteAddr c2_resolve_fmtWrite_eq c2_resolve_fmtWrite_fnAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.AllocRo
  (c2AllocMpl_codeLoaded_of_c2FmtProg c2MplAllocCli c2MplAllocCli_handleError_resolve
   c2MplAllocCli_memcpy_resolve c2MplAllocCli_noAllocShim_resolve c2MplAllocCli_placeable
   c2MplAllocCli_rustAlloc_resolve c2MplAllocCli_rustRealloc_resolve
   c2MplAllocCli_stringWriter_codeLoaded c2MplAllocCli_vtable_eq c2_cliFmtWriteRoGuard
   c2_cliFormatInnerRoGuard c2_stringWriteVtableRoAt_alloc c2_stringWriteVtableRoAt_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code
  (c2FmtProg_codeLoaded_of_f3CodeInv ls_codeLoaded_of_c2FmtProg rxCode_of_c2FmtProg_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2EmptySeg c2FmtExterns c2FmtProg c2FmtProgTrap c2FmtProgTrap_codeLoaded_iff
   c2FmtProgTrap_svc c2FmtProg_svc c2FmtStubs c2HaltHook c2LrTrapSym c2Seg1 c2Seg1Bytes
   c2Seg1Start)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs
  (c2FmtProgTrap_blockExternFree_of_pre_lib2 c2FmtProgTrap_externAt_handleError
   c2FmtProgTrap_externAt_none_of_ge_stub_not_panic
   c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic c2FmtProgTrap_externAt_of_ne
   c2FmtProgTrap_externAt_self c2FmtProg_externAt_eq_real c2FmtProg_externAt_handleError
   c2FmtProg_externAt_none_of_lt_stub c2FmtProg_externAt_none_of_not_panic
   c2FmtProg_externAt_some_bounds)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.SubLink
  (c2_fmtWriteSubLink c2_formatInnerSubLink)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.TrapStubs
  (execInst_preserves_execFrozen fineHookPool_nonZeroEquivLim fitsEnv_nonZeroEquivLim
   instPoolMemTransportWithExecFrozen nonZeroEquivLim nonZeroEquivLim_ne_zero step_running
   steps_preserves_exception steps_preserves_halted withExecFrozenBudget
   withExecFrozenBudget_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
  (withFsTraceExact withRoMemGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays
  (fmtWriteGhostSpecOf fmtWriteGhostSpecOf_outcome_setPC fmtWriteGhostSpecOf_pre_setPC
   formatInnerGhostSpecOf formatInnerGhostSpecOf_outcome_setPC formatInnerGhostSpecOf_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (CliFmtWriteProtoAddrCall CliFormatInnerLsCall cliFmtWriteProtoAddrSpec cliFormatInnerLsCallSpec
   dotTplBytes extract_withLsRetFmtWrite extract_withLsRetFormatInner fmtWriteHook0_cliProtoAddr_ok
   fmtWriteProtoAddrCliLsSpec formatInnerCallCliLsSpec formatInnerHook0_cliLsCallSpec_ok
   hookOk_withLsRetFmtWrite hookOk_withLsRetFormatInner intro_withLsRetFmtWrite
   intro_withLsRetFormatInner withLsRetFmtWrite withLsRetFormatInner)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (ExactOrNilEnv cliFmtWriteEnv_nil cliFormatInnerEnv_nil exactOrNilEnv_exact exactOrNilEnv_imp
   exactOrNilEnv_nil fitsEnv_exactOrNil)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
  (cliAllocFormatInner_lsCall_ro_ok cliCoreFmtWrite_protoAddr_ro_ok
   cliFmtWriteRoGuard cliFormatInnerRoGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_stepsUntil_det)

export Defs (c2EmptySeg c2Seg1 c2Seg1Start c2Seg1Bytes c2FmtExterns)
export Defs (c2FmtStubs c2FmtProg c2LrTrapSym c2HaltHook c2FmtProgTrap)
export Defs (c2FmtProg_svc c2FmtProgTrap_svc c2FmtProgTrap_codeLoaded_iff)
export Code (c2FmtProg_codeLoaded_of_f3CodeInv rxCode_of_c2FmtProg_codeLoaded ls_codeLoaded_of_c2FmtProg)
export Externs (c2FmtProg_externAt_eq_real c2FmtProg_externAt_some_bounds c2FmtProg_externAt_none_of_lt_stub c2FmtProg_externAt_none_of_not_panic c2FmtProg_externAt_handleError)
export Externs (c2FmtProgTrap_externAt_self c2FmtProgTrap_externAt_of_ne c2FmtProgTrap_externAt_handleError c2FmtProgTrap_externAt_none_of_ge_stub_not_panic c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic)
export Externs (c2FmtProgTrap_blockExternFree_of_pre_lib2)
export AllocRo (c2MplAllocCli c2MplAllocCli_placeable c2MplAllocCli_vtable_eq c2MplAllocCli_handleError_resolve c2MplAllocCli_memcpy_resolve)
export AllocRo (c2MplAllocCli_noAllocShim_resolve c2MplAllocCli_rustAlloc_resolve c2MplAllocCli_rustRealloc_resolve c2MplAllocCli_stringWriter_codeLoaded c2AllocMpl_codeLoaded_of_c2FmtProg)
export AllocRo (c2_stringWriteVtableRoAt_cli c2_stringWriteVtableRoAt_alloc c2_cliFmtWriteRoGuard c2_cliFormatInnerRoGuard)
export TrapStubs (withExecFrozenBudget withExecFrozenBudget_repAlloc instPoolMemTransportWithExecFrozen)

attribute [local irreducible] c2FmtProg c2FmtProgTrap

/-! ### Stepping Bridges: `c2FmtProgTrap lr` → `StepsUntil c2FmtProg` → Real Block `617` -/

private theorem setPC_mem (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl

private theorem setPC_fs (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by
  cases s; rfl

private theorem setPC_trace (s : State) (pc : BitVec 64) : (s.setPC pc).trace = s.trace := by
  cases s; rfl

private theorem setPC_symtab (s : State) (pc : BitVec 64) : (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

private theorem setPC_lr (s : State) (pc : BitVec 64) :
    (s.setPC pc).readReg64 .lr = s.readReg64 .lr := by
  cases s; rfl

private theorem setPC_status (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by
  cases s; rfl

private theorem setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by
  cases s; rfl

private theorem setPC_setPC (s : State) (pc1 pc2 : BitVec 64) :
    (s.setPC pc1).setPC pc2 = s.setPC pc2 := by
  cases s; rfl

private theorem setPC_of_pc_eq {s : State} {pc : BitVec 64} (h : s.pc = pc) :
    s.setPC pc = s := by
  cases s; dsimp only at h; subst h; rfl

private theorem allocCallPreserved_of_setPC {s0 sf : State} {pc : BitVec 64}
    (h : LibsignalBinary.Heap.AllocCallPreserved (s0.setPC pc) sf) :
    LibsignalBinary.Heap.AllocCallPreserved s0 sf := by
  cases s0; cases sf; exact h

private theorem sp_mod16_iff_spAligned (s : State) :
    s.sp.toNat % 16 = 0 ↔ s.spAligned = true := by
  unfold State.spAligned
  rw [beq_iff_eq]
  have hm : (s.sp &&& 15#64).toNat = s.sp.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod s.sp.toNat 4
  constructor
  · intro h0
    apply BitVec.eq_of_toNat_eq
    rw [hm, h0, BitVec.toNat_ofNat]
  · intro heq
    rw [← hm, heq]
    rfl

private theorem c2FmtProg_evalInst_of_not_isSvc0 {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) : c2FmtProg.evalInst inst s = execInst inst s := by
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · rfl
  | _ => rfl

private theorem steps_c2FmtProg_preserves_execFrozen {s1 sf : State}
    (hs : Steps c2FmtProg s1 sf) (hfr1 : ExecFrozen s1.mem) :
    ExecFrozen sf.mem := by
  induction hs with
  | refl _ => exact hfr1
  | @step sa sb _ h1 _ ih =>
    apply ih
    cases h1 with
    | halt_unmapped _ _ _ => exact hfr1
    | @extern f _ he _ _ =>
      obtain ⟨hf, _, _⟩ := c2FmtProg_externAt_some_bounds he
      subst hf
      exact hfr1
    | extern_fault _ _ _ => exact hfr1
    | @exec inst _ _ =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have h := (standard_stripS (keep := keepRxSeg) hfr1).2
        simpa [Program.evalInst, execInstWithSvc, c2FmtProg_svc] using h
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        rw [c2FmtProg_evalInst_of_not_isSvc0 hnsvc0 sa]
        exact execInst_preserves_execFrozen hnsvc0 hfr1

private theorem step_c2FmtProg_to_real {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) {sa sb : State}
    (h1 : Step c2FmtProg sa sb) :
    Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) sa sb := by
  have hext := c2FmtProg_externAt_eq_real hLs mmpl W sa.pc
  have hsvc : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard := rfl
  cases h1 with
  | halt_unmapped hr hfm hne =>
    refine Step.halt_unmapped hr ?_ ?_
    · unfold Program.fetchMem at hfm ⊢
      rwa [← hext]
    · rwa [← hext]
  | extern hr he hkf hsym =>
    exact Step.extern hr (hext ▸ he) hkf hsym
  | extern_fault hr he hbad =>
    exact Step.extern_fault hr (hext ▸ he) hbad
  | @exec inst hr hfm =>
    have hfm_real : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem sa.mem sa.pc =
        some inst := by
      unfold Program.fetchMem at hfm ⊢
      rwa [← hext]
    have hev : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst inst sa =
        c2FmtProg.evalInst inst sa := by
      simp [Program.evalInst, execInstWithSvc, hsvc, c2FmtProg_svc]
    exact hev ▸ Step.exec hr hfm_real

private theorem steps_c2FmtProg_to_real {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) {s1 sf : State}
    (hs : Steps c2FmtProg s1 sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1 sf := by
  induction hs with
  | refl s => exact .refl s
  | step h1 _ ih => exact .step (step_c2FmtProg_to_real hLs mmpl W h1) ih

/-- Any non-halting, non-exception run on `c2FmtProgTrap lr` ending at `SubroutineStop s0` never
    stepped from `pc = lr` (since `c2FmtProgTrap lr` halts at `lr`), and therefore yields
    `StepsUntil c2FmtProg (SubroutineStop s0) s1 sf`. -/
private theorem stepsUntil_c2FmtProg_of_trap {s0 s1 sf : State}
    (hs : Steps (c2FmtProgTrap (s0.readReg64 .lr)) s1 sf)
    (hstop : SubroutineStop s0 sf)
    (hnhalt : sf.status ≠ .Halted)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg) :
    StepsUntil c2FmtProg (SubroutineStop s0) s1 sf := by
  let lr := s0.readReg64 .lr
  change Steps (c2FmtProgTrap lr) s1 sf at hs
  induction hs with
  | refl s => exact .refl s
  | @step sa sb _ h1 hrest ih =>
    have hra : sa.status = .Running := step_running h1
    have hne_lr : sa.pc ≠ lr := by
      intro hpc
      have he_trap : (c2FmtProgTrap lr).externAt? sa.pc = some c2HaltHook :=
        hpc ▸ c2FmtProgTrap_externAt_self lr
      cases h1 with
      | halt_unmapped _ _ hnone => rw [he_trap] at hnone; cases hnone
      | extern _ he _ _ =>
        rw [he_trap] at he; injection he with hf; subst hf
        exact hnhalt (steps_preserves_halted hrest rfl)
      | extern_fault _ _ _ =>
        exact hnoex _ (steps_preserves_exception hrest rfl)
      | exec _ hfm =>
        unfold Program.fetchMem at hfm
        simp [he_trap] at hfm
    have hnotStop : ¬ SubroutineStop s0 sa := by
      rintro (⟨hpc, _, _⟩ | hp | ⟨_, hex⟩ | ho)
      · exact hne_lr hpc
      · rw [hra] at hp; cases hp
      · rw [hra] at hex; cases hex
      · rw [hra] at ho; cases ho
    have hext_eq : (c2FmtProgTrap lr).externAt? sa.pc = c2FmtProg.externAt? sa.pc :=
      c2FmtProgTrap_externAt_of_ne hne_lr
    have h1_base : Step c2FmtProg sa sb := by
      cases h1 with
      | halt_unmapped hr hfm hnone =>
        refine Step.halt_unmapped hr ?_ (hext_eq ▸ hnone)
        unfold Program.fetchMem at hfm ⊢
        rwa [← hext_eq]
      | extern hr he hkf hsym =>
        exact Step.extern hr (hext_eq ▸ he) hkf hsym
      | extern_fault hr he hbad =>
        exact Step.extern_fault hr (hext_eq ▸ he) hbad
      | @exec inst hr hfm =>
        have hfm_base : c2FmtProg.fetchMem sa.mem sa.pc = some inst := by
          unfold Program.fetchMem at hfm ⊢
          rwa [← hext_eq]
        have hev : (c2FmtProgTrap lr).evalInst inst sa = c2FmtProg.evalInst inst sa := by
          simp [Program.evalInst, execInstWithSvc, c2FmtProgTrap_svc, c2FmtProg_svc]
        rw [hev]
        exact Step.exec hr hfm_base
    exact .step hnotStop h1_base (ih hstop hnhalt hnoex)

private theorem subroutineStop_of_outcome {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (hout : SubroutineOutcome spec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted ∧ (∀ msg, sf.status ≠ .Exception msg) := by
  rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨ec, he, _⟩ | ⟨ho, _⟩
  · refine ⟨Or.inl hret, ?_, ?_⟩
    · intro hh; have hs := hret.2.2; rw [hh] at hs; cases hs
    · intro msg hex; have hs := hret.2.2; rw [hex] at hs; cases hs
  · refine ⟨Or.inr (Or.inl hp), ?_, ?_⟩
    · intro hh; rw [hh] at hp; cases hp
    · intro msg hex; rw [hex] at hp; cases hp
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨ec, he⟩)), ?_, ?_⟩
    · intro hh; rw [hh] at he; cases he
    · intro msg hex; rw [hex] at he; cases he
  · refine ⟨Or.inr (Or.inr (Or.inr ho)), ?_, ?_⟩
    · intro hh; rw [hh] at ho; cases ho
    · intro msg hex; rw [hex] at ho; cases ho

/-! ## 5. `c2FmtGhost` Combinator & Concrete Public Exports -/

/-- Image-level guard for `c2FmtGhost`: executable pages frozen, `.rodata` slice guard satisfied,
    and contiguous `seg[1] ++ seg[2]` RX code loaded. -/
@[expose] def c2FmtImgGuard (roGuard : Memory → Prop) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧ roGuard s0.mem ∧ c2FmtProg.CodeLoaded s0.mem

/-- Active call precondition for `c2FmtGhost` across any `(γ, tp, x, R)`. -/
@[expose] def ActiveC2FmtPre {α : Type}
    (specOf : GhostName → BitVec 64 → Spec α) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.sp.toNat % 16 = 0 ∧
  ∃ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp),
    s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R

/-- Witnessed real-instruction run on `c2FmtProg` from `s0.setPC entryTarget` to `SubroutineStop s0`. -/
@[expose] def ActiveC2FmtRun {α : Type}
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α) (s0 : State) : Prop :=
  ∃ sf : State,
    StepsUntil c2FmtProg (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
    s0.mem.KeepsFrozen sf.mem ∧
    sf.oracle = s0.oracle ∧
    sf.symtab = s0.symtab ∧
    ExecFrozen sf.mem ∧
    sf.fs = s0.fs ∧
    sf.trace = s0.trace ∧
    ∀ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      SubroutineOutcome (specOf γ tp) x R s0 sf

/-- `W`-independent `(γ, tp)`-independent ghost hook running `c2FmtProg` on unstripped memory when
    `c2FmtImgGuard` holds and falling back to `keepFsTrace fallback` otherwise. -/
@[expose] noncomputable def c2FmtGhost {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State)
    (s0 : State) : State := by
  classical
  exact if c2FmtImgGuard roGuard s0 then
    if ActiveC2FmtPre specOf s0 then
      if hRun : ActiveC2FmtRun entryTarget specOf s0 then
        Classical.choose hRun
      else
        { s0 with status := .Exception "c2FmtGhost: subroutine_ok violated" }
    else
      { s0 with status := .Exception "c2FmtGhost: inactive precondition" }
  else
    keepFsTrace fallback s0

theorem c2FmtGhost_fs {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) (s0 : State) :
    (c2FmtGhost roGuard entryTarget specOf fallback s0).fs = s0.fs := by
  classical
  unfold c2FmtGhost
  split
  · split
    · split
      · rename_i hRun
        exact (Classical.choose_spec hRun).2.2.2.2.2.1
      · rfl
    · rfl
  · rfl

theorem c2FmtGhost_trace {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) (s0 : State) :
    (c2FmtGhost roGuard entryTarget specOf fallback s0).trace = s0.trace := by
  classical
  unfold c2FmtGhost
  split
  · split
    · split
      · rename_i hRun
        exact (Classical.choose_spec hRun).2.2.2.2.2.2.1
      · rfl
    · rfl
  · rfl

theorem c2FmtGhost_fsT {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    HookFsTraced IsFsC (c2FmtGhost roGuard entryTarget specOf fallback) :=
  fun s0 => FsTraced.of_eq (c2FmtGhost_trace roGuard entryTarget specOf fallback s0)
    (congrArg FsState.files (c2FmtGhost_fs roGuard entryTarget specOf fallback s0))

theorem c2FmtGhost_noAllocFailed {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    HookNoAllocFailed (c2FmtGhost roGuard entryTarget specOf fallback) :=
  fun s0 => traceDeltaNoAllocFailed_of_eq (c2FmtGhost_trace roGuard entryTarget specOf fallback s0)

theorem c2FmtGhost_preserves_execFrozen {α : Type}
    (roGuard : Memory → Prop) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) {fallback : State → State}
    (hFallbackPerm : ∀ s : State, (fallback s).mem.perm = s.mem.perm)
    {u : State} (hFr : ExecFrozen u.mem) :
    ExecFrozen (c2FmtGhost roGuard entryTarget specOf fallback u).mem ∧
      (c2FmtGhost roGuard entryTarget specOf fallback u).fs = u.fs := by
  classical
  refine ⟨?_, c2FmtGhost_fs roGuard entryTarget specOf fallback u⟩
  unfold c2FmtGhost
  split
  · split
    · split
      · rename_i hRun
        exact (Classical.choose_spec hRun).2.2.2.2.1
      · exact hFr
    · exact hFr
  · exact ExecFrozen.of_perm_eq hFr (congrFun (hFallbackPerm u))

/-! ### `ActiveC2FmtRun` Dischargers for `lsFmtWriteSym` & `lsFormatInnerSym` -/

private theorem withExecFrozenBudget_pool {M : LibsignalBinary.Heap.AllocCostModel}
    (A : LibsignalBinary.Heap.RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    (withExecFrozenBudget A).pool lim st s =
      A.pool lim st s ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝ := rfl

private theorem sep_insert_pool_pure (A B C D P E R : SepProp) :
    P ∗ ((A ∗ B ∗ C ∗ D ∗ E) ∗ R) = (A ∗ B ∗ C ∗ (D ∗ P) ∗ E) ∗ R := by
  sep_ac_rfl

section FmtWriteRun

attribute [local irreducible]
  cliElfBytes c2MplAllocCli c2CoreFmtMpl c2CoreMpl c2FmtWriteAddr
  cliFmtWriteRoGuard fineCostModel fineHookRustCliAllocBudget nonZeroEquivLim withExecFrozenBudget
  dotTplBytes CryptoVerification.RustHeap.vecU8At CryptoVerification.RustHeap.vecU8
  VerifiedLibraries.RustStd.fmtArgumentsAt CliFmtWriteProtoAddrCall.clientSep

private theorem fmtWrite_pre_sub [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFmtWriteProtoAddrCall) (st0 : fineCostModel.σ) (R : SepProp)
    {s0 : State}
    (hFr0 : ExecFrozen s0.mem)
    (hRo0 : cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl s0.mem)
    (hpre : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R) :
    (s0.setPC c2FmtWriteAddr).mem ⊨
      (withRoMemGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs)))).pre (c, st0) (s0.setPC c2FmtWriteAddr) ∗ R := by
  have hm_s1 : (s0.setPC c2FmtWriteAddr).mem = s0.mem := setPC_mem s0 c2FmtWriteAddr
  have hpre_s1 : (s0.setPC c2FmtWriteAddr).mem ⊨
      (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) (s0.setPC c2FmtWriteAddr) ∗ R := by
    rw [hm_s1, fmtWriteGhostSpecOf_pre_setPC mmpl brkStart lim γ tp (c, st0) s0 c2FmtWriteAddr]
    exact hpre
  have hpre_in1 := (extract_withLsRetFmtWrite hpre_s1).2
  dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpre_in1 ⊢
  rw [withExecFrozenBudget_repAlloc, withExecFrozenBudget_pool]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_in1 ⊢
  refine ⟨hm_s1.symm ▸ hRo0, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  rcases hpre_in1 with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, hEx⟩, hm0⟩
  refine ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen,
    (fitsEnv_nonZeroEquivLim fineCostModel lim st0 _).symm ▸ hFit, hEx⟩, ?_⟩
  rw [fineHookPool_nonZeroEquivLim γ mmpl tp brkStart lim st0 (s0.setPC c2FmtWriteAddr)]
  have hFr1 : ExecFrozen (s0.setPC c2FmtWriteAddr).mem := hm_s1.symm ▸ hFr0
  have hm0_fr : (s0.setPC c2FmtWriteAddr).mem ⊨
      ⌜nonZeroEquivLim lim ≠ zeroBudgetLimits → ExecFrozen (s0.setPC c2FmtWriteAddr).mem⌝ ∗
      ((CryptoVerification.RustHeap.vecU8At
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc c.v c.cap0 c.ptr0 c.bs ∗
        VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x2 c.x3
          dotTplBytes c.args ∗
        c.clientSep ∗
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st0 (s0.setPC c2FmtWriteAddr) ∗
        stackAt (s0.setPC c2FmtWriteAddr).sp
          CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨fun _ => hFr1, hm0⟩
  exact Satisfies.mono (Entails.of_eq (sep_insert_pool_pure _ _ _ _ _ _ _)) hm0_fr

private theorem fmtWrite_hout_s0 [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (c : CliFmtWriteProtoAddrCall) (st0 : fineCostModel.σ) (R : SepProp)
    {s0 sf : State}
    (hout_sub : SubroutineOutcome
      (withRoMemGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
        (withFsTraceExact (cliFmtWriteProtoAddrSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs))))
      (c, st0) R (s0.setPC c2FmtWriteAddr) sf) :
    SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.oracle = s0.oracle := by
  rcases hout_sub with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpost1
    rw [withExecFrozenBudget_repAlloc] at hpost1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfs, htr⟩, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨evs, hp⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp
    rcases hp with ⟨bs', hp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hw0, hacp1, hfs', htr', hEnv⟩, hm_f⟩
    rw [withExecFrozenBudget_pool,
      fineHookPool_nonZeroEquivLim γ mmpl tp brkStart lim _ sf] at hm_f
    have hm_drop : sf.mem ⊨
        (CryptoVerification.RustHeap.vecU8
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc c.v bs' ∗
          VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x2 c.x3
            dotTplBytes c.args ∗
          c.clientSep ∗
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim
            (fineCostModel.stepEvents evs st0) sf ∗
          stackAt (s0.setPC c2FmtWriteAddr).sp
            CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R := by
      have hm1 : sf.mem ⊨
          ⌜nonZeroEquivLim lim ≠ zeroBudgetLimits → ExecFrozen sf.mem⌝ ∗
          ((CryptoVerification.RustHeap.vecU8
              (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc c.v bs' ∗
            VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x2 c.x3
              dotTplBytes c.args ∗
            c.clientSep ∗
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim
              (fineCostModel.stepEvents evs st0) sf ∗
            stackAt (s0.setPC c2FmtWriteAddr).sp
              CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R) :=
        Satisfies.mono (Entails.of_eq (sep_insert_pool_pure _ _ _ _ _ _ _).symm) hm_f
      rw [satisfies_pure_sepConj] at hm1
      exact hm1.2
    have hacp0 : LibsignalBinary.Heap.AllocCallPreserved s0 sf :=
      allocCallPreserved_of_setPC hacp1
    have hout1 : SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R
        (s0.setPC c2FmtWriteAddr) sf := by
      refine Or.inl ⟨hret1, hcc1, ?_⟩
      dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfs, htr⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨bs', ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hw0, hacp1, hfs', htr', hEnv⟩, hm_drop⟩
    exact ⟨fmtWriteGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp (c, st0) R s0 sf
      c2FmtWriteAddr hout1,
      hfs.trans (setPC_fs s0 c2FmtWriteAddr),
      htr.trans (setPC_trace s0 c2FmtWriteAddr),
      hacp0.2.2.2.2.2.1⟩
  · dsimp only [withRoMemGuard, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withRoMemGuard, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem single_fmtWrite_run [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) s0)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFmtWriteProtoAddrCall × fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre x s0 ∗ R) :
    ∃ sf : State,
      StepsUntil c2FmtProg (SubroutineStop s0) (s0.setPC c2FmtWriteAddr) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      sf.oracle = s0.oracle ∧
      SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) x R s0 sf := by
  rcases hImg with ⟨hFr0, hRo0, hCL0⟩
  obtain ⟨hRet, _⟩ := extract_withLsRetFmtWrite hpre
  rcases x with ⟨c, st0⟩
  have hlim' : nonZeroEquivLim lim ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  have hL := c2_fmtWriteSubLink hLs mmpl hMm γ tp brkStart hlim' hRet
  have hSubOk := cliCoreFmtWrite_protoAddr_ro_ok
    (EnvOf := fun c0 => ExactOrNilEnv c0.exactEvs) hL
  have hEntryEq : c2FmtWriteAddr = coreMultiLib.fnAddr c2CoreMpl coreFmtWriteSym :=
    (c2_resolve_fmtWrite_eq hLs).symm.trans (c2_resolve_fmtWrite_fnAddr hLs)
  have hm_s1 : (s0.setPC c2FmtWriteAddr).mem = s0.mem := setPC_mem s0 c2FmtWriteAddr
  have hCL_trap : (c2FmtProgTrap (s0.readReg64 .lr)).CodeLoaded (s0.setPC c2FmtWriteAddr).mem :=
    (c2FmtProgTrap_codeLoaded_iff _ (s0.setPC c2FmtWriteAddr).mem).mpr (hm_s1.symm ▸ hCL0)
  obtain ⟨sf, hsteps_trap, hout_sub⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome hSubOk (c, st0) R (s0.setPC c2FmtWriteAddr)
      ((State.pc_setPC s0 c2FmtWriteAddr).trans hEntryEq)
      ((setPC_status s0 c2FmtWriteAddr).trans hrun)
      (fmtWrite_pre_sub mmpl brkStart lim γ tp c st0 R hFr0 hRo0 hpre)
      ((setPC_spAligned s0 c2FmtWriteAddr).trans hsp)
      hCL_trap
  have hout_s0 := fmtWrite_hout_s0 mmpl brkStart lim γ tp c st0 R hout_sub
  obtain ⟨hstop, hnhalt, hnoex⟩ := subroutineStop_of_outcome hout_s0.1
  have huntil := stepsUntil_c2FmtProg_of_trap hsteps_trap hstop hnhalt hnoex
  exact ⟨sf, huntil, hstop, hout_s0.2.1, hout_s0.2.2.1, hout_s0.2.2.2, hout_s0.1⟩

section
attribute [local irreducible] fmtWriteGhostSpecOf

private theorem activeC2FmtRun_fmtWrite [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) s0)
    (hAct : ActiveC2FmtPre (fmtWriteGhostSpecOf mmpl brkStart lim) s0) :
    ActiveC2FmtRun c2FmtWriteAddr (fmtWriteGhostSpecOf mmpl brkStart lim) s0 := by
  rcases hAct with ⟨hrun, hspMod, γ₀, tp₀, x₀, R₀, hpre₀⟩
  have hsp : s0.spAligned = true := (sp_mod16_iff_spAligned s0).mp hspMod
  obtain ⟨sf, huntil, hstop, hfs, htr, horc, _⟩ :=
    single_fmtWrite_run mmpl hMm hLs brkStart lim hImg hrun hsp γ₀ tp₀ x₀ R₀ hpre₀
  have hsteps := huntil.toSteps
  have hkf : s0.mem.KeepsFrozen sf.mem := by
    have h0 := hsteps.keepsFrozen
    rwa [setPC_mem] at h0
  have hsym : sf.symtab = s0.symtab := by
    have h0 := hsteps.symtab_eq
    rwa [setPC_symtab] at h0
  have hfr_sf : ExecFrozen sf.mem :=
    steps_c2FmtProg_preserves_execFrozen hsteps ((setPC_mem s0 c2FmtWriteAddr).symm ▸ hImg.1)
  refine ⟨sf, huntil, hkf, horc, hsym, hfr_sf, hfs, htr, ?_⟩
  intro γ tp x R hpre
  obtain ⟨sf', huntil', hstop', _, _, _, hout'⟩ :=
    single_fmtWrite_run mmpl hMm hLs brkStart lim hImg hrun hsp γ tp x R hpre
  have hdet : sf = sf' := h2fsgen_stepsUntil_det huntil hstop huntil' hstop'
  rwa [hdet]

end
end FmtWriteRun

private theorem fi_withExecFrozenBudget_pool {M} (A : LibsignalBinary.Heap.RustCliAllocBudget M)
    (lim0 : BudgetLimits) (st : M.σ) (s : State) :
    (withExecFrozenBudget A).pool lim0 st s =
      (A.pool lim0 st s ∗ ⌜lim0 ≠ zeroBudgetLimits → ExecFrozen s.mem⌝) :=
  rfl

private theorem fi_setPC_mem (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := by
  cases s; rfl

private theorem fi_setPC_fs (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by
  cases s; rfl

private theorem fi_setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by
  cases s; rfl

private theorem fi_setPC_status (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := by
  cases s; rfl

private theorem fi_setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by
  cases s; rfl

private theorem fi_setPC_symtab (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

private theorem fi_allocCallPreserved_setPC {s0 sf : State} {pc : BitVec 64}
    (h : LibsignalBinary.Heap.AllocCallPreserved (s0.setPC pc) sf) :
    LibsignalBinary.Heap.AllocCallPreserved s0 sf := by
  cases s0; cases sf; exact h

section FormatInnerRun
attribute [local irreducible] cliElfBytes c2AllocMpl c2CoreFmtMpl c2CoreMpl
  cliFormatInnerRoGuard c2FormatInnerAddr
  withExecFrozenBudget fineHookRustCliAllocBudget nonZeroEquivLim
  CryptoVerification.RustHeap.vecU8
  VerifiedLibraries.RustStd.fmtArgumentsAt
  CliFormatInnerLsCall.clientSep CliFormatInnerLsCall.shapePreOk
  fineCostModel

private theorem single_formatInner_run [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) s0)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFormatInnerLsCall × fineCostModel.σ) (R : SepProp)
    (hpre : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre x s0 ∗ R) :
    ∃ sf : State,
      StepsUntil c2FmtProg (SubroutineStop s0) (s0.setPC c2FormatInnerAddr) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      sf.oracle = s0.oracle ∧
      SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) x R s0 sf := by
  rcases hImg with ⟨hFr0, hRo0, hCL0⟩
  obtain ⟨hRet, _⟩ := extract_withLsRetFormatInner hpre
  rcases x with ⟨c, st0⟩
  have hlim' : nonZeroEquivLim lim ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  have hL := c2_formatInnerSubLink hLs mmpl hMm γ tp brkStart hlim' hRet
  have hSubOk := cliAllocFormatInner_lsCall_ro_ok
    (EnvOf := fun c0 => ExactOrNilEnv c0.exactEvs) hL
  have hEntryEq : c2FormatInnerAddr = allocMultiLib.fnAddr c2AllocMpl allocFormatInnerSym :=
    (c2_resolve_formatInner_eq hLs).symm.trans (c2_resolve_formatInner_fnAddr hLs)
  have hm_s1 : (s0.setPC c2FormatInnerAddr).mem = s0.mem := fi_setPC_mem s0 c2FormatInnerAddr
  have hfs_s1 : (s0.setPC c2FormatInnerAddr).fs = s0.fs := fi_setPC_fs s0 c2FormatInnerAddr
  have htr_s1 : (s0.setPC c2FormatInnerAddr).trace = s0.trace := fi_setPC_trace s0 c2FormatInnerAddr
  have hpre_sub : (s0.setPC c2FormatInnerAddr).mem ⊨
      (withRoMemGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl)
        (withFsTraceExact (cliFormatInnerLsCallSpec fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
          (nonZeroEquivLim lim)
          (fun c0 => ExactOrNilEnv c0.exactEvs)))).pre (c, st0) (s0.setPC c2FormatInnerAddr) ∗ R := by
    have hpre_s1 : (s0.setPC c2FormatInnerAddr).mem ⊨
        (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) (s0.setPC c2FormatInnerAddr) ∗ R := by
      rw [hm_s1, formatInnerGhostSpecOf_pre_setPC mmpl brkStart lim γ tp (c, st0) s0 c2FormatInnerAddr]
      exact hpre
    have hpre_in1 := (extract_withLsRetFormatInner hpre_s1).2
    dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpre_in1 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_in1 ⊢
    refine ⟨hm_s1.symm ▸ hRo0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    rcases hpre_in1 with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
    refine ⟨⟨hx8, hx0, hx1, hshOk,
      (fitsEnv_nonZeroEquivLim fineCostModel lim st0 _).symm ▸ hFit, hEx⟩, ?_⟩
    rw [fi_withExecFrozenBudget_pool,
      fineHookPool_nonZeroEquivLim γ mmpl tp brkStart lim st0 (s0.setPC c2FormatInnerAddr)]
    have hFr1 : ExecFrozen (s0.setPC c2FormatInnerAddr).mem := hm_s1.symm ▸ hFr0
    have hAdd : ∀ {P Q : SepProp},
        ((s0.setPC c2FormatInnerAddr).mem ⊨ P) →
        (⌜nonZeroEquivLim lim ≠ zeroBudgetLimits → ExecFrozen (s0.setPC c2FormatInnerAddr).mem⌝ ∗ P) = Q →
        ((s0.setPC c2FormatInnerAddr).mem ⊨ Q) := by
      intro P Q hp heq; rw [← heq, satisfies_pure_sepConj]; exact ⟨fun _ => hFr1, hp⟩
    exact hAdd hm0 (by sep_ac_rfl)
  have hCL_trap : (c2FmtProgTrap (s0.readReg64 .lr)).CodeLoaded (s0.setPC c2FormatInnerAddr).mem :=
    (c2FmtProgTrap_codeLoaded_iff _ (s0.setPC c2FormatInnerAddr).mem).mpr (hm_s1.symm ▸ hCL0)
  obtain ⟨sf, hsteps_trap, hout_sub⟩ :=
    subroutine_ok_elim_steps_outcome hSubOk (c, st0) R (s0.setPC c2FormatInnerAddr)
      ((State.pc_setPC s0 c2FormatInnerAddr).trans hEntryEq)
      ((fi_setPC_status s0 c2FormatInnerAddr).trans hrun)
      hpre_sub
      ((fi_setPC_spAligned s0 c2FormatInnerAddr).trans hsp)
      hCL_trap
  have hout_s0 : SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0 sf ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.oracle = s0.oracle := by
    rcases hout_sub with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpost1
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hfs, htr⟩, hp⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hp
      rcases hp with ⟨evs, hp⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hp
      rcases hp with ⟨bs', hp⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp with ⟨⟨hacp1, hfs', htr', hEnv⟩, hm_f⟩
      rw [withExecFrozenBudget_repAlloc (fineHookRustCliAllocBudget γ mmpl tp brkStart),
        fi_withExecFrozenBudget_pool,
        fineHookPool_nonZeroEquivLim γ mmpl tp brkStart lim _ sf] at hm_f
      have hm_drop : sf.mem ⊨
          (CryptoVerification.RustHeap.vecU8
              (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc c.ret bs' ∗
            VerifiedLibraries.RustStd.fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
            c.clientSep ∗
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim
              (fineCostModel.stepEvents evs st0) sf ∗
            stackAt (s0.setPC c2FormatInnerAddr).sp
              CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R := by
        have hDrop : ∀ {P Q : SepProp},
            (sf.mem ⊨ P) →
            P = (⌜nonZeroEquivLim lim ≠ zeroBudgetLimits → ExecFrozen sf.mem⌝ ∗ Q) →
            (sf.mem ⊨ Q) := by
          intro P Q hp heq; rw [heq, satisfies_pure_sepConj] at hp; exact hp.2
        exact hDrop hm_f (by sep_ac_rfl)
      have hacp0 : LibsignalBinary.Heap.AllocCallPreserved s0 sf :=
        fi_allocCallPreserved_setPC hacp1
      have hout1 : SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R
          (s0.setPC c2FormatInnerAddr) sf := by
        refine Or.inl ⟨hret1, hcc1, ?_⟩
        dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
          cliFormatInnerLsCallSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hfs, htr⟩, ?_⟩
        rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs, ?_⟩
        rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨bs', ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hacp1, hfs', htr', hEnv⟩, hm_drop⟩
      exact ⟨formatInnerGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp (c, st0) R s0 sf
        c2FormatInnerAddr hout1, hfs.trans hfs_s1, htr.trans htr_s1, hacp0.2.2.2.2.2.1⟩
    · dsimp only [withRoMemGuard, withFsTraceExact, cliFormatInnerLsCallSpec] at hpan
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
      have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
    · dsimp only [withRoMemGuard, withFsTraceExact] at hex
      rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
    · dsimp only [withRoMemGuard, withFsTraceExact] at hoom
      rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1
  obtain ⟨hstop, hnhalt, hnoex⟩ := subroutineStop_of_outcome hout_s0.1
  have huntil := stepsUntil_c2FmtProg_of_trap hsteps_trap hstop hnhalt hnoex
  exact ⟨sf, huntil, hstop, hout_s0.2.1, hout_s0.2.2.1, hout_s0.2.2.2, hout_s0.1⟩

section
attribute [local irreducible] formatInnerGhostSpecOf

private theorem activeC2FmtRun_formatInner [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) s0)
    (hAct : ActiveC2FmtPre (formatInnerGhostSpecOf mmpl brkStart lim) s0) :
    ActiveC2FmtRun c2FormatInnerAddr (formatInnerGhostSpecOf mmpl brkStart lim) s0 := by
  rcases hAct with ⟨hrun, hspMod, γ₀, tp₀, x₀, R₀, hpre₀⟩
  have hsp : s0.spAligned = true := (sp_mod16_iff_spAligned s0).mp hspMod
  obtain ⟨sf, huntil, hstop, hfs, htr, horc, _⟩ :=
    single_formatInner_run mmpl hMm hLs brkStart lim hImg hrun hsp γ₀ tp₀ x₀ R₀ hpre₀
  have hsteps := huntil.toSteps
  have hkf : s0.mem.KeepsFrozen sf.mem := by
    have h0 := hsteps.keepsFrozen
    rwa [fi_setPC_mem] at h0
  have hsym : sf.symtab = s0.symtab := by
    have h0 := hsteps.symtab_eq
    rwa [fi_setPC_symtab] at h0
  have hfr_sf : ExecFrozen sf.mem :=
    steps_c2FmtProg_preserves_execFrozen hsteps ((fi_setPC_mem s0 c2FormatInnerAddr).symm ▸ hImg.1)
  refine ⟨sf, huntil, hkf, horc, hsym, hfr_sf, hfs, htr, ?_⟩
  intro γ tp x R hpre
  obtain ⟨sf', huntil', hstop', _, _, _, hout'⟩ :=
    single_formatInner_run mmpl hMm hLs brkStart lim hImg hrun hsp γ tp x R hpre
  have hdet : sf = sf' := h2fsgen_stepsUntil_det huntil hstop huntil' hstop'
  rwa [hdet]

end
end FormatInnerRun

/-! ## 6. Concrete `c2FmtWriteGhost` & `c2FormatInnerGhost` Exports -/

/-- Concrete 0-hook stock-ELF ghost hook for `lsFmtWriteSym` (`core::fmt::write`). -/
@[expose] noncomputable def c2FmtWriteGhost [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  c2FmtGhost
    (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl)
    c2FmtWriteAddr
    (fmtWriteGhostSpecOf mmpl brkStart lim)
    fmtWriteHook0

/-- Concrete 0-hook stock-ELF ghost hook for `lsFormatInnerSym` (`alloc::fmt::format::format_inner`). -/
@[expose] noncomputable def c2FormatInnerGhost [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  c2FmtGhost
    (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl)
    c2FormatInnerAddr
    (formatInnerGhostSpecOf mmpl brkStart lim)
    formatInnerHook0

theorem c2_fmtWriteGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsFmtWriteSym (c2FmtWriteGhost mmpl brkStart lim) where
  fs_eq := c2FmtGhost_fs _ _ _ _
  fsT := c2FmtGhost_fsT _ _ _ _
  rowSpec := by dsimp [ExtraRowSpec]; exact trivial

theorem c2_formatInnerGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsFormatInnerSym (c2FormatInnerGhost mmpl brkStart lim) where
  fs_eq := c2FmtGhost_fs _ _ _ _
  fsT := c2FmtGhost_fsT _ _ _ _
  rowSpec := by dsimp [ExtraRowSpec]; exact trivial

theorem c2_fmtWriteGhost_noAllocFailed [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookNoAllocFailed (c2FmtWriteGhost mmpl brkStart lim) :=
  c2FmtGhost_noAllocFailed _ _ _ _

theorem c2_formatInnerGhost_noAllocFailed [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookNoAllocFailed (c2FormatInnerGhost mmpl brkStart lim) :=
  c2FmtGhost_noAllocFailed _ _ _ _

theorem c2_fmtWriteGhost_ok [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (c2FmtWriteGhost mmpl brkStart lim)
      (fmtWriteProtoAddrCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) := by
  classical
  rintro x R s0 hrun hpre hsp
  obtain ⟨hRet, hpreInner⟩ := extract_withLsRetFmtWrite hpre
  rcases x with ⟨c, st0⟩
  dsimp only [cliFmtWriteProtoAddrSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R := by
    refine intro_withLsRetFmtWrite hRet ?_
    dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen,
      fitsEnv_exactOrNil hFit hEx, exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  have hGhostSpec :
      s0.mem.KeepsFrozen (c2FmtWriteGhost mmpl brkStart lim s0).mem ∧
      (c2FmtWriteGhost mmpl brkStart lim s0).symtab = s0.symtab ∧
      SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0
        (c2FmtWriteGhost mmpl brkStart lim s0) := by
    unfold c2FmtWriteGhost c2FmtGhost
    by_cases hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) s0
    · have hAct : ActiveC2FmtPre (fmtWriteGhostSpecOf mmpl brkStart lim) s0 :=
        ⟨hrun, (sp_mod16_iff_spAligned s0).mpr hsp, γ, tp, (c, st0), R, hpre0⟩
      have hRun := activeC2FmtRun_fmtWrite mmpl hMm hLsLsmpl brkStart lim hImg hAct
      simp only [hImg, hAct, hRun, ↓reduceIte, ↓reduceDIte]
      have hspec := Classical.choose_spec hRun
      exact ⟨hspec.2.1, hspec.2.2.2.1, hspec.2.2.2.2.2.2.2 γ tp (c, st0) R hpre0⟩
    · simp only [hImg, ↓reduceIte]
      have hFallback : HookOk (keepFsTrace fmtWriteHook0)
          (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) :=
        hookOk_withLsRetFmtWrite
          (fmtWriteHook0_cliProtoAddr_ok fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (fun c0 => exactOrNilEnv_nil c0.exactEvs))
      exact hFallback (c, st0) R s0 hrun hpre0 hsp
  obtain ⟨hkf, hsym, hout⟩ := hGhostSpec
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
      at hpost
    dsimp only [fmtWriteProtoAddrCliLsSpec,
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs.fmtWriteProtoAddrLsEnvSpec,
      withLsRetFmtWrite, cliFmtWriteProtoAddrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1,
      exactOrNilEnv_imp cliFmtWriteEnv_nil hEx evs hp.1.2.2.2.2⟩, hp.2⟩
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact,
      cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem c2_formatInnerGhost_ok [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (c2FormatInnerGhost mmpl brkStart lim)
      (formatInnerCallCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) := by
  classical
  rintro x R s0 hrun hpre hsp
  obtain ⟨hRet, hpreInner⟩ := extract_withLsRetFormatInner hpre
  rcases x with ⟨c, st0⟩
  dsimp only [cliFormatInnerLsCallSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R := by
    refine intro_withLsRetFormatInner hRet ?_
    dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hshOk,
      fitsEnv_exactOrNil hFit hEx, exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  have hGhostSpec :
      s0.mem.KeepsFrozen (c2FormatInnerGhost mmpl brkStart lim s0).mem ∧
      (c2FormatInnerGhost mmpl brkStart lim s0).symtab = s0.symtab ∧
      SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) (c, st0) R s0
        (c2FormatInnerGhost mmpl brkStart lim s0) := by
    unfold c2FormatInnerGhost c2FmtGhost
    by_cases hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) s0
    · have hAct : ActiveC2FmtPre (formatInnerGhostSpecOf mmpl brkStart lim) s0 :=
        ⟨hrun, (sp_mod16_iff_spAligned s0).mpr hsp, γ, tp, (c, st0), R, hpre0⟩
      have hRun := activeC2FmtRun_formatInner mmpl hMm hLsLsmpl brkStart lim hImg hAct
      simp only [hImg, hAct, hRun, ↓reduceIte, ↓reduceDIte]
      have hspec := Classical.choose_spec hRun
      exact ⟨hspec.2.1, hspec.2.2.2.1, hspec.2.2.2.2.2.2.2 γ tp (c, st0) R hpre0⟩
    · simp only [hImg, ↓reduceIte]
      have hFallback : HookOk (keepFsTrace formatInnerHook0)
          (formatInnerGhostSpecOf mmpl brkStart lim γ tp) :=
        hookOk_withLsRetFormatInner
          (formatInnerHook0_cliLsCallSpec_ok fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (fun c0 => exactOrNilEnv_nil c0.exactEvs))
      exact hFallback (c, st0) R s0 hrun hpre0 hsp
  obtain ⟨hkf, hsym, hout⟩ := hGhostSpec
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec] at hpost
    dsimp only [formatInnerCallCliLsSpec,
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs.formatInnerCallLsEnvSpec,
      withLsRetFormatInner, cliFormatInnerLsCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1,
      exactOrNilEnv_imp cliFormatInnerEnv_nil hEx evs hp.1.2.2.2⟩, hp.2⟩
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem c2_fmtWriteGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsFmtWriteSym (guardOf lsFmtWriteSym)
      (c2FmtWriteGhost mmpl brkStart lim) := by
  classical
  refine ⟨c2_fmtWriteGhost_rowSpecOk mmpl brkStart lim, ?_⟩
  refine
    { preserves_execFrozen := fun u _ _ hFr =>
        c2FmtGhost_preserves_execFrozen _ _ _ (fallback := fmtWriteHook0) (fun _ => rfl) hFr
      replay_at_stub := ?_ }
  intro W s0 sf _ _ _ _ _ _ _
  right
  have hResEq : libsignalSessionLib.resolve lsmpl lsFmtWriteSym = c2FmtWriteAddr :=
    c2_resolve_fmtWrite_eq hLs
  have hStubNone :
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve lsmpl lsFmtWriteSym) = none := by
    rw [hResEq, ← c2FmtProg_externAt_eq_real hLs mmpl W c2FmtWriteAddr]
    exact c2FmtProg_externAt_none_of_not_panic (by decide)
  refine ⟨hStubNone, ?_⟩
  intro u _ _ hpc hrun hnoex_fu hkf hfr ⟨hInv, hPfs⟩
  have hImg : c2FmtImgGuard (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) u :=
    ⟨hfr, c2_cliFmtWriteRoGuard hLs hInv, c2FmtProg_codeLoaded_of_f3CodeInv hLs hInv⟩
  have hfu_fs := c2FmtGhost_fs
    (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) c2FmtWriteAddr
    (fmtWriteGhostSpecOf mmpl brkStart lim) fmtWriteHook0 u
  have hInv_fu : F3CodeInv lsmpl mmpl (c2FmtWriteGhost mmpl brkStart lim u).mem ∧
      PredFs (c2FmtWriteGhost mmpl brkStart lim u).fs :=
    f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u _ ⟨hInv, hPfs⟩ hkf hfu_fs
  have hfr_fu :=
    (c2FmtGhost_preserves_execFrozen
      (cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl) c2FmtWriteAddr
      (fmtWriteGhostSpecOf mmpl brkStart lim) (fallback := fmtWriteHook0) (fun _ => rfl) hfr).1
  refine ⟨?_, hfr_fu, hInv_fu⟩
  have hAct : ActiveC2FmtPre (fmtWriteGhostSpecOf mmpl brkStart lim) u := by
    by_contra hNotAct
    apply hnoex_fu "c2FmtGhost: inactive precondition"
    unfold c2FmtWriteGhost c2FmtGhost
    simp [hImg, hNotAct]
  have hRun : ActiveC2FmtRun c2FmtWriteAddr (fmtWriteGhostSpecOf mmpl brkStart lim) u :=
    activeC2FmtRun_fmtWrite mmpl hMm hLs brkStart lim hImg hAct
  have hfu_eq : c2FmtWriteGhost mmpl brkStart lim u = Classical.choose hRun := by
    unfold c2FmtWriteGhost c2FmtGhost
    simp [hImg, hAct, hRun]
  have hsteps_c2 : Steps c2FmtProg (u.setPC c2FmtWriteAddr) (Classical.choose hRun) :=
    (Classical.choose_spec hRun).1.toSteps
  have hsetPC_u : u.setPC c2FmtWriteAddr = u := setPC_of_pc_eq (hpc.trans hResEq)
  rw [← hfu_eq, hsetPC_u] at hsteps_c2
  exact steps_c2FmtProg_to_real hLs mmpl W hsteps_c2

theorem c2_formatInnerGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsFormatInnerSym (guardOf lsFormatInnerSym)
      (c2FormatInnerGhost mmpl brkStart lim) := by
  classical
  have hFallbackPerm : ∀ s : State, (formatInnerHook0 s).mem.perm = s.mem.perm :=
    fun s => perm_writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64
  refine ⟨c2_formatInnerGhost_rowSpecOk mmpl brkStart lim, ?_⟩
  refine
    { preserves_execFrozen := fun u _ _ hFr =>
        c2FmtGhost_preserves_execFrozen _ _ _ hFallbackPerm hFr
      replay_at_stub := ?_ }
  intro W s0 sf _ _ _ _ _ _ _
  right
  have hResEq : libsignalSessionLib.resolve lsmpl lsFormatInnerSym = c2FormatInnerAddr :=
    c2_resolve_formatInner_eq hLs
  have hStubNone :
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve lsmpl lsFormatInnerSym) = none := by
    rw [hResEq, ← c2FmtProg_externAt_eq_real hLs mmpl W c2FormatInnerAddr]
    exact c2FmtProg_externAt_none_of_not_panic (by decide)
  refine ⟨hStubNone, ?_⟩
  intro u _ _ hpc hrun hnoex_fu hkf hfr ⟨hInv, hPfs⟩
  have hImg : c2FmtImgGuard (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) u :=
    ⟨hfr, c2_cliFormatInnerRoGuard hLs hInv, c2FmtProg_codeLoaded_of_f3CodeInv hLs hInv⟩
  have hfu_fs := c2FmtGhost_fs
    (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) c2FormatInnerAddr
    (formatInnerGhostSpecOf mmpl brkStart lim) formatInnerHook0 u
  have hInv_fu : F3CodeInv lsmpl mmpl (c2FormatInnerGhost mmpl brkStart lim u).mem ∧
      PredFs (c2FormatInnerGhost mmpl brkStart lim u).fs :=
    f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u _ ⟨hInv, hPfs⟩ hkf hfu_fs
  have hfr_fu :=
    (c2FmtGhost_preserves_execFrozen
      (cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl) c2FormatInnerAddr
      (formatInnerGhostSpecOf mmpl brkStart lim) hFallbackPerm hfr).1
  refine ⟨?_, hfr_fu, hInv_fu⟩
  have hAct : ActiveC2FmtPre (formatInnerGhostSpecOf mmpl brkStart lim) u := by
    by_contra hNotAct
    apply hnoex_fu "c2FmtGhost: inactive precondition"
    unfold c2FormatInnerGhost c2FmtGhost
    simp [hImg, hNotAct]
  have hRun : ActiveC2FmtRun c2FormatInnerAddr (formatInnerGhostSpecOf mmpl brkStart lim) u :=
    activeC2FmtRun_formatInner mmpl hMm hLs brkStart lim hImg hAct
  have hfu_eq : c2FormatInnerGhost mmpl brkStart lim u = Classical.choose hRun := by
    unfold c2FormatInnerGhost c2FmtGhost
    simp [hImg, hAct, hRun]
  have hsteps_c2 : Steps c2FmtProg (u.setPC c2FormatInnerAddr) (Classical.choose hRun) :=
    (Classical.choose_spec hRun).1.toSteps
  have hsetPC_u : u.setPC c2FormatInnerAddr = u :=
    (show ∀ (s : State) (pc : BitVec 64), s.pc = pc → s.setPC pc = s from
      fun s pc h => by cases s; dsimp only at h; subst h; rfl) u c2FormatInnerAddr (hpc.trans hResEq)
  rw [← hfu_eq, hsetPC_u] at hsteps_c2
  exact steps_c2FmtProg_to_real hLs mmpl W hsteps_c2

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow
