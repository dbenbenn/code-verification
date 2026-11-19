/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssembleBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble
import LibsignalBinary.Proofs.CodeLayout

/-!
# Budget-Threaded Base Combinators and Destination Assembly for CLI `SegClone`

Threads `RustCliAllocBudget M` and `VmPreserved` across `SepWPpCl`, the `SegCloneHooks` bundle,
frame-remainder helpers, and destination slot assembly (`+0x594 → +0x69c / +0x7e4`) on CLI
Block `463`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto SessionState)
open CryptoVerification (
  LibsignalPlacement lsmpl
  lsRustNoAllocShimSym lsRustAllocSym
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser SessionGhost uuidTryParse sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks96_6QAt)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel errsAt)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  DstVals dstSlotsAt spillSlotsAt
  segClone_dstSlotsMidAt segClone_dstSlotsWrittenAt
  chunks96_6QAt_sp_0xb40 segClone_chunks96_6QAt_sp_0xd38
  pointsTo128_eq_pointsTo64 segClone_version_cond_iff
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAt)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  ls_hook_ok_226 recFramePlaced
)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (
  SepWPpCl
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  TryDecryptEnvArgs segCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  protocolAddressAt_atState signalMessageAt_atState errsAt_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  recordDecryptPlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `SepWPpCl` `VmPreserved` and `A.pool` Transport Combinators -/

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

/-- Lift a `VmPreserved`-producing `SepWP` basic-block segment into `SepWPpCl`. -/
theorem SepWPpCl_of_sepWP_vm [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPpCl prog ret sm Pm Q Qp))) :
    SepWPpCl prog ret s P Q Qp :=
  SepWPpCl.of_sepWP (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

/-- Transport `A.pool lim st s_old` to `A.pool lim st s` in a `SepWPpCl` precondition across a
    `VmPreserved s_old s` transition. -/
theorem SepWPpCl_transport_budgetPool [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {ret : BitVec 64} {s_old s : State} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s_old s)
    (h : SepWPpCl prog ret s (A.pool lim st s ∗ Rest) Q Qp) :
    SepWPpCl prog ret s (A.pool lim st s_old ∗ Rest) Q Qp :=
  SepWPpCl.weaken_pre (sepConj_mono_left (Entails.of_eq (A.pool_transport lim st s_old s hvm).symm)) h

/-- Normalize CLI `recFramePlaced (A.atState lim st s)` into `recFramePlaced A.repAlloc ∗ A.pool`. -/
theorem cliRecFramePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (x : RecordDecryptGhost) (sp : BitVec 64) :
    recFramePlaced (A.atState lim st s) x sp =
      recFramePlaced A.repAlloc x sp ∗ A.pool lim st s := by
  unfold recFramePlaced
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.repAlloc_pool, sepConj_emp]
  simp only [sepConj_assoc]

/-! ## Budget Extern Hooks and No-Panic Helpers -/

structure SegCloneHooks [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec

theorem SegCloneHooks.shim_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
  ls_hook_ok_226 (by decide) hA.shim

theorem SegCloneHooks.alloc_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
  ls_hook_ok_226 (by decide) hA.alloc

theorem SegCloneHooks.allocNoOom_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget hA.alloc_ok

theorem SegCloneHooks.memcpy_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.ρ "memcpy") sessionMemcpyRegionBudgetSpec :=
  ls_hook_ok_226 (by decide) hA.memcpy

abbrev clonePanicPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (recordDecryptPlacedSpec C A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R)

/-! ## Frame Remainder, Reassembly, and Postcondition -/

abbrev segClone_fixedRestPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64) : SepProp :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRestPlaced
    A.repAlloc ctl x sp

theorem segClone_fixedRest_reassemble_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st' : M.σ) (sf : State) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) :
    (spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78 ∗
      chunks96_6QAt (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      memRegion (sp + 0x5f0#64) 104 ∗
      ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
      stackAt sp allocHookStack ∗ A.pool lim st' sf ∗
      segClone_fixedRestPlaced A ctl x sp) ⊢
      (recFramePlaced (A.atState lim st' sf) x sp ∗
        errsAt (A.atState lim st' sf) (sp + 0x5d8#64) [] ∗
        memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest) := by
  have hbase :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest_reassemble_placed
      A.repAlloc ctl x sp sq0 sq1 sq2 sq3 sq4 sq5
      v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78
  rw [RustCliAllocBudget.repAlloc_pool, emp_sepConj] at hbase
  rw [cliRecFramePlaced_atState, errsAt_atState]
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := A.pool lim st' sf) hbase) (Entails.of_eq (by sep_ac_rfl)))
  exact Entails.of_eq (by unfold segClone_fixedRestPlaced; sep_ac_rfl)

@[expose] def segClone_clonePostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_init : M.σ) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧
    (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      let st' := M.stepEvents (segCloneEvents x.G x.st) st_init
      recFramePlaced (A.atState lim st' sf) x s0.sp ∗
      sessionStateAt (A.atState lim st' sf) (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt (A.atState lim st' sf) (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt (A.atState lim st' sf) (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      cliTapeAt ctl x.cur x.rest)

/-! ## Destination Slot Assembly (`+0x594 → +0x69c / +0x7e4`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable CLI Block-`463` first half of destination slot assembly (`+0x594 → +0x620`,
    35 instructions), threading `VmPreserved s s1` and polymorphic in `Qp`. -/
theorem segClone_assemble_1_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (v00 v08 : BitVec 64) (w14 : BitVec 32) (pendPtr' : BitVec 64)
    (w24 w28 w2c sessionVersion previousCounter : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = (blkPl_463).base + 1568#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x8 = w2c.setWidth 64 → s1.readReg64 .x9 = w28.setWidth 64 →
      s1.readReg64 .x10 = previousCounter.setWidth 64 → s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
            scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗ F)
        Q Qp) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
          scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗ F)
      Q Qp := by
  unfold segClone_dstSlotsMidAt spillSlotsAt at hnext
  unfold dstSlotsAt spillSlotsAt
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply sepWPp_of_sepWP_vm (mid := (blkPl_463).base + 1568#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPp.weaken_pre ?_
      (hnext _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close))
    exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable CLI Block-`463` second half of destination slot assembly and version check
    (`+0x620 → +0x69c / +0x7e4`, 31 instructions), threading `VmPreserved s s1` and polymorphic in `Qp`. -/
theorem segClone_assemble_2_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1568#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w2c.setWidth 64) (hx9 : s.readReg64 .x9 = w28.setWidth 64)
    (hx10 : s.readReg64 .x10 = x.st.previousCounter.setWidth 64)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (_hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q Qp := by
  have hver_eq_iff :
      x.st.version.toNat = x.msg.messageVersion.toNat ↔
        (if x.st.sessionVersion = 0 then 2 else x.st.sessionVersion) =
          x.msg.messageVersion.setWidth 32 := by
    unfold SessionState.version
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)]
    · intro h
      have ht := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)] at ht
  have hpc_ver :
      (if (if x.st.sessionVersion = 0 then 2#64 else BitVec.truncate 64 x.st.sessionVersion) =
          BitVec.zeroExtend 64 x.msg.messageVersion then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) =
      (if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) := by
    simp only [segClone_version_cond_iff, ← hver_eq_iff]
  unfold segClone_dstSlotsWrittenAt spillSlotsAt at hnext
  unfold segClone_dstSlotsMidAt spillSlotsAt
  simp only [sepConj_assoc] at hnext ⊢
  apply sepWPp_of_sepWP_vm
    (mid := if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simpa using hpc_ver) (by exact hrun)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPp.weaken_pre ?_
      (hnext _ hvm (by simpa using hpc_ver) (by exact hrun) rfl hsp rfl rfl (by segCloneAssemble_close))
    exact Entails.of_eq (by sep_ac_rfl)

theorem segClone_fields_10_to_11_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q Qp := by
  refine segClone_assemble_1_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08 w14 pendPtr' w24 w28 w2c
    x.st.sessionVersion x.st.previousCounter
    (((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
    hpc hrun hsp hx24 hx28 htr
    fun s1 hvm1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := segClone_dstSlotsMidAt s1.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
            scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          spillSlotsAt s1.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_assemble_2_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr'
    w24 w28 w2c w288 w28c
    (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx10_1
    (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by reg_chain) hx24_1
    (by reg_chain) (by reg_chain) (by reg_chain) htr1
    fun s2 hvm2 hpc2 hrun2 hsp2 hspA2 hx9_2 hx29_2 htr2 => ?_
  rw [hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s2 (hvm1.trans hvm2) hpc2 hrun2 (by reg_chain) hspA2 hx9_2 (by reg_chain) htr2)

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
