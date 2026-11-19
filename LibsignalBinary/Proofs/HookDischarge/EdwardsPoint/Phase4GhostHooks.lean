/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import VerifiedLibraries.Common.Spec.Curve25519
-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliProcess
-- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.Bridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
import ProofLib.Hoare.Model
import ProofLib.Hoare.LibcHooks
import ProofLib.Process.FsLemmas
import ProofLib.Process.OracleEq
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk

/-! # `linkedCallHookG` Ghost Hooks, Consumer `HookOk`, and `GhostRowReplayOn` -/
set_option autoImplicit false
public section
namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj (MultiPlacedLib MultiPlacement Placement PlacedLib HoldsBytes)
open ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open VerifiedLibraries.Common (EdPoint EdExtPoint p25519 edOrderL edZero edSmul edExtZero edExtToAffine)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks libsignalSessionLib cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.Slots (lsScalarModSymCli lsScalarWideSymCli
  lsToEdwardsSymCli lsCompressSymCli lsTorsionFreeSymCli lsDsmbSymCli)
open CryptoVerification.SignalSession.CliExt (withStack pureByteFunctionSpec inputAfter)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FdsHiFrame PoolPreserved RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved VmPreserved.of_eq)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates withRoDataSep)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen SpecStripSInvariant
  SpecPreservesFsTrace keepFsTrace linkedCallHook satisfies_stripExecOutside stepsUntil_of_stripS_standard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (linkedCallHookG
  linkedCallHookG_eq_of_guard linkedCallHookG_eq_of_not_guard withStateGuard hookOk_linkedCallHookG
  linkedCallHookG_fs linkedCallHookG_fsT linkedCallHookG_activeRealPre_of_noException
  ghostExternReplaysOn_of_linkedCallHookG_liftVis)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (lsRetAddr624_of_noException_via_activeRealPre keepLr_false_of_noException_via_activeRealPre
   specStripSInvariant_withLsRet specPreservesFsTrace_withLsRet hookOk_withLsRet_of_simulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet extract_withLsRet
  withLsRet_pre_setPC withLsRet_outcome_setPC hookOk_withLsRet subroutine_ok_withLsRet
  withLsRet_withVmPreserved withLsRet_frameLeft)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (withAlloc hookOk_withAlloc_of_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowReplayOn)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (DalekBlockOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (fe51_one
  fe51_edwards_d fe51_minus_one fe51_sqrt_m1 sc52_l sc52_rr fe51_edwards_d2 basepoint_order
  odd_multiples_basepoint basepointOrderBytes sc52LBytes sc52RRBytes fe51OneBytes fe51EdwardsDBytes
  fe51EdwardsD2Bytes fe51SqrtM1Bytes fe51MinusOneBytes oddMultiplesBasepointBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
  (scalarFromBytesModOrderSpec scalarFromBytesModOrderWideSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (montToEdwards
  fe51Point4Bounded edExtOfBytes edPointEq edVarBaseMul
  montgomeryPointToEdwardsSpec edwardsPointCompressSpec vartimeDoubleScalarMulBasepointSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree (edwardsPointIsTorsionFreeU32Spec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk (scalar_from_bytes_mod_order_ok
  scalar_from_bytes_mod_order_wide_ok montgomery_point_to_edwards_ok edwards_point_compress_ok
  edwards_point_is_torsion_free_u32_ok vartime_double_scalar_mul_basepoint_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (fe51OneBytes_length
  fe51EdwardsDBytes_length fe51MinusOneBytes_length fe51SqrtM1Bytes_length sc52LBytes_length
  sc52RRBytes_length fe51EdwardsD2Bytes_length basepointOrderBytes_length
  oddMultiplesBasepointBytes_length)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (withRoOk DalekCliRoOk
  dalekCliMultiLib_externAt_none specSimulates_absorb_roDataSep specSimulates_withVmPreserved
  specSimulates_keepsFs dalekScalarModVec dalekScalarWideVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (EdExtValid)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (fe51OfNat51
  fe51OfNat51_length
  fe51OfNat51_bounded51 fe51OfNat51_bounded fe51ValOfBytes_fe51OfNat51 edExtToBytes51
  edExtToBytes51_length edExtToBytes51_bounded51 edExtToBytes51_bounded
  edExtOfBytes_edExtToBytes51_mod edExtOfBytes_edExtToBytes51
  edExtOfBytes_edExtToBytes51_edExtOfAffine edExtOfBytes_edExtToBytes51_edProjectiveToExtended
  edExtOfBytes_edExtToBytes51_dsmb dalekMontToEdVec dalekCompressVec dalekTorsionFreeBool
  dalekDsmbVec dalekPrimsReal dalekScalarModFallback dalekScalarWideFallback dalekMontToEdFallback
  dalekCompressFallback dalekTorsionFreeFallback dalekDsmbFallback PureFallbackPreserved
  dalekScalarModFallback_preserved dalekScalarWideFallback_preserved
  dalekMontToEdFallback_preserved dalekCompressFallback_preserved
  dalekTorsionFreeFallback_preserved dalekDsmbFallback_preserved dalekHookStack
  dalekPureLeafCore dalekScalarModSpec dalekScalarWideSpec dalekScalarModSpec_eq_cliExt
  dalekScalarWideSpec_eq_cliExt dalekPureLeaf_byVal_sim dalekPureLeaf_fallback_ok
  dalekScalarModFallback_ok dalekScalarWideFallback_ok dalekPureLeaf_post_fsT
  dalekOptionEdwardsAt dalekMontToEdCore dalekMontToEdSpec montToEdwards_mod2_eq_montLiftEd
  dalekMontToEd_post_fsT dalekMontToEdFallback_ok dalekCompressCore dalekCompressSpec
  dalekCompress_post_fsT dalekCompress_byVal_bound_sim dalekCompressFallback_ok
  dalekTorsionFreeBool_eq_of_valid dalekTorsionFreeCore dalekTorsionFreeSpec
  dalekTorsionFree_post_fsT dalekTorsionFree_bound_sim dalekTorsionFreeFallback_ok
  dalekDsmbCore dalekDsmbSpec dalekDsmb_post_fsT dalekDsmbFallback_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality (RwOnlyHeap
  rwOnlyHeap_pure rwOnlyHeap_pointsToBytes rwOnlyHeap_pointsTo64 rwOnlyHeap_memRegion
  rwOnlyHeap_stackAt rwOnlyHeap_sepConj rwOnlyHeap_sepExists BoundedHeapIntervals
  boundedHeapIntervals_mono boundedHeapIntervals_pure boundedHeapIntervals_pointsToBytes
  boundedHeapIntervals_memRegion boundedHeapIntervals_stackAt boundedHeapIntervals_sepConj
  dalekActiveBlocks dalekActiveKeep DalekActiveCodeLoaded DalekActiveRoOk DalekActivePlaceable
  checkDalekActivePlaceable dalekActivePlaceable_of_check dalekActiveInvMem dalekActiveGuard
  dalekActiveInvMem_stripExecOutside dalekActiveGuard_stripS dalekActiveGuard_stripS_iff_of_roNoExec
  dalekActiveGuard_stripS_setPC dalekActiveInvMem_of_keepsFrozen
  dalekActive_subroutineOk_guarded_withVmPreserved)

/-! ## 1. Active State Guard (`dalekActiveInvMem`, `dalekActiveGuard`) & Generic `dalekBlockGhost` -/

private theorem keepFsTrace_eq_of_fs_trace {f : State → State}
    (hfs : ∀ s : State, (f s).fs = s.fs) (htr : ∀ s : State, (f s).trace = s.trace) :
    keepFsTrace f = f := by
  funext s; unfold keepFsTrace; rw [← hfs s, ← htr s]

private theorem dalekActiveKeep_of_block_offset (dalekMpl : MultiPlacement) {j k : Nat}
    (hj : j ∈ dalekActiveBlocks)
    (hno : (dalekCliMultiLib.blockProgram dalekMpl j).base.toNat +
      (dalekCliMultiLib.blockProgram dalekMpl j).code.length ≤ 2 ^ 64)
    (hk : k < (dalekCliMultiLib.blockProgram dalekMpl j).code.length) :
    dalekActiveKeep dalekMpl ((dalekCliMultiLib.blockProgram dalekMpl j).base + BitVec.ofNat 64 k) = true := by
  let Pj := dalekCliMultiLib.blockProgram dalekMpl j
  have hsub : Pj.base + BitVec.ofNat 64 k - Pj.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (Pj.base + BitVec.ofNat 64 k - Pj.base).toNat < Pj.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  unfold dalekActiveKeep; rw [List.any_eq_true]; exact ⟨j, hj, decide_eq_true hin⟩

@[expose] noncomputable def dalekBlockGhost [LibsignalPlacement]
    (dalekMpl : MultiPlacement) (j : Nat) {α : Type} (master : Spec α) (fallback : State → State) : State → State :=
  linkedCallHookG (dalekActiveGuard dalekMpl) (dalekActiveKeep dalekMpl) emptyStdProg
    (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j) (withLsRet master) fallback

theorem dalekBlockGhost_fs [LibsignalPlacement] (dalekMpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) (s0 : State) :
    (dalekBlockGhost dalekMpl j master fallback s0).fs = s0.fs :=
  linkedCallHookG_fs (dalekActiveGuard dalekMpl) (dalekActiveKeep dalekMpl) emptyStdProg
    (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j) (withLsRet master) fallback s0

theorem dalekBlockGhost_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) : HookFsTraced IsFsC (dalekBlockGhost dalekMpl j master fallback) :=
  linkedCallHookG_fsT (dalekActiveGuard dalekMpl) (dalekActiveKeep dalekMpl) emptyStdProg
    (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j) (withLsRet master) fallback

theorem dalekBlockGhost_preserves_execFrozen [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (j : Nat) {α : Type} (master : Spec α) {fallback : State → State}
    (hfb : PureFallbackPreserved fallback) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (dalekBlockGhost dalekMpl j master fallback u).mem := by
  classical
  unfold dalekBlockGhost linkedCallHookG
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (hfb s).2.1) (fun s => (hfb s).2.2.1)
  split
  · unfold linkedCallHook; split
    · split
      · rename_i hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · rw [hkfb]; exact ExecFrozen.of_perm_eq hfr (hfb u).1.perm_eq
    · exact hfr
  · split
    · rw [hkfb]; exact ExecFrozen.of_perm_eq hfr (hfb u).1.perm_eq
    · exact hfr

theorem dalekBlockGhost_lsRetAddr624_of_noException [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat} {α : Type}
    {master : Spec α} {fallback : State → State} {u : State}
    (hnoex : ∀ msg, (dalekBlockGhost dalekMpl j master fallback u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  lsRetAddr624_of_noException_via_activeRealPre linkedCallHookG_activeRealPre_of_noException hnoex

theorem dalekBlockGhost_keepLr_false_of_noException [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat} {α : Type}
    {master : Spec α} {fallback : State → State} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hnoex : ∀ msg, (dalekBlockGhost dalekMpl j master fallback u).status ≠ .Exception msg) :
    dalekActiveKeep dalekMpl (u.readReg64 .lr) = false :=
  keepLr_false_of_noException_via_activeRealPre hKeep linkedCallHookG_activeRealPre_of_noException hnoex

private theorem dalekBlockProgram_svc (dalekMpl : MultiPlacement) (j : Nat) :
    (dalekCliMultiLib.blockProgram dalekMpl j).svc = Syscall.standard := rfl

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := fun a => by
  have hst := hstrip a; rw [ProofLib.strip_perm, ProofLib.strip_perm] at hst
  have hfr0_a := hfr0 a; have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a <;> cases hpf : mf.perm a
    · rfl
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rename_i p0 pf; rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
      rcases p0 with ⟨r0, w0, x0, _, _⟩; rcases pf with ⟨rf, wf, xf, _, _⟩; unfold ProofLib.stripPerm at hst
      cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
        cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

structure DalekBlockBridge (j : Nat) {α β : Type}
    (blockSpec : MultiPlacement → Spec β) (master : Spec α) (fallback : State → State) : Prop where
  hj_act : j ∈ dalekActiveBlocks := by decide
  hj : j < dalekCliMultiLib.blocks.length := by decide
  blk_ok : DalekBlockOk j blockSpec
  blk_pan : ∀ mpl, (blockSpec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_ex : ∀ mpl, (blockSpec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_oom : ∀ mpl, (blockSpec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_pre_mem : ∀ mpl x (s : State) (m : Memory),
    (blockSpec mpl).pre x (s.setMem m) = (blockSpec mpl).pre x s := by intro _ _ s _; cases s; rfl
  blk_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
    (blockSpec mpl).post x (s0.setMem m0) (sf.setMem mf) = (blockSpec mpl).post x s0 sf := by
    intro _ _ s0 sf _ _; cases s0; cases sf; rfl
  sim : ∀ mpl, SpecSimulates (keepsFs (Spec.withTraceEq (blockSpec mpl))) (withRoOk (DalekCliRoOk mpl) master)
  m_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl
  m_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl
  m_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl
  m_pre_mem : ∀ x (s : State) (m : Memory),
    master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl
  m_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
    master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
    intro _ s0 sf _ _; cases s0; cases sf; rfl
  m_pre_rw : ∀ x s h, (master.pre x s).holds h → RwOnlyHeap h
  m_pre_bdd : ∀ x s h, (master.pre x s).holds h → BoundedHeapIntervals 6 0x10000 h
  m_post_rw : ∀ x s0 sf h, (master.post x s0 sf).holds h → RwOnlyHeap h
  strip_inv : ∀ keep, SpecStripSInvariant keep master := by
    intro _; exact ⟨fun _ s => by cases s; rfl, fun _ s0 sf => by cases s0; cases sf; rfl,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  fsT : SpecPreservesFsTrace master
  post_fsT : ∀ x (R : SepProp) (s0 sf : State), sf.mem ⊨ master.post x s0 sf ∗ R → sf.fs = s0.fs ∧ sf.trace = s0.trace
  pre_pc : ∀ x (s : State) (pc : BitVec 64), master.pre x (s.setPC pc) = master.pre x s := by intro _ s _; cases s; rfl
  out_pc : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
    SubroutineOutcome master x R (s0.setPC pc) sf → SubroutineOutcome master x R s0 sf := by
    intro _ _ s0 sf _ h; cases s0; cases sf; exact h
  fb_pres : PureFallbackPreserved fallback
  fb_ok : HookOk fallback master

private theorem dalekSubroutineOk_guarded_withVmPreserved {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (dalekMpl : MultiPlacement) :
    subroutine_ok (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j)
      (withStateGuard (dalekActiveGuard dalekMpl) (withVmPreserved master)) :=
  dalekActive_subroutineOk_guarded_withVmPreserved B.hj_act dalekMpl B.blk_ok B.blk_pan B.blk_ex
    B.blk_oom B.blk_pre_mem B.blk_post_mem B.sim B.m_pan B.m_ex B.m_oom B.m_pre_mem B.m_post_mem
    B.m_pre_rw B.m_pre_bdd B.m_post_rw

private theorem dalekSubroutineOk_guarded_withLsRet [LibsignalPlacement] {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (dalekMpl : MultiPlacement) :
    subroutine_ok (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j)
      (withStateGuard (dalekActiveGuard dalekMpl) (withLsRet master)) := by
  have hDrop : SpecSimulates (withStateGuard (dalekActiveGuard dalekMpl) (withVmPreserved master))
      (withStateGuard (dalekActiveGuard dalekMpl) master) := fun x R s0 hpre => ⟨x, R, hpre, fun sf hout => by
    rcases hout with ⟨hret, hcc, hpost⟩ | h
    · dsimp only [withStateGuard, withVmPreserved] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; exact Or.inl ⟨hret, hcc, hpost.2⟩
    · exact Or.inr h⟩
  have hLs := subroutine_ok_withLsRet (SpecSimulates.subroutine_ok hDrop (dalekSubroutineOk_guarded_withVmPreserved B dalekMpl))
  have hComm :
      withLsRet (withStateGuard (dalekActiveGuard dalekMpl) master) =
        withStateGuard (dalekActiveGuard dalekMpl) (withLsRet master) :=
    withLsRet_frameLeft master (fun _ s => ⌜dalekActiveGuard dalekMpl s⌝) master.post
  rwa [hComm] at hLs

theorem dalekBlockGhost_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withLsRet master) := by
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (B.fb_pres s).2.1) (fun s => (B.fb_pres s).2.2.1)
  exact hookOk_linkedCallHookG emptyStdProg_svc (dalekBlockProgram_svc dalekMpl j)
    (fun pc _ => emptyStdProg_externAt_none pc) (dalekCliMultiLib_externAt_none dalekMpl j B.hj (fun _ => none))
    (fun s0 hFr hG => dalekActiveGuard_stripS_setPC dalekMpl (dalekMpl.base j) s0 hFr hG)
    (dalekSubroutineOk_guarded_withLsRet B dalekMpl)
    (specStripSInvariant_withLsRet (B.strip_inv (dalekActiveKeep dalekMpl))) (specPreservesFsTrace_withLsRet B.fsT)
    (withLsRet_pre_setPC B.pre_pc) (withLsRet_outcome_setPC B.out_pc) (by rw [hkfb]; exact hookOk_withLsRet B.fb_ok)

theorem dalekBlockGhost_vmPreserved_and_nonSyscall [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (s0 : State) :
    let sf := dalekBlockGhost dalekMpl j master fallback s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle := by
  classical
  dsimp only; unfold dalekBlockGhost
  have hkfb := keepFsTrace_eq_of_fs_trace (fun s => (B.fb_pres s).2.1) (fun s => (B.fb_pres s).2.2.1)
  by_cases hG : dalekActiveGuard dalekMpl s0
  · rw [linkedCallHookG_eq_of_guard hG]; unfold linkedCallHook; split
    · rename_i hActPre; split
      · rename_i hReal; rcases hActPre with ⟨hrun, hsp, x, R, hpreLs⟩
        let keep := dalekActiveKeep dalekMpl; let s1 := s0.setPC (dalekMpl.base j); let s1' := stripS keep s1
        have hs1_pre : s1.mem ⊨ master.pre x s1 ∗ R := by dsimp only [s1]; rw [B.pre_pc]; exact (extract_withLsRet hpreLs).2
        have hs1'_pre : s1'.mem ⊨ master.pre x s1' ∗ R := by
          have hsat := satisfies_stripExecOutside keep hs1_pre; rwa [← (B.strip_inv keep).pre_eq x s1] at hsat
        have hs1'_preG : s1'.mem ⊨ (withStateGuard (dalekActiveGuard dalekMpl) (withVmPreserved master)).pre x s1' ∗ R := by
          dsimp only [withStateGuard, withVmPreserved]; rw [sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨dalekActiveGuard_stripS_setPC dalekMpl (dalekMpl.base j) s0 hReal.1 hG, hs1'_pre⟩
        obtain ⟨sf', hsteps', hout'⟩ := reaches_outcome_iff.1
          (subroutine_ok_iff.1 (dalekSubroutineOk_guarded_withVmPreserved B dalekMpl) x R s1' rfl hrun hs1'_preG hsp) hReal.2.2.1
        have hsub_no := dalekCliMultiLib_externAt_none dalekMpl j B.hj (fun _ => none)
        rcases hout' with ⟨hret', _, hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
        · obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
            stepsUntil_of_stripS_standard (s0 := s0) emptyStdProg_svc (dalekBlockProgram_svc dalekMpl j)
              (fun pc _ => emptyStdProg_externAt_none pc) (fun pc f he => nomatch hsub_no pc ▸ he)
              hReal.2.1 hsteps' (Or.inl hret') (by rw [hret'.2.2]; decide) s1 rfl hReal.1
          have hchoose := Classical.choose_spec hReal.2.2.2
          rw [StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf]
          have horc' := Steps.oracle_eq_of_standard (dalekBlockProgram_svc dalekMpl j) hsub_no hsteps'; rw [hsf_eq] at horc'
          dsimp only [withStateGuard, withVmPreserved] at hpost'
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'; obtain ⟨hvm', hpostM'⟩ := hpost'
          obtain ⟨hfs', htr'⟩ := B.post_fsT x R s1' sf' hpostM'; rw [hsf_eq] at hvm' hfs' htr'
          have hfs : sf.fs = s0.fs := by dsimp only [s1', s1] at hfs'; cases s0; cases sf; exact hfs'
          have htr : sf.trace = s0.trace := by dsimp only [s1', s1] at htr'; cases s0; cases sf; exact htr'
          have horc : sf.oracle = s0.oracle := by dsimp only [s1', s1] at horc'; cases s0; cases sf; exact horc'
          have hperm := perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen hvm'.2.2.1
          have hpool : PoolPreserved s0 sf := by
            rcases hvm'.1 with ⟨h1, h2, h3⟩; dsimp only [s1', s1] at h1 h2 h3
            exact ⟨by cases s0; cases sf; exact h1, by cases s0; cases sf; exact h2, by cases s0; cases sf; exact h3⟩
          have hphys : sf.physMemAvail = s0.physMemAvail := by
            have hp := hvm'.2.1; dsimp only [s1', s1] at hp; cases s0; cases sf; exact hp
          exact ⟨⟨hpool, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩, hfs, htr, hpool.2.2, horc⟩
        · dsimp only [withStateGuard, withVmPreserved] at hp; rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
        · dsimp only [withStateGuard, withVmPreserved] at he; rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
        · dsimp only [withStateGuard, withVmPreserved] at ho; rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim
      · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨VmPreserved.of_eq rfl rfl rfl rfl rfl (fun _ _ _ => rfl), rfl, rfl, rfl, rfl⟩
  · rw [linkedCallHookG_eq_of_not_guard hG]; split
    · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨VmPreserved.of_eq rfl rfl rfl rfl rfl (fun _ _ _ => rfl), rfl, rfl, rfl, rfl⟩

theorem dalekBlockGhost_withVmPreserved_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withLsRet (withVmPreserved master)) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withVmPreserved (dalekBlockGhost_ok B) (fun s0 => (dalekBlockGhost_vmPreserved_and_nonSyscall B s0).1)

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) : u.setPC pc = u := by
  cases u; dsimp only [State.setPC] at hpc ⊢; subst hpc; rfl
private theorem realProg617_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard := rfl
@[expose] def hasAtLeast4 {α : Type} : List α → Bool | _ :: _ :: _ :: _ :: _ => true | _ => false
private theorem getD_eq_getElem_local {α : Type} : ∀ (l : List α) (d : α) {j : Nat} (hj : j < l.length), l.getD j d = l[j]
  | [], _, _, hj => nomatch hj | _ :: _, _, 0, _ => rfl | _ :: tl, d, _ + 1, hj => getD_eq_getElem_local tl d (Nat.lt_of_succ_lt_succ hj)
private theorem flatMap_patchedWord_length (blk : Obj.CodeBlock) (pl : Placement) :
    ∀ l : List Nat, (l.flatMap fun j => Obj.bytesOfWordLE (blk.patchedWord pl (4 * j))).length = 4 * l.length
  | [] => rfl
  | hd :: tl => by
    have hbw : (Obj.bytesOfWordLE (blk.patchedWord pl (4 * hd))).length = 4 := rfl
    rw [List.flatMap_cons, List.length_append, hbw, flatMap_patchedWord_length blk pl tl, List.length_cons]; omega
private theorem blockProgram_no_wrap_and_pos (dalekMpl : MultiPlacement) {j : Nat}
    (hj_act : j ∈ dalekActiveBlocks) (hj : j < dalekCliMultiLib.blocks.length)
    (hpl : DalekActivePlaceable dalekMpl)
    (hw : hasAtLeast4 (dalekCliMultiLib.blocks.getD j { code := [] }).code = true) :
    ((dalekCliMultiLib.blockProgram dalekMpl j).base.toNat + (dalekCliMultiLib.blockProgram dalekMpl j).code.length ≤ 2 ^ 64) ∧
    0 < (dalekCliMultiLib.blockProgram dalekMpl j).code.length := by
  have hget := getD_eq_getElem_local dalekCliMultiLib.blocks { code := [] } hj
  have hge4 : 4 ≤ dalekCliMultiLib.blocks[j].code.length := by
    rw [hget] at hw
    rcases hc : dalekCliMultiLib.blocks[j].code with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [hasAtLeast4, hc] at hw ⊢
  have hlen : (dalekCliMultiLib.blockProgram dalekMpl j).code.length = 4 * (dalekCliMultiLib.blocks[j].code.length / 4) := by
    change ((dalekCliMultiLib.blocks.getD j { code := [] }).patched _).length = _
    unfold Obj.CodeBlock.patched; rw [flatMap_patchedWord_length, List.length_range, hget]
  have hnw := hpl.active_block_no_wrap hj_act hj
  have hle := Nat.mul_div_le dalekCliMultiLib.blocks[j].code.length 4
  change (dalekMpl.base j).toNat + (dalekCliMultiLib.blockProgram dalekMpl j).code.length ≤ 2 ^ 64 ∧ _
  rw [hlen]; exact ⟨by omega, by omega⟩

theorem dalekBlockGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl dalekMpl : MultiPlacement) (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (sym : String) {j : Nat} {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks, StubReachesTargetOn (dalekActiveInvMem dalekMpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (libsignalSessionLib.resolve mpl sym) (dalekMpl.base j)) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True) (dalekBlockGhost dalekMpl j master fallback) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨dalekBlockGhost_preserves_execFrozen dalekMpl j master B.fb_pres hfr, dalekBlockGhost_fs dalekMpl j master fallback u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _; right
    have hRep := ghostExternReplaysOn_of_linkedCallHookG_liftVis
      (InvMem := dalekActiveInvMem dalekMpl) (Guard := dalekActiveGuard dalekMpl) (keep := dalekActiveKeep dalekMpl)
      (P_run := emptyStdProg) (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (P_sub := dalekCliMultiLib.blockProgram dalekMpl j) (stubPc := libsignalSessionLib.resolve mpl sym)
      (entryTarget := dalekMpl.base j) (spec := withLsRet master) (fallback := fallback)
      emptyStdProg_svc (dalekBlockProgram_svc dalekMpl j) (fun pc _ => emptyStdProg_externAt_none pc)
      (dalekCliMultiLib_externAt_none dalekMpl j B.hj (fun _ => none)) (hRealStubNone W) (hStub W)
      (fun _ _ _ _ _ hvis => h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := dalekActiveKeep dalekMpl) (P1 := emptyStdProg) (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt_none pc) (fun _ hk => hRealDalekNoExt W hk) hvis)
      (fun _ _ hInvM => (dalekActiveInvMem_stripExecOutside hInvM).2.1 j B.hj_act)
      (fun _ _ hInvM hkf => dalekActiveInvMem_of_keepsFrozen hkf hInvM) (fun _ _ hInvM => hInvM)
      (fun s0 hFr hG => dalekActiveGuard_stripS_setPC dalekMpl (dalekMpl.base j) s0 hFr hG)
      (dalekSubroutineOk_guarded_withLsRet B dalekMpl)
      (specStripSInvariant_withLsRet (B.strip_inv (dalekActiveKeep dalekMpl)))
      (specPreservesFsTrace_withLsRet B.fsT) (withLsRet_pre_setPC B.pre_pc) (withLsRet_outcome_setPC B.out_pc)
    refine ⟨hRep.1, fun u _ _ hpc hrun hnoex hkf hfr hInvU => ?_⟩
    obtain ⟨hSteps1, hfr1, _⟩ := hRep.2 u hpc hrun hnoex hfr
      (dalekBlockGhost_keepLr_false_of_noException hKeep hnoex) (hInvDalek u hInvU)
    exact ⟨hSteps1, hfr1, hInvKeep u _ hInvU hkf (dalekBlockGhost_fs dalekMpl j master fallback u)⟩

theorem dalekBlockGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl dalekMpl : MultiPlacement) (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (sym : String) {j : Nat} {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl sym = dalekMpl.base j)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hw : hasAtLeast4 (dalekCliMultiLib.blocks.getD j { code := [] }).code = true := by rfl) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True) (dalekBlockGhost dalekMpl j master fallback) := by
  obtain ⟨hnw, hpos⟩ := blockProgram_no_wrap_and_pos dalekMpl B.hj_act B.hj hpl hw
  exact dalekBlockGhost_rowReplayOn_of_stub mpl mmpl dalekMpl InvS EG sym B hInvDalek hInvKeep hKeep hRealDalekNoExt
    (fun W => by
      rw [hTargetEq, show dalekMpl.base j = (dalekCliMultiLib.blockProgram dalekMpl j).base + 0#64 by
        change dalekMpl.base j = dalekMpl.base j + 0#64; bv_omega]
      exact hRealDalekNoExt W (dalekActiveKeep_of_block_offset dalekMpl B.hj_act hnw hpos))
    (fun _ u hpc _ _ _ => by rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]; exact Steps.refl _)

/-! ## 2. Generic Stack/Allocator Lifting & the 6 `dalekCliMultiLib` Ghost Hooks -/

private theorem satisfies_prepend_pure {m : Memory} {P : Prop} {Q : SepProp} (hP : P) (hQ : m ⊨ Q) : m ⊨ ⌜P⌝ ∗ Q :=
  (satisfies_pure_sepConj P Q m).mpr ⟨hP, hQ⟩

private theorem withLsRet_withAlloc_eq [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc A lim spec) = withAlloc A lim (withLsRet spec) := by
  cases spec; dsimp only [withLsRet, withAlloc]; congr 1; funext ⟨x, st⟩ s; simp only [sepConj_assoc]

private theorem specSimulates_of_keepsFs {α : Type} (spec : Spec α) : SpecSimulates (keepsFs spec) spec :=
  fun x R s0 hpre => ⟨x, R, hpre, fun sf hout => by
    rcases hout with ⟨hret, hcc, hp⟩ | h
    · dsimp only [keepsFs] at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp; exact Or.inl ⟨hret, hcc, hp.2⟩
    · exact Or.inr h⟩

private theorem specSimulates_withStack_mono {α : Type} (core : Spec α) {stk₀ stk : Nat}
    (hlo : stk₀ ≤ stk) (hhi : stk ≤ 2 ^ 64) (hpan : core.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : core.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl) (hoom : core.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withStack core stk₀) (withStack core stk) := by
  refine SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun x R s0 hpre => ?_
  dsimp only [withStack] at hpre; rw [stackAt_shrink s0.sp stk stk₀ hlo hhi] at hpre
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk₀) ∗ R,
    Satisfies.mono (by dsimp only [withStack]; sep_entail) hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [withStack] at hpost ⊢; rw [stackAt_shrink s0.sp stk stk₀ hlo hhi]; exact Satisfies.mono (by sep_entail) hpost

private theorem specSimulates_intro_roOk {α β : Type} {RoOk : Memory → Prop} {spec₁ : Spec α} {spec₂ : Spec β}
    (h : SpecSimulates spec₁ spec₂) : SpecSimulates spec₁ (withRoOk RoOk spec₂) := fun y R s0 hpre => by
  dsimp only [withRoOk] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact h y R s0 hpre.2

private theorem specSimulates_absorb_ro1 {α : Type} {RoOk : Memory → Prop} {addr : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α} (hlen : bytes.length ≤ 2 ^ 64) (hro : ∀ m, RoOk m → RoDataAt m addr bytes) :
    SpecSimulates (withRoOk RoOk (withRoDataSep addr bytes spec)) (withRoOk RoOk spec) := by
  have hcomm : SpecSimulates (withRoOk RoOk (withRoDataSep addr bytes spec))
      (withRoDataSep addr bytes (withRoOk RoOk spec)) :=
    fun x R s0 hpre => ⟨x, R,
      by dsimp only [withRoDataSep, withRoOk] at hpre ⊢; exact Satisfies.mono (by sep_entail) hpre,
      fun _ hout => hout⟩
  exact hcomm.trans (specSimulates_absorb_roDataSep hlen hro)

private theorem specPreservesFsTrace_of_post {α : Type} {master : Spec α}
    (hpost_fsT : ∀ x (R : SepProp) (s0 sf : State), sf.mem ⊨ master.post x s0 sf ∗ R → sf.fs = s0.fs ∧ sf.trace = s0.trace)
    (hpan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl) (hex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl) : SpecPreservesFsTrace master :=
  fun x R s0 sf hout => by
    rcases hout with ⟨_, _, hp⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨hfs, htr⟩ := hpost_fsT x R s0 sf hp; exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
    · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem dalekGhost_lift_keepsFs_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) {target : Spec γ} (hsim : SpecSimulates master (keepsFs target)) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withLsRet (withVmPreserved (keepsFs target))) :=
  hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved hsim) (dalekBlockGhost_withVmPreserved_ok B)

private theorem dalekGhost_lift_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withLsRet (withVmPreserved target)) :=
  hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved hsim) (dalekBlockGhost_withVmPreserved_ok B)

private theorem dalekGhost_lift_withAlloc_ls_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withAlloc A lim (withLsRet target)) := by
  have h1 : HookOk (dalekBlockGhost dalekMpl j master fallback) (withVmPreserved (withLsRet target)) := by
    rw [← withLsRet_withVmPreserved]; exact dalekGhost_lift_ok B hsim
  exact hookOk_withAlloc_of_withVmPreserved A lim h1

private theorem dalekGhost_lift_withAlloc_ok [LibsignalPlacement] {dalekMpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (dalekBlockGhost dalekMpl j master fallback) (withLsRet (withAlloc A lim target)) := by
  rw [withLsRet_withAlloc_eq]; exact dalekGhost_lift_withAlloc_ls_ok B A lim hsim

private theorem pureLeaf_pre_rw {m n : Nat} (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n)
    (stk : Nat) (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).pre x s).holds h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj
    (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (fun _ => rwOnlyHeap_memRegion _ _)))
    (fun _ => rwOnlyHeap_stackAt _ _) hh

private theorem pureLeaf_pre_bdd {m n : Nat} (hm : m ≤ 0x10000) (hn : n ≤ 0x10000)
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) {stk : Nat} (hstk : stk ≤ 0x10000)
    (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).pre x s).holds h) :
    BoundedHeapIntervals 6 0x10000 h :=
  boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
    (boundedHeapIntervals_sepConj
      (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
        (fun _ => boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; exact hm))
          (fun _ => boundedHeapIntervals_memRegion _ _ hn)))
      (fun _ => boundedHeapIntervals_stackAt _ _ hstk) hh)

private theorem pureLeaf_post_rw {m n : Nat} (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n)
    (stk : Nat) (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s0 sf : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).post x s0 sf).holds h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
    (fun _ => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (fun _ => rwOnlyHeap_pointsToBytes _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _)) hh

/-! ### 2.1 `B01` (`lsScalarModSymCli`) & `B02` (`lsScalarWideSymCli`) -/

private theorem scalarMod_sim_master :
    SpecSimulates (Spec.withTraceEq scalarFromBytesModOrderSpec) (dalekScalarModSpec 208 false) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [dalekScalarModSpec, withStack, dalekPureLeafCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 208 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre; simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (inA ↦ₛ v.toList) ⌜out_bs.length = 32⌝, satisfies_pure_sepConj] at hpre; obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
  · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
    rw [show stackFrame sf 208 = stackAt s0.sp 208 by unfold stackFrame; rw [hcc.1]] at hpost
    simp only [dalekScalarModSpec, withStack, dalekPureLeafCore, inputAfter, Bool.false_eq_true,
      ↓reduceIte, dalekScalarModVec, List.Vector.toList, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

private theorem dalekScalarModBridge :
    DalekBlockBridge 1 (fun _ => scalarFromBytesModOrderSpec) (keepsFs (dalekScalarModSpec 208 false)) dalekScalarModFallback :=
  { blk_ok := scalar_from_bytes_mod_order_ok
    sim := fun _ => specSimulates_intro_roOk (specSimulates_keepsFs scalarMod_sim_master)
    m_pre_rw := pureLeaf_pre_rw dalekScalarModVec 208
    m_pre_bdd := pureLeaf_pre_bdd (by decide) (by decide) dalekScalarModVec (by decide)
    m_post_rw := pureLeaf_post_rw dalekScalarModVec 208
    fsT := specPreservesFsTrace_of_post (dalekPureLeaf_post_fsT dalekScalarModVec 208)
    post_fsT := dalekPureLeaf_post_fsT dalekScalarModVec 208
    fb_pres := dalekScalarModFallback_preserved
    fb_ok := dalekPureLeaf_fallback_ok (by decide) dalekScalarModVec 208 }

private theorem scalarWide_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (scalarFromBytesModOrderWideSpec mpl))
      (withRoOk (DalekCliRoOk mpl) (dalekScalarWideSpec 448 false)) := by
  have hcore : SpecSimulates (Spec.withTraceEq (scalarFromBytesModOrderWideSpec mpl))
      (withRoDataSep (sc52_l mpl) sc52LBytes (withRoDataSep (sc52_rr mpl) sc52RRBytes (dalekScalarWideSpec 448 false))) := by
    refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekScalarWideSpec, withStack, dalekPureLeafCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = inA ∧ s0.readReg64 .x8 = ret⌝ ∗ ((sc52_l mpl ↦ᵣ sc52LBytes) ∗
        (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗ (inA ↦ₛ v.toList) ∗ memRegion ret 32 ∗ stackAt s0.sp 448 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre1
    rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 448 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre; obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 32⌝ ∗ ((sc52_l mpl ↦ᵣ sc52LBytes) ∗ (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗
        (inA ↦ₛ v.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 448 ∗ R) := Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderWideSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderWideSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 448 = stackAt s0.sp 448 by unfold stackFrame; rw [hcc.1]] at hpost
      simp only [withRoDataSep, dalekScalarWideSpec, withStack, dalekPureLeafCore, inputAfter,
        Bool.false_eq_true, ↓reduceIte, dalekScalarWideVec, List.Vector.toList, sepConj_assoc]
      exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr hpost)
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [sc52LBytes_length]; decide) (fun _ h => h.ro_sc52_l)).trans
      (specSimulates_absorb_ro1 (by rw [sc52RRBytes_length]; decide) (fun _ h => h.ro_sc52_rr)))

private theorem dalekScalarWideBridge :
    DalekBlockBridge 2 scalarFromBytesModOrderWideSpec (keepsFs (dalekScalarWideSpec 448 false)) dalekScalarWideFallback :=
  { blk_ok := scalar_from_bytes_mod_order_wide_ok
    sim := fun mpl => specSimulates_keepsFs (scalarWide_sim_master mpl)
    m_pre_rw := pureLeaf_pre_rw dalekScalarWideVec 448
    m_pre_bdd := pureLeaf_pre_bdd (by decide) (by decide) dalekScalarWideVec (by decide)
    m_post_rw := pureLeaf_post_rw dalekScalarWideVec 448
    fsT := specPreservesFsTrace_of_post (dalekPureLeaf_post_fsT dalekScalarWideVec 448)
    post_fsT := dalekPureLeaf_post_fsT dalekScalarWideVec 448
    fb_pres := dalekScalarWideFallback_preserved
    fb_ok := dalekPureLeaf_fallback_ok (by decide) dalekScalarWideVec 448 }

@[expose] noncomputable def dalekScalarModGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 1 (keepsFs (dalekScalarModSpec 208 false)) dalekScalarModFallback
@[expose] noncomputable def dalekScalarWideGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 2 (keepsFs (dalekScalarWideSpec 448 false)) dalekScalarWideFallback

theorem dalekScalarModGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekScalarModGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekScalarModBridge s0
theorem dalekScalarModGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekScalarModGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 1 _ _
theorem dalekScalarModGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 208 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarModGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekScalarModSpec stk byVal))) :=
  dalekGhost_lift_ok dalekScalarModBridge ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarModVec stk byVal)))
theorem dalekScalarModGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 208 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarModGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekScalarModSpec stk byVal)))) :=
  dalekGhost_lift_keepsFs_ok dalekScalarModBridge (specSimulates_keepsFs
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarModVec stk byVal)))
theorem dalekScalarModGhostLs_cliExt_ok [LibsignalPlacement] (dalekMpl : MultiPlacement) (byVal : Bool := false) :
    HookOk (dalekScalarModGhostLs dalekMpl) (withLsRet (withVmPreserved (pureByteFunctionSpec dalekScalarModVec byVal))) :=
  dalekScalarModGhostLs_at_ok dalekMpl extHookStack byVal (by decide) (by decide)
theorem dalekScalarModGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 208 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarModGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekScalarModSpec stk byVal))) :=
  dalekGhost_lift_withAlloc_ok dalekScalarModBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarModVec stk byVal)))
theorem dalekScalarModGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 208 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarModGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekScalarModSpec stk byVal))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekScalarModBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarModVec stk byVal)))
theorem dalekScalarModGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsScalarModSymCli = dalekMpl.base 1)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsScalarModSymCli (fun _ => True) (dalekScalarModGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsScalarModSymCli dalekScalarModBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

theorem dalekScalarWideGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekScalarWideGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekScalarWideBridge s0
theorem dalekScalarWideGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekScalarWideGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 2 _ _
theorem dalekScalarWideGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 448 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarWideGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekScalarWideSpec stk byVal))) :=
  dalekGhost_lift_ok dalekScalarWideBridge ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarWideVec stk byVal)))
theorem dalekScalarWideGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 448 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarWideGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekScalarWideSpec stk byVal)))) :=
  dalekGhost_lift_keepsFs_ok dalekScalarWideBridge (specSimulates_keepsFs
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarWideVec stk byVal)))
theorem dalekScalarWideGhostLs_cliExt_ok [LibsignalPlacement] (dalekMpl : MultiPlacement) (byVal : Bool := false) :
    HookOk (dalekScalarWideGhostLs dalekMpl) (withLsRet (withVmPreserved (pureByteFunctionSpec dalekScalarWideVec byVal))) :=
  dalekScalarWideGhostLs_at_ok dalekMpl extHookStack byVal (by decide) (by decide)
theorem dalekScalarWideGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 448 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarWideGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekScalarWideSpec stk byVal))) :=
  dalekGhost_lift_withAlloc_ok dalekScalarWideBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarWideVec stk byVal)))
theorem dalekScalarWideGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (hlo : 448 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekScalarWideGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekScalarWideSpec stk byVal))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekScalarWideBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekPureLeaf_byVal_sim dalekScalarWideVec stk byVal)))
theorem dalekScalarWideGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsScalarWideSymCli = dalekMpl.base 2)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsScalarWideSymCli (fun _ => True) (dalekScalarWideGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsScalarWideSymCli dalekScalarWideBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

/-! ### 2.2 `B08` (`lsToEdwardsSymCli`, stack `2576` B) -/

private theorem rwOnlyHeap_dalekOptionEdwardsAt (r : BitVec 64) :
    ∀ (opt : Option EdPoint) (h : Heap), (dalekOptionEdwardsAt r opt).holds h → RwOnlyHeap h
  | none, _, hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsTo64 _ _) (fun _ => rwOnlyHeap_memRegion _ _) hh
  | some _, _, hh =>
    rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsTo64 _ _) (fun _ => rwOnlyHeap_pointsToBytes _ _))) hh

private theorem montToEd_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (montgomeryPointToEdwardsSpec mpl)) (withRoOk (DalekCliRoOk mpl) (dalekMontToEdSpec 2576)) := by
  have hcore : SpecSimulates (Spec.withTraceEq (montgomeryPointToEdwardsSpec mpl))
      (withRoDataSep (fe51_minus_one mpl) fe51MinusOneBytes
        (withRoDataSep (fe51_edwards_d mpl) fe51EdwardsDBytes
          (withRoDataSep (fe51_sqrt_m1 mpl) fe51SqrtM1Bytes (dalekMontToEdSpec 2576)))) := by
    refine SpecSimulates.of_map fun ⟨uA, u, sign, ret⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekMontToEdSpec, withStack, dalekMontToEdCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = uA ∧ (s0.readReg64 .x1).setWidth 8 = sign ∧ s0.readReg64 .x8 = ret⌝ ∗
        ((fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗ (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
          (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗ (uA ↦ₛ u.toList) ∗ memRegion ret 168 ∗ stackAt s0.sp 2576 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx1, hx8⟩, hpre⟩ := hpre1
    have hx1' : BitVec.truncate 8 (s0.readReg32 .x1) = sign := by
      simp only [State.readReg32, BitVec.truncate_eq_setWidth, BitVec.setWidth_setWidth_of_le (s0.readReg64 .x1) (by decide : 8 ≤ 32)]
      exact hx1
    rw [memRegion_eq_exists_bytes ret 168 (by decide), stackAt_eq_stackFrameAt s0.sp 2576 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre; obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 168⌝ ∗ ((fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗
        (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗ (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗
        (uA ↦ₛ u.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 2576 ∗ R) := Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, uA, sign, out_bs, u.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, montgomeryPointToEdwardsSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hx1', hout_len, u.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, montgomeryPointToEdwardsSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 2576 = stackAt s0.sp 2576 by unfold stackFrame; rw [hcc.1]] at hpost
      dsimp only [withRoDataSep, dalekMontToEdSpec, withStack, dalekMontToEdCore]
      rcases hres : montToEdwards u.toList (sign.toNat % 2) with _ | P
      · rw [hres] at hpost
        simp only [dalekOptionEdwardsAt, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
        obtain ⟨pad_bs, hpost⟩ := hpost
        have hp1 : sf.mem ⊨ ⌜pad_bs.length = 160⌝ ∗ (((ret + 8#64) ↦ₛ pad_bs) ∗ (ret ↦₆₄ 0#64) ∗ (uA ↦ₛ u.toList) ∗
            (fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗ (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
            (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗ stackAt s0.sp 2576 ∗ R) := Satisfies.mono (by sep_entail) hpost
        rw [satisfies_pure_sepConj] at hp1; obtain ⟨hpad_len, hp1⟩ := hp1
        exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr
          (Satisfies.mono (sepConj_mono (pointsToBytes_entails_memRegion_of_length hpad_len) (Entails.refl _)) hp1))
      · rw [hres] at hpost
        simp only [dalekOptionEdwardsAt, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
        obtain ⟨pt_bs, hpost⟩ := hpost; exact ⟨pt_bs, Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr hpost)⟩
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [fe51MinusOneBytes_length]; decide) (fun _ h => h.ro_fe51_minus_one)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51EdwardsDBytes_length]; decide) (fun _ h => h.ro_fe51_edwards_d)).trans
        (specSimulates_absorb_ro1 (by rw [fe51SqrtM1Bytes_length]; decide) (fun _ h => h.ro_fe51_sqrt_m1))))

private theorem dalekMontToEdBridge :
    DalekBlockBridge 8 montgomeryPointToEdwardsSpec (keepsFs (dalekMontToEdSpec 2576)) dalekMontToEdFallback :=
  { blk_ok := montgomery_point_to_edwards_ok
    sim := fun mpl => specSimulates_keepsFs (montToEd_sim_master mpl)
    m_pre_rw := fun ⟨_, _, _, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (fun _ => rwOnlyHeap_memRegion _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, u, _, _⟩ _ _ hh => boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
      (boundedHeapIntervals_sepConj
        (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
          (fun _ => boundedHeapIntervals_sepConj
            (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide))
            (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))
        (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _, ret⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_dalekOptionEdwardsAt ret _)))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekMontToEd_post_fsT 2576)
    post_fsT := dalekMontToEd_post_fsT 2576
    fb_pres := dalekMontToEdFallback_preserved
    fb_ok := dalekMontToEdFallback_ok 2576 }

@[expose] noncomputable def dalekMontToEdGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 8 (keepsFs (dalekMontToEdSpec 2576)) dalekMontToEdFallback
theorem dalekMontToEdGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekMontToEdGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekMontToEdBridge s0
theorem dalekMontToEdGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekMontToEdGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 8 _ _
theorem dalekMontToEdGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (hlo : 2576 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekMontToEdGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekMontToEdSpec stk))) :=
  dalekGhost_lift_ok dalekMontToEdBridge ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekMontToEdGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (hlo : 2576 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekMontToEdGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekMontToEdSpec stk)))) :=
  dalekGhost_lift_keepsFs_ok dalekMontToEdBridge (specSimulates_keepsFs (specSimulates_withStack_mono _ hlo hhi))
theorem dalekMontToEdGhostLs_extStack_ok [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookOk (dalekMontToEdGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekMontToEdSpec extHookStack))) :=
  dalekMontToEdGhostLs_at_ok dalekMpl extHookStack (by decide) (by decide)
theorem dalekMontToEdGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (hlo : 2576 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekMontToEdGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekMontToEdSpec stk))) :=
  dalekGhost_lift_withAlloc_ok dalekMontToEdBridge A lim ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekMontToEdGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (hlo : 2576 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekMontToEdGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekMontToEdSpec stk))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekMontToEdBridge A lim ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekMontToEdGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsToEdwardsSymCli = dalekMpl.base 8)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsToEdwardsSymCli (fun _ => True) (dalekMontToEdGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsToEdwardsSymCli dalekMontToEdBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

/-! ### 2.3 `B14` (`lsCompressSymCli`, stack `1552` B) -/

private theorem compress_sim_master :
    SpecSimulates (Spec.withTraceEq edwardsPointCompressSpec) (dalekCompressSpec 1552 false (2 ^ 54)) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [dalekCompressSpec, withStack, dalekCompressCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx8, hvb⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 1552 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre; obtain ⟨out_bs, hpre⟩ := hpre
  have hpre2 : s0.mem ⊨ ⌜out_bs.length = 32⌝ ∗ ((inA ↦ₛ v.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 1552 ∗ R) :=
    Satisfies.mono (by sep_entail) hpre
  rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
  refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
  · dsimp only [Spec.withTraceEq, edwardsPointCompressSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, hvb⟩, Satisfies.mono (by sep_entail) hpre⟩
  · dsimp only [Spec.withTraceEq, edwardsPointCompressSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
    rw [show stackFrame sf 1552 = stackAt s0.sp 1552 by unfold stackFrame; rw [hcc.1]] at hpost
    simp only [dalekCompressSpec, withStack, dalekCompressCore, inputAfter, Bool.false_eq_true,
      ↓reduceIte, dalekCompressVec, List.Vector.toList, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

private theorem dalekCompressBridge :
    DalekBlockBridge 14 (fun _ => edwardsPointCompressSpec) (keepsFs (dalekCompressSpec 1552 false (2 ^ 54))) dalekCompressFallback :=
  { blk_ok := edwards_point_compress_ok
    sim := fun _ => specSimulates_intro_roOk (specSimulates_keepsFs compress_sim_master)
    m_pre_rw := fun ⟨_, _, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (fun _ => rwOnlyHeap_memRegion _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, v, _⟩ _ _ hh => boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
      (boundedHeapIntervals_sepConj
        (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
          (fun _ => boundedHeapIntervals_sepConj
            (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide))
            (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))
        (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _) (fun _ => rwOnlyHeap_pointsToBytes _ _)))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekCompress_post_fsT 1552)
    post_fsT := dalekCompress_post_fsT 1552
    fb_pres := dalekCompressFallback_preserved
    fb_ok := dalekCompressFallback_ok }

@[expose] noncomputable def dalekCompressGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 14 (keepsFs (dalekCompressSpec 1552 false (2 ^ 54))) dalekCompressFallback
theorem dalekCompressGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekCompressGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekCompressBridge s0
theorem dalekCompressGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekCompressGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 14 _ _
theorem dalekCompressGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (bound : Nat := 2 ^ 54)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 54 := by decide) :
    HookOk (dalekCompressGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekCompressSpec stk byVal bound))) :=
  dalekGhost_lift_ok dalekCompressBridge ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekCompress_byVal_bound_sim stk byVal hb)))
theorem dalekCompressGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (bound : Nat := 2 ^ 54)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 54 := by decide) :
    HookOk (dalekCompressGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekCompressSpec stk byVal bound)))) :=
  dalekGhost_lift_keepsFs_ok dalekCompressBridge (specSimulates_keepsFs
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekCompress_byVal_bound_sim stk byVal hb)))
theorem dalekCompressGhostLs_extStack_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (byVal : Bool := false) (bound : Nat := 2 ^ 54) (hb : bound ≤ 2 ^ 54 := by decide) :
    HookOk (dalekCompressGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekCompressSpec extHookStack byVal bound))) :=
  dalekCompressGhostLs_at_ok dalekMpl extHookStack byVal bound (by decide) (by decide) hb
theorem dalekCompressGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (bound : Nat := 2 ^ 54)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 54 := by decide) :
    HookOk (dalekCompressGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekCompressSpec stk byVal bound))) :=
  dalekGhost_lift_withAlloc_ok dalekCompressBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekCompress_byVal_bound_sim stk byVal hb)))
theorem dalekCompressGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (byVal : Bool := false) (bound : Nat := 2 ^ 54)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 54 := by decide) :
    HookOk (dalekCompressGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekCompressSpec stk byVal bound))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekCompressBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekCompress_byVal_bound_sim stk byVal hb)))
theorem dalekCompressGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsCompressSymCli = dalekMpl.base 14)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsCompressSymCli (fun _ => True) (dalekCompressGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsCompressSymCli dalekCompressBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

/-! ### 2.4 `B19` (`lsTorsionFreeSymCli`, stack `4848` B) -/

private theorem torsionFree_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (edwardsPointIsTorsionFreeU32Spec mpl))
      (withRoOk (DalekCliRoOk mpl) (dalekTorsionFreeSpec 4848 (2 ^ 53))) := by
  have hcore : SpecSimulates (Spec.withTraceEq (edwardsPointIsTorsionFreeU32Spec mpl))
      (withRoDataSep (basepoint_order mpl) basepointOrderBytes
        (withRoDataSep (fe51_one mpl) fe51OneBytes
          (withRoDataSep (fe51_edwards_d2 mpl) fe51EdwardsD2Bytes (dalekTorsionFreeSpec 4848 (2 ^ 53))))) := by
    refine SpecSimulates.of_map fun ⟨pA, p⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = pA ∧ fe51Point4Bounded p.toList (2 ^ 53)⌝ ∗
        ((basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
          (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (pA ↦ₛ p.toList) ∗ stackAt s0.sp 4848 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hpb⟩, hpre⟩ := hpre1
    rw [stackAt_eq_stackFrameAt s0.sp 4848 (by decide)] at hpre
    refine ⟨(pA, p.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, edwardsPointIsTorsionFreeU32Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hpb⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, edwardsPointIsTorsionFreeU32Spec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 4848 = stackAt s0.sp 4848 by unfold stackFrame; rw [hcc.1]] at hpost
      have hp1 : sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 =
          (if edPointEq (edVarBaseMul p.toList basepointOrderBytes) edExtZero then 1#32 else 0#32) ∧
          (EdExtValid (edExtOfBytes p.toList) → (sf.readReg64 .x0).setWidth 32 =
            if edSmul edOrderL (edExtToAffine (edExtOfBytes p.toList)) == edZero then 1#32 else 0#32)⌝ ∗
          ((basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
            (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (pA ↦ₛ p.toList) ∗ stackAt s0.sp 4848 ∗ R) :=
        Satisfies.mono (by sep_entail) hpost
      rw [satisfies_pure_sepConj] at hp1; obtain ⟨⟨hr1, hr2⟩, hp1⟩ := hp1
      dsimp only [withRoDataSep, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore, dalekTorsionFreeBool]
      exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure (And.intro htr (And.intro hr1 hr2)) hp1)
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [basepointOrderBytes_length]; decide) (fun _ h => h.ro_basepoint_order)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51OneBytes_length]; decide) (fun _ h => h.ro_fe51_one)).trans
        (specSimulates_absorb_ro1 (by rw [fe51EdwardsD2Bytes_length]; decide) (fun _ h => h.ro_fe51_edwards_d2))))

private theorem dalekTorsionFreeBridge :
    DalekBlockBridge 19 edwardsPointIsTorsionFreeU32Spec (keepsFs (dalekTorsionFreeSpec 4848 (2 ^ 53))) dalekTorsionFreeFallback :=
  { blk_ok := edwards_point_is_torsion_free_u32_ok
    sim := fun mpl => specSimulates_keepsFs (torsionFree_sim_master mpl)
    m_pre_rw := fun ⟨_, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_pointsToBytes _ _))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, _⟩ _ _ hh => boundedHeapIntervals_mono (by decide : (0 + 1) + 1 ≤ 6) (Nat.le_refl _)
      (boundedHeapIntervals_sepConj
        (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
          (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide)))
        (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := by
      intro ⟨pA, p⟩ s0 sf h hh
      dsimp only [keepsFs, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hh
      generalize dalekTorsionFreeBool p = b at hh
      exact rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_pointsToBytes _ _))
          (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekTorsionFree_post_fsT 4848)
    post_fsT := dalekTorsionFree_post_fsT 4848
    fb_pres := dalekTorsionFreeFallback_preserved
    fb_ok := dalekTorsionFreeFallback_ok }

@[expose] noncomputable def dalekTorsionFreeGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 19 (keepsFs (dalekTorsionFreeSpec 4848 (2 ^ 53))) dalekTorsionFreeFallback
theorem dalekTorsionFreeGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekTorsionFreeGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekTorsionFreeBridge s0
theorem dalekTorsionFreeGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekTorsionFreeGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 19 _ _
theorem dalekTorsionFreeGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (bound : Nat := 2 ^ 53)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 53 := by decide) :
    HookOk (dalekTorsionFreeGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekTorsionFreeSpec stk bound))) :=
  dalekGhost_lift_ok dalekTorsionFreeBridge ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekTorsionFree_bound_sim stk hb)))
theorem dalekTorsionFreeGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (bound : Nat := 2 ^ 53)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 53 := by decide) :
    HookOk (dalekTorsionFreeGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekTorsionFreeSpec stk bound)))) :=
  dalekGhost_lift_keepsFs_ok dalekTorsionFreeBridge (specSimulates_keepsFs
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekTorsionFree_bound_sim stk hb)))
theorem dalekTorsionFreeGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (bound : Nat := 2 ^ 53)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 53 := by decide) :
    HookOk (dalekTorsionFreeGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekTorsionFreeSpec stk bound))) :=
  dalekGhost_lift_withAlloc_ok dalekTorsionFreeBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekTorsionFree_bound_sim stk hb)))
theorem dalekTorsionFreeGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (bound : Nat := 2 ^ 53)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) (hb : bound ≤ 2 ^ 53 := by decide) :
    HookOk (dalekTorsionFreeGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekTorsionFreeSpec stk bound))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekTorsionFreeBridge A lim ((specSimulates_of_keepsFs _).trans
    ((specSimulates_withStack_mono _ hlo hhi).trans (dalekTorsionFree_bound_sim stk hb)))
theorem dalekTorsionFreeGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsTorsionFreeSymCli = dalekMpl.base 19)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsTorsionFreeSymCli (fun _ => True) (dalekTorsionFreeGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsTorsionFreeSymCli dalekTorsionFreeBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

/-! ### 2.5 `B17` (`lsDsmbSymCli`, stack `5008` B) -/

private theorem dsmb_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (vartimeDoubleScalarMulBasepointSpec mpl))
      (withRoOk (DalekCliRoOk mpl) (dalekDsmbSpec 5008)) := by
  have hcore : SpecSimulates (Spec.withTraceEq (vartimeDoubleScalarMulBasepointSpec mpl))
      (withRoDataSep (odd_multiples_basepoint mpl) oddMultiplesBasepointBytes
        (withRoDataSep (fe51_one mpl) fe51OneBytes
          (withRoDataSep (fe51_edwards_d2 mpl) fe51EdwardsD2Bytes (dalekDsmbSpec 5008)))) := by
    refine SpecSimulates.of_map fun ⟨aA, a, pA, p, bA, b, ret⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekDsmbSpec, withStack, dalekDsmbCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = aA ∧ s0.readReg64 .x1 = pA ∧ s0.readReg64 .x2 = bA ∧
          s0.readReg64 .x8 = ret ∧ fe51Point4Bounded p.toList (2 ^ 52)⌝ ∗
        ((odd_multiples_basepoint mpl ↦ᵣ oddMultiplesBasepointBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
          (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗
          (bA ↦ₛ b.toList) ∗ memRegion ret 160 ∗ stackAt s0.sp 5008 ∗ R) := Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx1, hx2, hx8, hpb⟩, hpre⟩ := hpre1
    rw [memRegion_eq_exists_bytes ret 160 (by decide), stackAt_eq_stackFrameAt s0.sp 5008 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre; obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 160⌝ ∗ ((odd_multiples_basepoint mpl ↦ᵣ oddMultiplesBasepointBytes) ∗
        (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (aA ↦ₛ a.toList) ∗
        (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 5008 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, aA, pA, bA, out_bs, a.toList, p.toList, b.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, vartimeDoubleScalarMulBasepointSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hx1, hx2, hout_len, a.2, hpb, b.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, vartimeDoubleScalarMulBasepointSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 5008 = stackAt s0.sp 5008 by unfold stackFrame; rw [hcc.1]] at hpost
      dsimp only [withRoDataSep, dalekDsmbSpec, withStack, dalekDsmbCore]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨res_bs, hpost⟩ := hpost; exact ⟨res_bs, Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr hpost)⟩
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [oddMultiplesBasepointBytes_length]; decide) (fun _ h => h.ro_odd_multiples_basepoint)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51OneBytes_length]; decide) (fun _ h => h.ro_fe51_one)).trans
        (specSimulates_absorb_ro1 (by rw [fe51EdwardsD2Bytes_length]; decide) (fun _ h => h.ro_fe51_edwards_d2))))

private theorem dalekDsmbBridge :
    DalekBlockBridge 17 vartimeDoubleScalarMulBasepointSpec (keepsFs (dalekDsmbSpec 5008)) dalekDsmbFallback :=
  { blk_ok := vartime_double_scalar_mul_basepoint_ok
    sim := fun mpl => specSimulates_keepsFs (dsmb_sim_master mpl)
    m_pre_rw := fun ⟨_, _, _, _, _, _, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
            (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
              (fun _ => rwOnlyHeap_memRegion _ _)))))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, _, _, _, _, _, _⟩ _ _ hh =>
      boundedHeapIntervals_mono (by decide : (0 + (1 + (1 + (1 + 1)))) + 1 ≤ 6) (Nat.le_refl _)
        (boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj
              (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide))
              (fun _ => boundedHeapIntervals_sepConj
                (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide))
                (fun _ => boundedHeapIntervals_sepConj
                  (fun _ => boundedHeapIntervals_pointsToBytes _ _ (by rw [List.Vector.toList_length]; decide))
                  (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))))
          (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _, _, _, _, _⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
            (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
              (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
                (fun _ => rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
                  (fun _ => rwOnlyHeap_pointsToBytes _ _)))))))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekDsmb_post_fsT 5008)
    post_fsT := dalekDsmb_post_fsT 5008
    fb_pres := dalekDsmbFallback_preserved
    fb_ok := dalekDsmbFallback_ok 5008 }

@[expose] noncomputable def dalekDsmbGhostLs [LibsignalPlacement] (dalekMpl : MultiPlacement) : State → State :=
  dalekBlockGhost dalekMpl 17 (keepsFs (dalekDsmbSpec 5008)) dalekDsmbFallback
theorem dalekDsmbGhostLs_vmPreserved_and_nonSyscall [LibsignalPlacement] (dalekMpl : MultiPlacement) (s0 : State) :
    let sf := dalekDsmbGhostLs dalekMpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  dalekBlockGhost_vmPreserved_and_nonSyscall dalekDsmbBridge s0
theorem dalekDsmbGhostLs_fsT [LibsignalPlacement] (dalekMpl : MultiPlacement) :
    HookFsTraced IsFsC (dalekDsmbGhostLs dalekMpl) := dalekBlockGhost_fsT dalekMpl 17 _ _
theorem dalekDsmbGhostLs_at_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (hlo : 5008 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekDsmbGhostLs dalekMpl) (withLsRet (withVmPreserved (dalekDsmbSpec stk))) :=
  dalekGhost_lift_ok dalekDsmbBridge ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekDsmbGhostLs_keepsFs_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    (stk : Nat := dalekHookStack) (hlo : 5008 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekDsmbGhostLs dalekMpl) (withLsRet (withVmPreserved (keepsFs (dalekDsmbSpec stk)))) :=
  dalekGhost_lift_keepsFs_ok dalekDsmbBridge (specSimulates_keepsFs (specSimulates_withStack_mono _ hlo hhi))
theorem dalekDsmbGhostLs_withAlloc_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (hlo : 5008 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekDsmbGhostLs dalekMpl) (withLsRet (withAlloc A lim (dalekDsmbSpec stk))) :=
  dalekGhost_lift_withAlloc_ok dalekDsmbBridge A lim ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekDsmbGhostLs_withAlloc_ls_ok [LibsignalPlacement] (dalekMpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := dalekHookStack) (hlo : 5008 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (dalekDsmbGhostLs dalekMpl) (withAlloc A lim (withLsRet (dalekDsmbSpec stk))) :=
  dalekGhost_lift_withAlloc_ls_ok dalekDsmbBridge A lim ((specSimulates_of_keepsFs _).trans (specSimulates_withStack_mono _ hlo hhi))
theorem dalekDsmbGhostLs_rowReplayOn [LibsignalPlacement] (mpl mmpl dalekMpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State)) (hpl : DalekActivePlaceable dalekMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDsmbSymCli = dalekMpl.base 17)
    (hInvDalek : ∀ u : State, InvS u → dalekActiveInvMem dalekMpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → dalekActiveKeep dalekMpl lr = false)
    (hRealDalekNoExt : ∀ (W : CliHooks) {pc : BitVec 64}, dalekActiveKeep dalekMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsDsmbSymCli (fun _ => True) (dalekDsmbGhostLs dalekMpl) :=
  dalekBlockGhost_rowReplayOn mpl mmpl dalekMpl InvS EG lsDsmbSymCli dalekDsmbBridge
    hpl hTargetEq hInvDalek hInvKeep hKeep hRealDalekNoExt

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks
