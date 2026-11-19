/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Tight-Keep `SampleNTT` Non-Visitation for the 6 `dalekCliMultiLib` & 2 `mlkemPk` Rows (`ElfSampleNttStuckDivergeExtraTightDalek`)

Discharges `StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)`
for the 8 Dalek / ML-KEM-pk tight rows:
`lsScalarModSym`, `lsScalarWideSym`, `lsToEdwardsSym`, `lsCompressSym`, `lsTorsionFreeSym`,
`lsDsmbSym`, `lsMlkemPk1Sym`, and `lsMlkemPk2Sym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightDalek

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj (MultiPlacement)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open VerifiedLibraries.Common (EdPoint edExtZero edOrderL edSmul edZero edExtToAffine)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsCompressSym lsDsmbSym lsMlkemPk1Sym lsMlkemPk2Sym
   lsScalarModSym lsScalarWideSym lsToEdwardsSym lsTorsionFreeSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (inputAfter withStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk (mlkemPk1Words mlkemPk2Words)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk
  (edwards_point_compress_ok edwards_point_is_torsion_free_u32_ok
   montgomery_point_to_edwards_ok scalar_from_bytes_mod_order_ok
   scalar_from_bytes_mod_order_wide_ok vartime_double_scalar_mul_basepoint_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase
  (basepointOrderBytes basepoint_order fe51EdwardsD2Bytes fe51EdwardsDBytes fe51MinusOneBytes
   fe51OneBytes fe51SqrtM1Bytes fe51_edwards_d fe51_edwards_d2 fe51_minus_one fe51_one
   fe51_sqrt_m1 oddMultiplesBasepointBytes odd_multiples_basepoint sc52LBytes sc52RRBytes
   sc52_l sc52_rr)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges
  (DalekCliRoOk dalekCliMultiLib_externAt_none dalekScalarModVec dalekScalarWideVec
   specSimulates_absorb_roDataSep specSimulates_keepsFs withRoOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
  (edExtOfBytes edPointEq edVarBaseMul edwardsPointCompressSpec fe51Point4Bounded
   montToEdwards montgomeryPointToEdwardsSpec vartimeDoubleScalarMulBasepointSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks
  (dalekCompressCore dalekCompressFallback dalekCompressFallback_ok
   dalekCompressFallback_preserved dalekCompressSpec dalekCompressVec dalekCompress_post_fsT
   dalekDsmbCore dalekDsmbFallback dalekDsmbFallback_ok dalekDsmbFallback_preserved dalekDsmbSpec
   dalekDsmb_post_fsT dalekMontToEdCore dalekMontToEdFallback dalekMontToEdFallback_ok
   dalekMontToEdFallback_preserved dalekMontToEdSpec dalekMontToEd_post_fsT dalekOptionEdwardsAt
   dalekPureLeafCore dalekPureLeaf_fallback_ok dalekPureLeaf_post_fsT dalekScalarModFallback
   dalekScalarModFallback_preserved dalekScalarModSpec dalekScalarWideFallback
   dalekScalarWideFallback_preserved dalekScalarWideSpec dalekTorsionFreeBool
   dalekTorsionFreeCore dalekTorsionFreeFallback dalekTorsionFreeFallback_ok
   dalekTorsionFreeFallback_preserved dalekTorsionFreeSpec dalekTorsionFree_post_fsT)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
  (scalarFromBytesModOrderSpec scalarFromBytesModOrderWideSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree
  (edwardsPointIsTorsionFreeU32Spec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (EdExtValid)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality
  (BoundedHeapIntervals RwOnlyHeap boundedHeapIntervals_memRegion boundedHeapIntervals_mono
   boundedHeapIntervals_pointsToBytes boundedHeapIntervals_pure boundedHeapIntervals_sepConj
   boundedHeapIntervals_stackAt dalekActiveGuard dalekActiveGuard_stripS_setPC
   dalekActiveInvMem dalekActiveInvMem_stripExecOutside dalekActiveKeep
   dalekActive_subroutineOk_guarded_withVmPreserved rwOnlyHeap_memRegion rwOnlyHeap_pointsTo64
   rwOnlyHeap_pointsToBytes rwOnlyHeap_pure rwOnlyHeap_sepConj rwOnlyHeap_sepExists
   rwOnlyHeap_stackAt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks
  (DalekBlockBridge dalekBlockGhost dalekBlockGhost_keepLr_false_of_noException
   dalekCompressGhostLs dalekDsmbGhostLs dalekMontToEdGhostLs dalekScalarModGhostLs
   dalekScalarWideGhostLs dalekTorsionFreeGhostLs)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
  (basepointOrderBytes_length fe51EdwardsD2Bytes_length fe51EdwardsDBytes_length
   fe51MinusOneBytes_length fe51OneBytes_length fe51SqrtM1Bytes_length
   oddMultiplesBasepointBytes_length sc52LBytes_length sc52RRBytes_length)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates withRoDataSep)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecPreservesFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_lsmpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook
  (steps_mlkemPk1_of_hasWords steps_mlkemPk2_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook
  (c2DalekMpl c2DalekMpl_invMem_of_f3CodeInv c2DalekMpl_keep_lr_false c2DalekMpl_realNoExt
   c2MlkemPk1Addr c2MlkemPk2Addr resolve_compress_eq resolve_dsmb_eq resolve_mlkemPk1_eq
   resolve_mlkemPk2_eq resolve_scalarMod_eq resolve_scalarWide_eq resolve_toEdwards_eq
   resolve_torsionFree_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (linkedCallHookG_activeRealPre_of_noException linkedCallHookG_visitedIn withStateGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (specPreservesFsTrace_withLsRet specStripSInvariant_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg_externAt_none emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (subroutine_ok_withLsRet withLsRet withLsRet_frameLeft withLsRet_outcome_setPC
   withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (isLinkedPanicAddr keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
  (c2S5Addrs externAt?_s5TrapExt_eq_of_not_mem not_mem_s5_of_not_mem_c2S5Addrs
   s5TrapExt setPC_eq_self_of_pc_eq stepsStrictAvoid_of_s5Trap
   stepsStrictAvoid_s5_of_visitedIn_all_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (mlkemPk1Hook mlkemPk2Hook)

/-! ## 1. Generic `dalekBlockGhost` → `StepsStrictAvoid` Engine -/

set_option maxRecDepth 400000 in
private theorem c2DalekActiveKeep_s5_all_false :
    (c2S5Addrs.all fun p => !(dalekActiveKeep c2DalekMpl p)) = true := by
  decide +kernel

private theorem dalekBlockProgram_svc (dalekMpl : MultiPlacement) (j : Nat) :
    (dalekCliMultiLib.blockProgram dalekMpl j).svc = Syscall.standard := rfl

private theorem dalekSubroutineOk_guarded_withLsRet [LibsignalPlacement] {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback) (dalekMpl : MultiPlacement) :
    subroutine_ok (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j)
      (withStateGuard (dalekActiveGuard dalekMpl) (withLsRet master)) := by
  have hVm : subroutine_ok (dalekCliMultiLib.blockProgram dalekMpl j) (dalekMpl.base j)
      (withStateGuard (dalekActiveGuard dalekMpl) (withVmPreserved master)) :=
    dalekActive_subroutineOk_guarded_withVmPreserved B.hj_act dalekMpl B.blk_ok B.blk_pan B.blk_ex
      B.blk_oom B.blk_pre_mem B.blk_post_mem B.sim B.m_pan B.m_ex B.m_oom B.m_pre_mem B.m_post_mem
      B.m_pre_rw B.m_pre_bdd B.m_post_rw
  have hDrop : SpecSimulates
      (withStateGuard (dalekActiveGuard dalekMpl) (withVmPreserved master))
      (withStateGuard (dalekActiveGuard dalekMpl) master) :=
    fun x R s0 hpre => ⟨x, R, hpre, fun _ hout => by
      rcases hout with ⟨hret, hcc, hpost⟩ | h
      · dsimp only [withStateGuard, withVmPreserved] at hpost ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
        exact Or.inl ⟨hret, hcc, hpost.2⟩
      · exact Or.inr h⟩
  have hLs := subroutine_ok_withLsRet (SpecSimulates.subroutine_ok hDrop hVm)
  have hComm :
      withLsRet (withStateGuard (dalekActiveGuard dalekMpl) master) =
        withStateGuard (dalekActiveGuard dalekMpl) (withLsRet master) :=
    withLsRet_frameLeft master (fun _ s => ⌜dalekActiveGuard dalekMpl s⌝) master.post
  rwa [hComm] at hLs

private theorem dalekBlockGhost_avoidS5 [LibsignalPlacement]
    {mmpl : MultiPlacement} {sym : String} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : DalekBlockBridge j blockSpec master fallback)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hTargetEq : libsignalSessionLib.resolve lsmpl sym = c2DalekMpl.base j)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hnoex : ∀ msg, (dalekBlockGhost c2DalekMpl j master fallback u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekBlockGhost c2DalekMpl j master fallback u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hInvM : dalekActiveInvMem c2DalekMpl u.mem := c2DalekMpl_invMem_of_f3CodeInv hLs hinv
  have hGu : dalekActiveGuard c2DalekMpl u := hInvM
  have hActPre := linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr_out : dalekActiveKeep c2DalekMpl (u.readReg64 .lr) = false :=
    dalekBlockGhost_keepLr_false_of_noException (c2DalekMpl_keep_lr_false hLs) hnoex
  have hCodeSub :
      (dalekCliMultiLib.blockProgram c2DalekMpl j).CodeLoaded
        (stripExecOutside (dalekActiveKeep c2DalekMpl) u.mem) :=
    (dalekActiveInvMem_stripExecOutside hInvM).2.1 j B.hj_act
  obtain ⟨hvis, _⟩ := linkedCallHookG_visitedIn
    emptyStdProg_svc
    (dalekBlockProgram_svc c2DalekMpl j)
    (fun pc _ => emptyStdProg_externAt_none pc)
    (dalekCliMultiLib_externAt_none c2DalekMpl j B.hj (fun _ => none))
    (fun s0 hFr hG => dalekActiveGuard_stripS_setPC c2DalekMpl (c2DalekMpl.base j) s0 hFr hG)
    (dalekSubroutineOk_guarded_withLsRet B c2DalekMpl)
    (specStripSInvariant_withLsRet (B.strip_inv (dalekActiveKeep c2DalekMpl)))
    (specPreservesFsTrace_withLsRet B.fsT)
    (withLsRet_pre_setPC B.pre_pc)
    (withLsRet_outcome_setPC B.out_pc)
    hGu hActPre hfr hlr_out hCodeSub
  rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)] at hvis
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    (fun _ hk => c2DalekMpl_realNoExt hExt W hk)
    c2DalekActiveKeep_s5_all_false
    hvis

/-! ## 2. The 6 `DalekBlockBridge` Witnesses & Per-Row Theorems -/

private theorem satisfies_prepend_pure {m : Memory} {P : Prop} {Q : SepProp}
    (hP : P) (hQ : m ⊨ Q) : m ⊨ ⌜P⌝ ∗ Q :=
  (satisfies_pure_sepConj P Q m).mpr ⟨hP, hQ⟩

private theorem specSimulates_intro_roOk {α β : Type} {RoOk : Memory → Prop}
    {spec₁ : Spec α} {spec₂ : Spec β}
    (h : SpecSimulates spec₁ spec₂) : SpecSimulates spec₁ (withRoOk RoOk spec₂) :=
  fun y R s0 hpre => by
    dsimp only [withRoOk] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact h y R s0 hpre.2

private theorem specSimulates_absorb_ro1 {α : Type} {RoOk : Memory → Prop}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {spec : Spec α}
    (hlen : bytes.length ≤ 2 ^ 64) (hro : ∀ m, RoOk m → RoDataAt m addr bytes) :
    SpecSimulates (withRoOk RoOk (withRoDataSep addr bytes spec)) (withRoOk RoOk spec) := by
  have hcomm : SpecSimulates (withRoOk RoOk (withRoDataSep addr bytes spec))
      (withRoDataSep addr bytes (withRoOk RoOk spec)) :=
    fun x R s0 hpre => ⟨x, R,
      by dsimp only [withRoDataSep, withRoOk] at hpre ⊢; exact Satisfies.mono (by sep_entail) hpre,
      fun _ hout => hout⟩
  exact hcomm.trans (specSimulates_absorb_roDataSep hlen hro)

private theorem specPreservesFsTrace_of_post {α : Type} {master : Spec α}
    (hpost_fsT : ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ master.post x s0 sf ∗ R → sf.fs = s0.fs ∧ sf.trace = s0.trace)
    (hpan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl) : SpecPreservesFsTrace master :=
  fun x R s0 sf hout => by
    rcases hout with ⟨_, _, hp⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨hfs, htr⟩ := hpost_fsT x R s0 sf hp
      exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
    · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem pureLeaf_pre_rw {m n : Nat} (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n)
    (stk : Nat) (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).pre x s).holds h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj
    (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
        (fun _ => rwOnlyHeap_memRegion _ _)))
    (fun _ => rwOnlyHeap_stackAt _ _) hh

private theorem pureLeaf_pre_bdd {m n : Nat} (hm : m ≤ 65536) (hn : n ≤ 65536)
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) {stk : Nat} (hstk : stk ≤ 65536)
    (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).pre x s).holds h) :
    BoundedHeapIntervals 6 65536 h :=
  boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
    (boundedHeapIntervals_sepConj
      (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
        (fun _ => boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_pointsToBytes _ _
            (by rw [List.Vector.toList_length]; exact hm))
          (fun _ => boundedHeapIntervals_memRegion _ _ hn)))
      (fun _ => boundedHeapIntervals_stackAt _ _ hstk) hh)

private theorem pureLeaf_post_rw {m n : Nat} (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n)
    (stk : Nat) (x : BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) (s0 sf : State) (h : Heap)
    (hh : ((keepsFs (withStack (dalekPureLeafCore f false) stk)).post x s0 sf).holds h) :
    RwOnlyHeap h :=
  rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
    (fun _ => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
          (fun _ => rwOnlyHeap_pointsToBytes _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _)) hh

private theorem scalarMod_sim_master :
    SpecSimulates (Spec.withTraceEq scalarFromBytesModOrderSpec)
      (dalekScalarModSpec 208 false) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [dalekScalarModSpec, withStack, dalekPureLeafCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 208 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre; simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (inA ↦ₛ v.toList) ⌜out_bs.length = 32⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
  · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
    rw [show stackFrame sf 208 = stackAt s0.sp 208 by unfold stackFrame; rw [hcc.1]] at hpost
    simp only [dalekScalarModSpec, withStack, dalekPureLeafCore, inputAfter, Bool.false_eq_true,
      ↓reduceIte, dalekScalarModVec, List.Vector.toList, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

private theorem dalekScalarModBridge :
    DalekBlockBridge 1 (fun _ => scalarFromBytesModOrderSpec)
      (keepsFs (dalekScalarModSpec 208 false)) dalekScalarModFallback :=
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
      (withRoDataSep (sc52_l mpl) sc52LBytes
        (withRoDataSep (sc52_rr mpl) sc52RRBytes (dalekScalarWideSpec 448 false))) := by
    refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekScalarWideSpec, withStack, dalekPureLeafCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = inA ∧ s0.readReg64 .x8 = ret⌝ ∗
        ((sc52_l mpl ↦ᵣ sc52LBytes) ∗ (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗
          (inA ↦ₛ v.toList) ∗ memRegion ret 32 ∗ stackAt s0.sp 448 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre1
    rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 448 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 32⌝ ∗
        ((sc52_l mpl ↦ᵣ sc52LBytes) ∗ (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗
          (inA ↦ₛ v.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 448 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderWideSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
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
    DalekBlockBridge 2 scalarFromBytesModOrderWideSpec
      (keepsFs (dalekScalarWideSpec 448 false)) dalekScalarWideFallback :=
  { blk_ok := scalar_from_bytes_mod_order_wide_ok
    sim := fun mpl => specSimulates_keepsFs (scalarWide_sim_master mpl)
    m_pre_rw := pureLeaf_pre_rw dalekScalarWideVec 448
    m_pre_bdd := pureLeaf_pre_bdd (by decide) (by decide) dalekScalarWideVec (by decide)
    m_post_rw := pureLeaf_post_rw dalekScalarWideVec 448
    fsT := specPreservesFsTrace_of_post (dalekPureLeaf_post_fsT dalekScalarWideVec 448)
    post_fsT := dalekPureLeaf_post_fsT dalekScalarWideVec 448
    fb_pres := dalekScalarWideFallback_preserved
    fb_ok := dalekPureLeaf_fallback_ok (by decide) dalekScalarWideVec 448 }

private theorem rwOnlyHeap_dalekOptionEdwardsAt (r : BitVec 64) :
    ∀ (opt : Option EdPoint) (h : Heap), (dalekOptionEdwardsAt r opt).holds h → RwOnlyHeap h
  | none, _, hh =>
    rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsTo64 _ _) (fun _ => rwOnlyHeap_memRegion _ _) hh
  | some _, _, hh =>
    rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsTo64 _ _)
        (fun _ => rwOnlyHeap_pointsToBytes _ _))) hh

private theorem montToEd_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (montgomeryPointToEdwardsSpec mpl))
      (withRoOk (DalekCliRoOk mpl) (dalekMontToEdSpec 2576)) := by
  have hcore : SpecSimulates (Spec.withTraceEq (montgomeryPointToEdwardsSpec mpl))
      (withRoDataSep (fe51_minus_one mpl) fe51MinusOneBytes
        (withRoDataSep (fe51_edwards_d mpl) fe51EdwardsDBytes
          (withRoDataSep (fe51_sqrt_m1 mpl) fe51SqrtM1Bytes (dalekMontToEdSpec 2576)))) := by
    refine SpecSimulates.of_map fun ⟨uA, u, sign, ret⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekMontToEdSpec, withStack, dalekMontToEdCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = uA ∧ (s0.readReg64 .x1).setWidth 8 = sign ∧
          s0.readReg64 .x8 = ret⌝ ∗
        ((fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗ (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
          (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗ (uA ↦ₛ u.toList) ∗
          memRegion ret 168 ∗ stackAt s0.sp 2576 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx1, hx8⟩, hpre⟩ := hpre1
    have hx1' : BitVec.truncate 8 (s0.readReg32 .x1) = sign := by
      simp only [State.readReg32, BitVec.truncate_eq_setWidth,
        BitVec.setWidth_setWidth_of_le (s0.readReg64 .x1) (by decide : 8 ≤ 32)]
      exact hx1
    rw [memRegion_eq_exists_bytes ret 168 (by decide), stackAt_eq_stackFrameAt s0.sp 2576 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 168⌝ ∗
        ((fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗ (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
          (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗ (uA ↦ₛ u.toList) ∗
          (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 2576 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, uA, sign, out_bs, u.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, montgomeryPointToEdwardsSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hx1', hout_len, u.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, montgomeryPointToEdwardsSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 2576 = stackAt s0.sp 2576 by unfold stackFrame; rw [hcc.1]] at hpost
      dsimp only [withRoDataSep, dalekMontToEdSpec, withStack, dalekMontToEdCore]
      rcases hres : montToEdwards u.toList (sign.toNat % 2) with _ | P
      · rw [hres] at hpost
        simp only [dalekOptionEdwardsAt, sepExists_sepConj_left, sepExists_sepConj_right,
          satisfies_sepExists] at hpost ⊢
        obtain ⟨pad_bs, hpost⟩ := hpost
        have hp1 : sf.mem ⊨ ⌜pad_bs.length = 160⌝ ∗
            (((ret + 8#64) ↦ₛ pad_bs) ∗ (ret ↦₆₄ 0#64) ∗ (uA ↦ₛ u.toList) ∗
              (fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗ (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
              (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗ stackAt s0.sp 2576 ∗ R) :=
          Satisfies.mono (by sep_entail) hpost
        rw [satisfies_pure_sepConj] at hp1; obtain ⟨hpad_len, hp1⟩ := hp1
        exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr
          (Satisfies.mono (sepConj_mono (pointsToBytes_entails_memRegion_of_length hpad_len)
            (Entails.refl _)) hp1))
      · rw [hres] at hpost
        simp only [dalekOptionEdwardsAt, sepExists_sepConj_left, sepExists_sepConj_right,
          satisfies_sepExists] at hpost ⊢
        obtain ⟨pt_bs, hpost⟩ := hpost
        exact ⟨pt_bs, Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr hpost)⟩
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [fe51MinusOneBytes_length]; decide)
        (fun _ h => h.ro_fe51_minus_one)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51EdwardsDBytes_length]; decide)
          (fun _ h => h.ro_fe51_edwards_d)).trans
        (specSimulates_absorb_ro1 (by rw [fe51SqrtM1Bytes_length]; decide)
          (fun _ h => h.ro_fe51_sqrt_m1))))

private theorem dalekMontToEdBridge :
    DalekBlockBridge 8 montgomeryPointToEdwardsSpec
      (keepsFs (dalekMontToEdSpec 2576)) dalekMontToEdFallback :=
  { blk_ok := montgomery_point_to_edwards_ok
    sim := fun mpl => specSimulates_keepsFs (montToEd_sim_master mpl)
    m_pre_rw := fun ⟨_, _, _, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
          (fun _ => rwOnlyHeap_memRegion _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, u, _, _⟩ _ _ hh =>
      boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
        (boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj
              (fun _ => boundedHeapIntervals_pointsToBytes _ _
                (by rw [List.Vector.toList_length]; decide))
              (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))
          (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _, ret⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
            (rwOnlyHeap_dalekOptionEdwardsAt ret _)))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekMontToEd_post_fsT 2576)
    post_fsT := dalekMontToEd_post_fsT 2576
    fb_pres := dalekMontToEdFallback_preserved
    fb_ok := dalekMontToEdFallback_ok 2576 }

private theorem compress_sim_master :
    SpecSimulates (Spec.withTraceEq edwardsPointCompressSpec)
      (dalekCompressSpec 1552 false (2 ^ 54)) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [dalekCompressSpec, withStack, dalekCompressCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hvb⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide), stackAt_eq_stackFrameAt s0.sp 1552 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  have hpre2 : s0.mem ⊨ ⌜out_bs.length = 32⌝ ∗
      ((inA ↦ₛ v.toList) ∗ (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 1552 ∗ R) :=
    Satisfies.mono (by sep_entail) hpre
  rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
  refine ⟨(ret, inA, out_bs, v.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
  · dsimp only [Spec.withTraceEq, edwardsPointCompressSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, hvb⟩, Satisfies.mono (by sep_entail) hpre⟩
  · dsimp only [Spec.withTraceEq, edwardsPointCompressSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
    rw [show stackFrame sf 1552 = stackAt s0.sp 1552 by unfold stackFrame; rw [hcc.1]] at hpost
    simp only [dalekCompressSpec, withStack, dalekCompressCore, inputAfter, Bool.false_eq_true,
      ↓reduceIte, dalekCompressVec, List.Vector.toList, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

private theorem dalekCompressBridge :
    DalekBlockBridge 14 (fun _ => edwardsPointCompressSpec)
      (keepsFs (dalekCompressSpec 1552 false (2 ^ 54))) dalekCompressFallback :=
  { blk_ok := edwards_point_compress_ok
    sim := fun _ => specSimulates_intro_roOk (specSimulates_keepsFs compress_sim_master)
    m_pre_rw := fun ⟨_, _, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
          (fun _ => rwOnlyHeap_memRegion _ _)))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, _, _⟩ _ _ hh =>
      boundedHeapIntervals_mono (by decide : (0 + (1 + 1)) + 1 ≤ 6) (Nat.le_refl _)
        (boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj
              (fun _ => boundedHeapIntervals_pointsToBytes _ _
                (by rw [List.Vector.toList_length]; decide))
              (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))
          (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
            (fun _ => rwOnlyHeap_pointsToBytes _ _)))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekCompress_post_fsT 1552)
    post_fsT := dalekCompress_post_fsT 1552
    fb_pres := dalekCompressFallback_preserved
    fb_ok := dalekCompressFallback_ok }

private theorem torsionFree_sim_master (mpl : MultiPlacement) :
    SpecSimulates (Spec.withTraceEq (edwardsPointIsTorsionFreeU32Spec mpl))
      (withRoOk (DalekCliRoOk mpl) (dalekTorsionFreeSpec 4848 (2 ^ 53))) := by
  have hcore : SpecSimulates (Spec.withTraceEq (edwardsPointIsTorsionFreeU32Spec mpl))
      (withRoDataSep (basepoint_order mpl) basepointOrderBytes
        (withRoDataSep (fe51_one mpl) fe51OneBytes
          (withRoDataSep (fe51_edwards_d2 mpl) fe51EdwardsD2Bytes
            (dalekTorsionFreeSpec 4848 (2 ^ 53))))) := by
    refine SpecSimulates.of_map fun ⟨pA, p⟩ R s0 hpre => ?_
    dsimp only [withRoDataSep, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hpre
    have hpre1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = pA ∧ fe51Point4Bounded p.toList (2 ^ 53)⌝ ∗
        ((basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
          (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (pA ↦ₛ p.toList) ∗
          stackAt s0.sp 4848 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hpb⟩, hpre⟩ := hpre1
    rw [stackAt_eq_stackFrameAt s0.sp 4848 (by decide)] at hpre
    refine ⟨(pA, p.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, edwardsPointIsTorsionFreeU32Spec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hpb⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, edwardsPointIsTorsionFreeU32Spec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 4848 = stackAt s0.sp 4848 by unfold stackFrame; rw [hcc.1]] at hpost
      have hp1 : sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 =
          (if edPointEq (edVarBaseMul p.toList basepointOrderBytes) edExtZero then 1#32 else 0#32) ∧
          (EdExtValid (edExtOfBytes p.toList) → (sf.readReg64 .x0).setWidth 32 =
            if edSmul edOrderL (edExtToAffine (edExtOfBytes p.toList)) == edZero then 1#32 else 0#32)⌝ ∗
          ((basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
            (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (pA ↦ₛ p.toList) ∗
            stackAt s0.sp 4848 ∗ R) :=
        Satisfies.mono (by sep_entail) hpost
      rw [satisfies_pure_sepConj] at hp1; obtain ⟨⟨hr1, hr2⟩, hp1⟩ := hp1
      dsimp only [withRoDataSep, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore,
        dalekTorsionFreeBool]
      exact Satisfies.mono (by sep_entail)
        (satisfies_prepend_pure (And.intro htr (And.intro hr1 hr2)) hp1)
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [basepointOrderBytes_length]; decide)
        (fun _ h => h.ro_basepoint_order)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51OneBytes_length]; decide)
          (fun _ h => h.ro_fe51_one)).trans
        (specSimulates_absorb_ro1 (by rw [fe51EdwardsD2Bytes_length]; decide)
          (fun _ h => h.ro_fe51_edwards_d2))))

private theorem dalekTorsionFreeBridge :
    DalekBlockBridge 19 edwardsPointIsTorsionFreeU32Spec
      (keepsFs (dalekTorsionFreeSpec 4848 (2 ^ 53))) dalekTorsionFreeFallback :=
  { blk_ok := edwards_point_is_torsion_free_u32_ok
    sim := fun mpl => specSimulates_keepsFs (torsionFree_sim_master mpl)
    m_pre_rw := fun ⟨_, _⟩ _ _ hh => rwOnlyHeap_sepConj
      (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_pointsToBytes _ _))
      (fun _ => rwOnlyHeap_stackAt _ _) hh
    m_pre_bdd := fun ⟨_, _⟩ _ _ hh =>
      boundedHeapIntervals_mono (by decide : (0 + 1) + 1 ≤ 6) (Nat.le_refl _)
        (boundedHeapIntervals_sepConj
          (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_pointsToBytes _ _
              (by rw [List.Vector.toList_length]; decide)))
          (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := by
      intro ⟨pA, p⟩ s0 sf h hh
      dsimp only [keepsFs, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hh
      generalize dalekTorsionFreeBool p = b at hh
      exact rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
            (fun _ => rwOnlyHeap_pointsToBytes _ _))
          (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekTorsionFree_post_fsT 4848)
    post_fsT := dalekTorsionFree_post_fsT 4848
    fb_pres := dalekTorsionFreeFallback_preserved
    fb_ok := dalekTorsionFreeFallback_ok }

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
          (bA ↦ₛ b.toList) ∗ memRegion ret 160 ∗ stackAt s0.sp 5008 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨hx0, hx1, hx2, hx8, hpb⟩, hpre⟩ := hpre1
    rw [memRegion_eq_exists_bytes ret 160 (by decide), stackAt_eq_stackFrameAt s0.sp 5008 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    obtain ⟨out_bs, hpre⟩ := hpre
    have hpre2 : s0.mem ⊨ ⌜out_bs.length = 160⌝ ∗
        ((odd_multiples_basepoint mpl ↦ᵣ oddMultiplesBasepointBytes) ∗
          (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗
          (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗
          (ret ↦ₛ out_bs) ∗ stackFrameAt s0.sp 5008 ∗ R) :=
      Satisfies.mono (by sep_entail) hpre
    rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hout_len, hpre⟩ := hpre2
    refine ⟨(ret, aA, pA, bA, out_bs, a.toList, p.toList, b.toList), R, ?_, fun sf _ hcc hpost => ?_⟩
    · dsimp only [Spec.withTraceEq, vartimeDoubleScalarMulBasepointSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hx1, hx2, hout_len, a.2, hpb, b.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · dsimp only [Spec.withTraceEq, vartimeDoubleScalarMulBasepointSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; obtain ⟨htr, hpost⟩ := hpost
      rw [show stackFrame sf 5008 = stackAt s0.sp 5008 by unfold stackFrame; rw [hcc.1]] at hpost
      dsimp only [withRoDataSep, dalekDsmbSpec, withStack, dalekDsmbCore]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨res_bs, hpost⟩ := hpost
      exact ⟨res_bs, Satisfies.mono (by sep_entail) (satisfies_prepend_pure htr hpost)⟩
  exact (specSimulates_intro_roOk hcore).trans
    ((specSimulates_absorb_ro1 (by rw [oddMultiplesBasepointBytes_length]; decide)
        (fun _ h => h.ro_odd_multiples_basepoint)).trans
      ((specSimulates_absorb_ro1 (by rw [fe51OneBytes_length]; decide)
          (fun _ h => h.ro_fe51_one)).trans
        (specSimulates_absorb_ro1 (by rw [fe51EdwardsD2Bytes_length]; decide)
          (fun _ h => h.ro_fe51_edwards_d2))))

private theorem dalekDsmbBridge :
    DalekBlockBridge 17 vartimeDoubleScalarMulBasepointSpec
      (keepsFs (dalekDsmbSpec 5008)) dalekDsmbFallback :=
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
              (fun _ => boundedHeapIntervals_pointsToBytes _ _
                (by rw [List.Vector.toList_length]; decide))
              (fun _ => boundedHeapIntervals_sepConj
                (fun _ => boundedHeapIntervals_pointsToBytes _ _
                  (by rw [List.Vector.toList_length]; decide))
                (fun _ => boundedHeapIntervals_sepConj
                  (fun _ => boundedHeapIntervals_pointsToBytes _ _
                    (by rw [List.Vector.toList_length]; decide))
                  (fun _ => boundedHeapIntervals_memRegion _ _ (by decide))))))
          (fun _ => boundedHeapIntervals_stackAt _ _ (by decide)) hh)
    m_post_rw := fun ⟨_, _, _, _, _, _, _⟩ _ _ _ hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
      (fun _ => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
            (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
              (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes _ _)
                (fun _ => rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj
                  (fun _ => rwOnlyHeap_pure)
                  (fun _ => rwOnlyHeap_pointsToBytes _ _)))))))
        (fun _ => rwOnlyHeap_stackAt _ _)) hh
    fsT := specPreservesFsTrace_of_post (dalekDsmb_post_fsT 5008)
    post_fsT := dalekDsmb_post_fsT 5008
    fb_pres := dalekDsmbFallback_preserved
    fb_ok := dalekDsmbFallback_ok 5008 }

theorem dalekScalarMod_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsScalarModSym)
    (hnoex : ∀ msg, (dalekScalarModGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekScalarModGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekScalarModBridge hLs (resolve_scalarMod_eq hLs) W hpc hnoex hfr hinv

theorem dalekScalarWide_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsScalarWideSym)
    (hnoex : ∀ msg, (dalekScalarWideGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekScalarWideGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekScalarWideBridge hLs (resolve_scalarWide_eq hLs) W hpc hnoex hfr hinv

theorem dalekToEdwards_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsToEdwardsSym)
    (hnoex : ∀ msg, (dalekMontToEdGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekMontToEdGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekMontToEdBridge hLs (resolve_toEdwards_eq hLs) W hpc hnoex hfr hinv

theorem dalekCompress_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsCompressSym)
    (hnoex : ∀ msg, (dalekCompressGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekCompressGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekCompressBridge hLs (resolve_compress_eq hLs) W hpc hnoex hfr hinv

theorem dalekTorsionFree_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsTorsionFreeSym)
    (hnoex : ∀ msg, (dalekTorsionFreeGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekTorsionFreeGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekTorsionFreeBridge hLs (resolve_torsionFree_eq hLs) W hpc hnoex hfr hinv

theorem dalekDsmb_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsDsmbSym)
    (hnoex : ∀ msg, (dalekDsmbGhostLs c2DalekMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (dalekDsmbGhostLs c2DalekMpl u) :=
  dalekBlockGhost_avoidS5 dalekDsmbBridge hLs (resolve_dsmb_eq hLs) W hpc hnoex hfr hinv

/-! ## 3. Straight-Line 2-Instruction `mlkemPk1` & `mlkemPk2` Rows (`Engine B`) -/

private noncomputable def checkPureSubslicePk (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (subProg : Program) : Bool :=
  let off := (subProg.base - f3RxSegBase).toNat
  let subLen := ProofLib.Placed.Split.rLen subProg.code
  Nat.beq (subProg.base.toNat % 4) 0 &&
  Nat.ble (subProg.base.toNat + subLen) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = subProg.base) &&
  Nat.ble (off + subLen) rxLen &&
  (subProg.code == ProofLib.Placed.Split.rTake subLen (ProofLib.Placed.Split.rDrop off rxBytes))

private theorem codeLoaded_of_pureSubslicePk {subProg : Program} {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m)
    (h : checkPureSubslicePk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) subProg = true) :
    subProg.CodeLoaded m := by
  apply codeLoaded_of_checkProgCodeSubslice hRx
  unfold checkPureSubslicePk at h
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rTake_eq,
    ProofLib.Placed.Split.rDrop_eq] at h
  unfold checkProgCodeSubslice
  rwa [f3TrialRxProg_base, f3TrialRxWordTree_eq]

set_option maxRecDepth 2000000 in
private theorem c2MlkemPkSlices_ok :
    (let rxBytes := f3TrialRxWordTree.toBytes
     let rxLen := ProofLib.Placed.Split.rLen rxBytes
     checkPureSubslicePk rxBytes rxLen (pureWordsProg c2MlkemPk1Addr mlkemPk1Words) &&
     checkPureSubslicePk rxBytes rxLen (pureWordsProg c2MlkemPk2Addr mlkemPk2Words)) = true := by
  rfl_kernel

private theorem c2MlkemPk1Slice_ok :
    checkPureSubslicePk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2MlkemPk1Addr mlkemPk1Words) = true := by
  have h := c2MlkemPkSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1

private theorem c2MlkemPk2Slice_ok :
    checkPureSubslicePk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2MlkemPk2Addr mlkemPk2Words) = true := by
  have h := c2MlkemPkSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.2

theorem mlkemPk1_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsMlkemPk1Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemPk1Hook u).status ≠ .Exception msg)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemPk1Hook u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_mlkemPk1_eq hLs
  have hpc' : u.pc = c2MlkemPk1Addr := hpc.trans hRes
  have hk0 : keepLib2Text c2MlkemPk1Addr = true := by decide
  have hk4 : keepLib2Text (c2MlkemPk1Addr + 4#64) = true := by decide
  have hn0 : c2MlkemPk1Addr ∉ c2S5Addrs := by decide
  have hn4 : (c2MlkemPk1Addr + 4#64) ∉ c2S5Addrs := by decide
  have hext0 :
      (cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W).externAt? c2MlkemPk1Addr = none := by
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn0)]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) (by decide)
  have hext4 :
      (cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W).externAt? (c2MlkemPk1Addr + 4#64) = none := by
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn4)]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk4) (by decide)
  have hst := steps_mlkemPk1_of_hasWords
    (P_real := cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W)
    (P_rx := pureWordsProg c2MlkemPk1Addr mlkemPk1Words)
    (codeLoaded_of_pureSubslicePk hinv.rxCode c2MlkemPk1Slice_ok)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    (pureWordsProg_externAt_none _ _ _)
    (pureWordsProg_externAt_none _ _ _)
    hext0 hext4 hrun
  rw [setPC_eq_self_of_pc_eq hpc'] at hst
  exact stepsStrictAvoid_of_s5Trap hExt W hst hnoex

theorem mlkemPk2_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsMlkemPk2Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemPk2Hook u).status ≠ .Exception msg)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemPk2Hook u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_mlkemPk2_eq hLs
  have hpc' : u.pc = c2MlkemPk2Addr := hpc.trans hRes
  have hk0 : keepLib2Text c2MlkemPk2Addr = true := by decide
  have hk4 : keepLib2Text (c2MlkemPk2Addr + 4#64) = true := by decide
  have hn0 : c2MlkemPk2Addr ∉ c2S5Addrs := by decide
  have hn4 : (c2MlkemPk2Addr + 4#64) ∉ c2S5Addrs := by decide
  have hext0 :
      (cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W).externAt? c2MlkemPk2Addr = none := by
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn0)]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) (by decide)
  have hext4 :
      (cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W).externAt? (c2MlkemPk2Addr + 4#64) = none := by
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn4)]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk4) (by decide)
  have hst := steps_mlkemPk2_of_hasWords
    (P_real := cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W)
    (P_rx := pureWordsProg c2MlkemPk2Addr mlkemPk2Words)
    (codeLoaded_of_pureSubslicePk hinv.rxCode c2MlkemPk2Slice_ok)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    (pureWordsProg_externAt_none _ _ _)
    (pureWordsProg_externAt_none _ _ _)
    hext0 hext4 hrun
  rw [setPC_eq_self_of_pc_eq hpc'] at hst
  exact stepsStrictAvoid_of_s5Trap hExt W hst hnoex

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightDalek
