/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import ProofLib.Placed.Multi
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.HeapIntro
import ProofLib.SepLogic.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality
meta import ProofLib.GenPlacedFetches

/-!
# Strict Stuck-`SampleNTT` Avoidance Wrappers for `B10` & `B19` (`ElfSampleNttStuckDivergeMlKemAvoidWrap`)

Proves `StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)` across the
0-hook real execution of block 10 (`lsMlkemFromSeedSym`, `mlkemFromSeedGhostAt c2MlkemMpl stk`) and
block 19 (`lsMlkemEncaps1Sym`, `mlkemEncaps1GhostAt c2MlkemMpl stk`) whenever `mlkemSampleNttTermOf`
holds at entry `u`:
1. Word `0` at `c2MlkemMpl.base j` (`j ∈ {10, 19}`) executes from `u`, where `¬ MlKemSampleNttStuckAt`
   holds directly from `hTerm`.
2. Subsequent straight-line segments inside `dropFirstWord (blockProgram c2MlkemMpl j)` (`off ≥ 4`)
   and active sub-block calls (`B29` `memset`, `B28` `memcpy`, `B05` `generate_keypair_compressed`,
   `B03` `encapsulate1_serialized` via `mlkemActive_run_visitedIn`) never visit any of the 5
   `SampleNTT` wrapper entry addresses `mlkemS5Blocks = [10, 19, 22, 23, 24]`.
3. First-stop determinism (`h2fsgen_stepsUntil_det`) on `emptyStdProg` identifies the avoiding
   return state `sf` with `mlkemFromSeedGhostAt` / `mlkemEncaps1GhostAt` without re-proving post
   functional projections.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidWrap

open Arm64 ProofLib SepProp BitVec
open Arm64.Obj (CodeBlock MultiPlacedLib MultiPlacement PlacedLib Placement lookupBlockSym)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E (readVecN)
open CryptoVerification.E2E.Pqxdh (readVecN_eq_of_pointsToBytes)
open CryptoVerification.SignalSession (
  CliHooks MlKemSampleNttStuckAt cliElfBytes cliExternsPlaced libsignalSessionLib
  lsKemDecapsSym lsKemEncapsSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemFromSeedSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality (
  BoundedHeapIntervals RwOnlyHeap boundedHeapIntervals_memRegion boundedHeapIntervals_mono
  boundedHeapIntervals_pointsToBytes boundedHeapIntervals_pure boundedHeapIntervals_sepConj
  boundedHeapIntervals_stackAt rwOnlyHeap_memRegion rwOnlyHeap_of_isBlock
  rwOnlyHeap_pointsToBytes rwOnlyHeap_pure rwOnlyHeap_sepConj rwOnlyHeap_stackAt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemMemcpySpec mlkemMemsetSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges (
  MlkemEncaps1CallTerminates MlkemFromSeedCallTerminates
  mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk
  mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk withPremise
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  externAt?_mlkemBlockProgram_ext_none mlkemEncaps1AtSpec mlkemFromSeedAtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement mbase mlkemMpl resolve_blk03 resolve_blk05 resolve_blk28 resolve_blk29
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768Encaps1Terminates Mlkem768FromSeedTerminates Shake128MatrixTerminates
  mlkem768Incremental mlkem768KeyPairWith sampleNtt sha3_512List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep stripS_mem stripS_pc stripS_readReg32 stripS_readReg64 stripS_sp
  stripS_spAligned stripS_status strip_readBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  Mlkem768Encaps1Terminates_matrix
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame10 blk10_code_eq blk10_tree_size blkLib10 blkPC10 blkPl10 blkPlaceable10 blkTree10
  cell_entails_memRegion8 mlkem768FromSeedTerminates_iff_list
  mlkem768Incremental_fromSeed_dk_toList mlkem768KeyPairWith_length
  mlkemGenKeypairTermRawSpec savedFrame10_entails_memRegion48
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub sepWP_elim_cell8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05 (
  blk05_generate_keypair_raw_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepWP.of_memRegion_vecRangeMem vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args MlkemEncaps1Args SavedFrame19 UnspilledSaved19 blk19_code_eq blk19_tree_size
  blkLib19 blkPC19 blkPl19 blkPlaceable19 blkTree19 encaps1OutCt1 encaps1OutEs encaps1OutSs
  mlkemBlk03RawSpec mlkemBlk03TermRawSpec savedFrame19_entails_memRegion16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  sepWP_elim_byte step_bCond_not_taken step_bCond_taken
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03 (
  blk03_encaps1_raw_ok
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  satisfies_of_stripExecOutside satisfies_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem (
  c2_mlkem_invMem_of_f3CodeInv
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkemKeep_lr_false c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg
  c2_mlkem_placeable c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
  c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG linkedCallHookG_activeRealPre_of_noException linkedCallHookG_eq_of_guard
  linkedCallHookG_stepsUntil withStateGuard
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_externAt_none emptyStdProg_svc
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer (
  mlKemSampleNttStuckAt_iff mlkemSampleNttSyms mlkemSampleNttTermOf
  mlkemSampleNttTermOf_mlkemEncaps1 mlkemSampleNttTermOf_mlkemFromSeed
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook (
  MlKemSafeBridge MlkemEncaps1StateTerminates MlkemFromSeedStateTerminates
  mlkemActiveGuard mlkemActiveGuard_stripS_setPC mlkemBlockGhost
  mlkemBlockGhost_keepLr_false_of_noException
  mlkemEncaps1GhostAt mlkemEncaps1SafeBridge mlkemFromSeedGhostAt mlkemFromSeedSafeBridge
  mlkemInvMem mlkemInvMem_of_keepsFrozen mlkemInvMem_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  extract_withLsRet subroutine_ok_withLsRet withLsRet withLsRet_frameLeft withLsRet_outcome_setPC
  withLsRet_pre_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  mlkemEncaps1TightStack mlkemFromSeedTightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts f3RxSeg_realProg617_externAt_none
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_stepsVisitedIn_of_stripS_standard
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore (
  StepsStrictAvoid
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality (
  c2_mlkemActiveInvMem_of_codeLoaded_roOk c2_mlkemActiveKeep_ne_s5Base
  mlkemActiveKeep mlkemActiveKeep_sub_c2MlkemKeep mlkemActive_run_visitedIn mlkemS5Blocks
)

attribute [local irreducible] mlkem768Incremental

/-! ## 1. `EmptyAvoid`, `MlKemSampleNttStuckAt` Exclusion, & Real-Program / Ghost Bridges -/

private def BadSntt (mpl : MultiPlacement) (z : State) : Prop :=
  z.status = .Running ∧ MlKemSampleNttStuckAt mpl z

private inductive EmptyAvoid (mpl : MultiPlacement) : State → State → Prop where
  | refl (s : State) : EmptyAvoid mpl s s
  | step {s1 s2 s3 : State} :
      ¬ BadSntt mpl s1 →
      c2MlkemKeep c2MlkemMpl s1.pc = true →
      Step emptyStdProg s1 s2 →
      EmptyAvoid mpl s2 s3 →
      EmptyAvoid mpl s1 s3

private theorem EmptyAvoid.trans {mpl : MultiPlacement} {s1 s2 s3 : State}
    (h12 : EmptyAvoid mpl s1 s2) (h23 : EmptyAvoid mpl s2 s3) :
    EmptyAvoid mpl s1 s3 := by
  induction h12 with
  | refl => exact h23
  | step hnb hk hs _ ih => exact .step hnb hk hs (ih h23)

private theorem step_real617_of_emptyStdProg
    {mpl mmpl : MultiPlacement} (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {s1 s2 : State} (hk : c2MlkemKeep c2MlkemMpl s1.pc = true)
    (hstep : Step emptyStdProg s1 s2) :
    Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1 s2 := by
  have hext_real :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc = none :=
    f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg hk)
      (c2_mlkemKeep_noPanic hk)
  have hext_emp : emptyStdProg.externAt? s1.pc = none := emptyStdProg_externAt_none s1.pc
  have hfm_eq :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem s1.mem s1.pc =
        emptyStdProg.fetchMem s1.mem s1.pc := by
    simp [Program.fetchMem, hext_real, hext_emp]
  cases hstep with
  | exec hrun hfetch =>
    exact Step.exec hrun (hfm_eq.trans hfetch)
  | halt_unmapped hrun hfetch _ =>
    exact Step.halt_unmapped hrun (hfm_eq.trans hfetch) hext_real
  | extern _ he _ _ => rw [hext_emp] at he; cases he
  | extern_fault _ he _ => rw [hext_emp] at he; cases he

private theorem EmptyAvoid.toRealAvoid
    {mpl mmpl : MultiPlacement} (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {s0 sf : State} (h : EmptyAvoid mpl s0 sf) :
    StepsStrictAvoid (BadSntt mpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s0 sf := by
  induction h with
  | refl s => exact .refl s
  | step hnb hk hs _ ih =>
    exact .step hnb (step_real617_of_emptyStdProg hExt W hk hs) ih

private theorem EmptyAvoid.toStepsUntil_stop {mpl : MultiPlacement} {u s sf : State}
    (hlr : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (h : EmptyAvoid mpl s sf) :
    StepsUntil emptyStdProg (SubroutineStop u) s sf := by
  induction h with
  | refl s => exact .refl s
  | @step s1 _ _ _ hk hs _ ih =>
    have hrun1 : s1.status = .Running := hs.status_running
    have hnstop1 : ¬ SubroutineStop u s1 := by
      rintro (⟨hpc, _, _⟩ | hp | ⟨_, he⟩ | ho)
      · rw [hpc, hlr] at hk; cases hk
      · rw [hrun1] at hp; cases hp
      · rw [hrun1] at he; cases he
      · rw [hrun1] at ho; cases ho
    exact .step hnstop1 hs ih

private theorem not_mlKemSampleNttStuckAt_of_ne_s5
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {z : State} (hne : ∀ k ∈ mlkemS5Blocks, z.pc ≠ c2MlkemMpl.base k) :
    ¬ MlKemSampleNttStuckAt mpl z := by
  rw [mlKemSampleNttStuckAt_iff]
  rintro ⟨sym, hmem, hpc, _⟩
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact hne 24 (by decide) (hpc.trans (c2_resolve_kyber1024Encaps_eq hLs))
  · exact hne 23 (by decide) (hpc.trans (c2_resolve_kyber1024Decaps_eq hLs))
  · exact hne 10 (by decide) (hpc.trans (c2_resolve_mlkem768FromSeed_eq hLs))
  · exact hne 19 (by decide) (hpc.trans (c2_resolve_mlkem768Encaps1_eq hLs))
  · exact hne 22 (by decide) (hpc.trans (c2_resolve_mlkem768Decaps_eq hLs))

private theorem c2_s5_bases_distinct :
    c2MlkemMpl.base 10 ≠ c2MlkemMpl.base 24 ∧
    c2MlkemMpl.base 10 ≠ c2MlkemMpl.base 23 ∧
    c2MlkemMpl.base 10 ≠ c2MlkemMpl.base 19 ∧
    c2MlkemMpl.base 10 ≠ c2MlkemMpl.base 22 ∧
    c2MlkemMpl.base 19 ≠ c2MlkemMpl.base 24 ∧
    c2MlkemMpl.base 19 ≠ c2MlkemMpl.base 23 ∧
    c2MlkemMpl.base 19 ≠ c2MlkemMpl.base 10 ∧
    c2MlkemMpl.base 19 ≠ c2MlkemMpl.base 22 := by
  decide

private theorem not_badSntt_entry10
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {u : State} (hpc : u.pc = c2MlkemMpl.base 10)
    (hTerm : mlkemSampleNttTermOf lsMlkemFromSeedSym u) :
    ¬ BadSntt mpl u := by
  rintro ⟨_, hStuck⟩
  rw [mlKemSampleNttStuckAt_iff] at hStuck
  obtain ⟨sym, hmem, hpc_sym, hnot⟩ := hStuck
  have hd := c2_s5_bases_distinct
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact hd.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_kyber1024Encaps_eq hLs)))
  · exact hd.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_kyber1024Decaps_eq hLs)))
  · exact hnot hTerm
  · exact hd.2.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_mlkem768Encaps1_eq hLs)))
  · exact hd.2.2.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_mlkem768Decaps_eq hLs)))

private theorem not_badSntt_entry19
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {u : State} (hpc : u.pc = c2MlkemMpl.base 19)
    (hTerm : mlkemSampleNttTermOf lsMlkemEncaps1Sym u) :
    ¬ BadSntt mpl u := by
  rintro ⟨_, hStuck⟩
  rw [mlKemSampleNttStuckAt_iff] at hStuck
  obtain ⟨sym, hmem, hpc_sym, hnot⟩ := hStuck
  have hd := c2_s5_bases_distinct
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact hd.2.2.2.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_kyber1024Encaps_eq hLs)))
  · exact hd.2.2.2.2.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_kyber1024Decaps_eq hLs)))
  · exact hd.2.2.2.2.2.2.1 (hpc.symm.trans (hpc_sym.trans (c2_resolve_mlkem768FromSeed_eq hLs)))
  · exact hnot hTerm
  · exact hd.2.2.2.2.2.2.2 (hpc.symm.trans (hpc_sym.trans (c2_resolve_mlkem768Decaps_eq hLs)))

private theorem emptyAvoid_of_activeVisitedIn
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 sf : State}
    (hvis : h2fsgen_StepsVisitedIn (mlkemActiveKeep c2MlkemMpl) emptyStdProg s0 sf) :
    EmptyAvoid mpl s0 sf := by
  induction hvis with
  | refl s => exact .refl s
  | @step s1 s2 _ hk hs _ ih =>
    have hnb : ¬ BadSntt mpl s1 := fun ⟨_, hst⟩ =>
      not_mlKemSampleNttStuckAt_of_ne_s5 hLs
        (fun k hk_s5 => c2_mlkemActiveKeep_ne_s5Base hk hk_s5) hst
    exact .step hnb (mlkemActiveKeep_sub_c2MlkemKeep hk) hs ih

private theorem stackAt_split_ge {sp : BitVec 64} {stk t : Nat}
    (ht : t ≤ stk) (hfit : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - t) ∗ stackAt sp t := by
  dsimp only [stackAt]
  have hb : (sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - t) =
      sp - BitVec.ofNat 64 t := by
    have hadd : BitVec.ofNat 64 (stk - t) + BitVec.ofNat 64 t = BitVec.ofNat 64 stk := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      by_cases hs : stk = 2 ^ 64
      · subst hs
        by_cases ht0 : t = 0
        · subst ht0; simp
        · by_cases htt : t = 2 ^ 64
          · subst htt; simp
          · have hlt1 : 2 ^ 64 - t < 2 ^ 64 := Nat.sub_lt (by decide) (Nat.pos_of_ne_zero ht0)
            have hlt2 : t < 2 ^ 64 := Nat.lt_of_le_of_ne ht htt
            rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.sub_add_cancel ht]
      · have hstk_lt : stk < 2 ^ 64 := Nat.lt_of_le_of_ne hfit hs
        have hsub_lt : stk - t < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le stk t) hstk_lt
        have ht_lt : t < 2 ^ 64 := Nat.lt_of_le_of_lt ht hstk_lt
        rw [Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt ht_lt,
          Nat.mod_eq_of_lt hstk_lt, Nat.sub_add_cancel ht,
          Nat.mod_eq_of_lt hstk_lt]
    rw [← hadd]
    bv_omega
  exact memRegion_split' (b := sp - BitVec.ofNat 64 stk) (b' := sp - BitVec.ofNat 64 t)
    (n := stk - t) (k := t) (by omega) hb.symm (by omega)

/-! ## 2. Ghost Endpoint Determinism Helper (`mlkemBlockGhost = sf`) -/

section GhostDet

private theorem stripS_setPC_readBytes (keep : BitVec 64 → Bool) (s : State)
    (pc a : BitVec 64) (n : Nat) :
    (stripS keep (s.setPC pc)).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem]
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [hmem]
  exact strip_readBytes keep s.mem a n

private theorem stripS_setPC_readVecN (keep : BitVec 64 → Bool) (s : State)
    (pc a : BitVec 64) (n : Nat) :
    readVecN (stripS keep (s.setPC pc)).mem a n = readVecN s.mem a n :=
  Subtype.ext (stripS_setPC_readBytes keep s pc a n)

private theorem mlkemFromSeedStateTerminates_stripS_setPC
    (keep : BitVec 64 → Bool) (pc : BitVec 64) (s0 : State)
    (hT : MlkemFromSeedStateTerminates s0) :
    MlkemFromSeedStateTerminates (stripS keep (s0.setPC pc)) := by
  unfold MlkemFromSeedStateTerminates at hT ⊢
  have hx0 : (s0.setPC pc).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
  rw [stripS_readReg64, hx0, stripS_setPC_readVecN]
  exact hT

private theorem mlkemEncaps1StateTerminates_stripS_setPC
    (keep : BitVec 64 → Bool) (pc : BitVec 64) (s0 : State)
    (hT : MlkemEncaps1StateTerminates s0) :
    MlkemEncaps1StateTerminates (stripS keep (s0.setPC pc)) := by
  unfold MlkemEncaps1StateTerminates at hT ⊢
  have hx0 : (s0.setPC pc).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
  have hx1 : (s0.setPC pc).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
  rw [stripS_readReg64, stripS_readReg64, hx0, hx1, stripS_setPC_readBytes]
  exact hT

private theorem keepsFs_strip_inv {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (keepsFs master) where
  pre_eq := fun x s => by
    dsimp only [keepsFs]
    have hs : stripS keep s = s.setMem (stripExecOutside keep s.mem) := by cases s; rfl
    rw [hs, B.m_pre_mem]
  post_eq := fun x s0 sf => by
    dsimp only [keepsFs]
    have hs0 : stripS keep s0 = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    have hsf : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
    have hfs : (stripS keep sf).fs = sf.fs ∧ (stripS keep s0).fs = s0.fs := by
      cases s0; cases sf; exact ⟨rfl, rfl⟩
    rw [hfs.1, hfs.2, hs0, hsf, B.m_post_mem]
  onPanic_eq := fun _ _ _ => by dsimp only [keepsFs]; rw [B.m_pan]
  onExit_eq := fun _ _ _ _ => by dsimp only [keepsFs]; rw [B.m_ex]
  onOom_eq := fun _ _ _ => by dsimp only [keepsFs]; rw [B.m_oom]

private theorem keepsFs_fsT {α : Type} {master : Spec α} {j : Nat} {sym : String}
    {fallback : State → State} (B : MlKemSafeBridge j sym master fallback) :
    SpecPreservesFsTrace (keepsFs master) := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1, FsTraced.of_eq (B.post_tr x R s0 sf hpost.2) (congrArg (·.files) hpost.1)⟩
  · dsimp only [keepsFs] at hp; rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
  · dsimp only [keepsFs] at he; rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
  · dsimp only [keepsFs] at ho; rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem keepsFs_pre_setPC {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) :
    ∀ x (s : State) (pc : BitVec 64),
      (keepsFs master).pre x (s.setPC pc) = (keepsFs master).pre x s := by
  intro x s pc
  dsimp only [keepsFs]
  exact B.m_pre_pc x s pc

private theorem keepsFs_outcome_setPC {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback) :
    ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (keepsFs master) x R (s0.setPC pc) sf →
        SubroutineOutcome (keepsFs master) x R s0 sf := by
  intro x R s0 sf pc hout
  have hret_iff : Returned (s0.setPC pc) sf ↔ Returned s0 sf := by cases s0; rfl
  have hcc_iff : CallingConventionPreserved (s0.setPC pc) sf ↔ CallingConventionPreserved s0 sf := by
    cases s0; rfl
  have hfs : (s0.setPC pc).fs = s0.fs := by cases s0; rfl
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [keepsFs] at hpost
    rw [hfs, B.m_post_pc] at hpost
    exact Or.inl ⟨hret_iff.mp hret, hcc_iff.mp hcc, hpost⟩
  · dsimp only [keepsFs] at hpan; rw [B.m_pan] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [keepsFs] at hex; rw [B.m_ex] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [keepsFs] at hoom; rw [B.m_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

variable [LibsignalPlacement]

private theorem specStripSInvariant_withLsRet {keep : BitVec 64 → Bool} {α : Type}
    {spec : Spec α} (h : SpecStripSInvariant keep spec) :
    SpecStripSInvariant keep (withLsRet spec) where
  pre_eq := fun x s => by dsimp only [withLsRet]; rw [stripS_readReg64, h.pre_eq x s]
  post_eq := h.post_eq
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq

private theorem specPreservesFsTrace_withLsRet {α : Type} {spec : Spec α}
    (h : SpecPreservesFsTrace spec) :
    SpecPreservesFsTrace (withLsRet spec) := h

private theorem subroutineOk_guarded_from_multi {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {CallTerm : α → Prop} {StateTerm : State → Prop}
    (mlkemMpl : MultiPlacement)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0))
    (hmok : mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (withPremise CallTerm (keepsFs (withVmPreserved master))))
      (fun _ => none))
    (hStateImpCall : ∀ (x : α) (R : SepProp) (s : State),
      StateTerm s → s.mem ⊨ master.pre x s ∗ R → CallTerm x) :
    subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)
        (withLsRet (keepsFs master))) := by
  obtain ⟨_, i, off, hsym', hsub⟩ := hmok
  have hij : i = j ∧ off = 0 := by
    rw [hsym] at hsym'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsym'
    exact ⟨hsym'.1.symm, hsym'.2.symm⟩
  rcases hij with ⟨rfl, rfl⟩
  have hfn : mlkemMultiLib.fnAddr mlkemMpl sym = mlkemMpl.base i := by
    simp [MultiPlacedLib.fnAddr, hsym]
  have hBase : subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl i) (mlkemMpl.base i)
      (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u) (keepsFs master)) := by
    apply subroutine_ok.of_codeLoaded
    intro x R s0 hpc hrun hpre hsp _hL
    dsimp only [withStateGuard, keepsFs] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hG, hT⟩, hpreM⟩ := hpre
    have hCall : CallTerm x := hStateImpCall x R s0 hT hpreM
    have hok_mpl := hsub mlkemMpl hG.1
    rw [hfn] at hok_mpl
    have hpre_sub : s0.mem ⊨
        (mlkemMultiLib.withCodeLoaded mlkemMpl
          (withMlKemRoOk mlkemMpl (withPremise CallTerm (keepsFs (withVmPreserved master))))).pre
          x s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
        withVmPreserved]
      rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hG.2.1,
        sepConj_assoc, pure_sepConj_of_true hG.2.2,
        sepConj_assoc, pure_sepConj_of_true hCall]
      exact hpreM
    exact hok_mpl.mono_outcome x R s0 hpc hrun hpre_sub hsp fun sf hout => by
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, he, hex⟩ | ⟨ho, hoom⟩
      · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
          withVmPreserved] at hpost
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
        obtain ⟨hfs, hvm_post⟩ := hpost
        rw [sepConj_assoc, satisfies_pure_sepConj] at hvm_post
        refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withStateGuard, keepsFs]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hfs, hvm_post.2⟩
      · exact Or.inr (Or.inl ⟨hp, hpan⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))
  have hLs := subroutine_ok_withLsRet hBase
  have hComm :
      withLsRet (withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)
          (keepsFs master)) =
        withStateGuard (fun u => mlkemActiveGuard mlkemMpl u ∧ StateTerm u)
          (withLsRet (keepsFs master)) :=
    withLsRet_frameLeft (keepsFs master)
      (fun _ s => ⌜mlkemActiveGuard mlkemMpl s ∧ StateTerm s⌝) (keepsFs master).post
  rwa [hComm] at hLs

private theorem mlkemBlockGhost_eq_of_emptyAvoid_ret
    {mpl : MultiPlacement} {j : Nat} {sym : String} {α : Type}
    {master : Spec α} {fallback : State → State}
    (B : MlKemSafeBridge j sym master fallback)
    (StateTerm : State → Prop)
    (hTermStrip : ∀ s0 : State, StateTerm s0 →
      StateTerm (stripS (mlkemKeep c2MlkemMpl) (s0.setPC (c2MlkemMpl.base j))))
    (hSubOk : subroutine_ok (mlkemMultiLib.blockProgram c2MlkemMpl j) (c2MlkemMpl.base j)
      (withStateGuard (fun u => mlkemActiveGuard c2MlkemMpl u ∧ StateTerm u)
        (withLsRet (keepsFs master))))
    (hLsLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {u sf : State}
    (hpc_j : u.pc = c2MlkemMpl.base j)
    (hTu : StateTerm u)
    (hInvM : mlkemInvMem c2MlkemMpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hnoex : ∀ msg, (mlkemBlockGhost c2MlkemMpl j (keepsFs master) fallback u).status ≠
      .Exception msg)
    (hAvoid : EmptyAvoid mpl u sf)
    (hRet : Returned u sf) :
    mlkemBlockGhost c2MlkemMpl j (keepsFs master) fallback u = sf ∧
      ExecFrozen (mlkemBlockGhost c2MlkemMpl j (keepsFs master) fallback u).mem := by
  have hGu : mlkemActiveGuard c2MlkemMpl u := hInvM
  have hKeepLr : ∀ lr : BitVec 64, LsRetAddr624 lr → mlkemKeep c2MlkemMpl lr = false :=
    fun lr hlr => c2_mlkemKeep_lr_false hLsLs hlr
  have hlr : mlkemKeep c2MlkemMpl (u.readReg64 .lr) = false :=
    mlkemBlockGhost_keepLr_false_of_noException hKeepLr hnoex
  have hCodeSub : (mlkemMultiLib.blockProgram c2MlkemMpl j).CodeLoaded
      (stripExecOutside (mlkemKeep c2MlkemMpl) u.mem) :=
    (mlkemInvMem_stripExecOutside hInvM).2.1 j B.hj
  have hActPre : ActiveRealPre (withLsRet (keepsFs master)) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hEqG : mlkemBlockGhost c2MlkemMpl j (keepsFs master) fallback u =
      linkedCallHookG (fun v => mlkemActiveGuard c2MlkemMpl v ∧ StateTerm v)
        (mlkemKeep c2MlkemMpl) emptyStdProg (mlkemMultiLib.blockProgram c2MlkemMpl j)
        (c2MlkemMpl.base j) (withLsRet (keepsFs master)) fallback u := by
    unfold mlkemBlockGhost
    rw [linkedCallHookG_eq_of_guard hGu, linkedCallHookG_eq_of_guard ⟨hGu, hTu⟩]
  obtain ⟨huntil_g, hstop_g, hFrOut⟩ :=
    linkedCallHookG_stepsUntil
      (Guard := fun v => mlkemActiveGuard c2MlkemMpl v ∧ StateTerm v)
      (fallback := fallback)
      emptyStdProg_svc
      (rfl : (mlkemMultiLib.blockProgram c2MlkemMpl j).svc = Syscall.standard)
      (fun pc _ => emptyStdProg_externAt_none pc)
      (externAt?_mlkemBlockProgram_ext_none c2MlkemMpl B.hj (fun _ => none))
      (fun v _ ⟨hg, ht⟩ => ⟨mlkemActiveGuard_stripS_setPC c2MlkemMpl _ v hg, hTermStrip v ht⟩)
      hSubOk
      (specStripSInvariant_withLsRet (keepsFs_strip_inv B (mlkemKeep c2MlkemMpl)))
      (specPreservesFsTrace_withLsRet (keepsFs_fsT B))
      (withLsRet_pre_setPC (keepsFs_pre_setPC B))
      (withLsRet_outcome_setPC (keepsFs_outcome_setPC B))
      ⟨hGu, hTu⟩ hActPre hFr hlr hCodeSub
  rw [← hEqG] at huntil_g hstop_g hFrOut
  have hsetPC : u.setPC (c2MlkemMpl.base j) = u := by
    cases u; dsimp only [State.setPC] at hpc_j ⊢; subst hpc_j; rfl
  rw [hsetPC] at huntil_g
  have hstop_sf : SubroutineStop u sf := Or.inl hRet
  have hlr_c2 : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false := hlr
  have huntil_sf : StepsUntil emptyStdProg (SubroutineStop u) u sf :=
    hAvoid.toStepsUntil_stop hlr_c2
  exact ⟨h2fsgen_stepsUntil_det huntil_g hstop_g huntil_sf hstop_sf, hFrOut⟩

end GhostDet

/-! ## 3. Straight-Line Sub-Programs (`firstWordProg` & `dropFirstWord`) & `SepWP` Runners -/

private def firstWordProg (P : Program) : Program :=
  { base := P.base, code := P.code.take 4 }

private def dropFirstWord (P : Program) : Program :=
  { base := P.base + 4#64, code := P.code.drop 4 }

private theorem setMem_pc (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem setMem_status (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem setMem_sp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem setMem_spAligned (s : State) (m : Memory) :
    (s.setMem m).spAligned = s.spAligned := by
  cases s; rfl
private theorem setMem_pstate (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem setMem_readReg64 (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases s; rfl
private theorem setMem_readReg32 (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases s; rfl
private theorem setMem_readVReg128 (s : State) (m : Memory) (r : BitVec 5) :
    (s.setMem m).readVReg128 r = s.readVReg128 r := by
  cases s; rfl
private theorem setMem_regs (s : State) (m : Memory) : (s.setMem m).regs = s.regs := by
  cases s; rfl
private theorem setMem_vregs (s : State) (m : Memory) : (s.setMem m).vregs = s.vregs := by
  cases s; rfl
private theorem stripS_setMem_eq (keep0 keepD : BitVec 64 → Bool) (s : State) :
    (stripS keep0 s).setMem (stripExecOutside keepD s.mem) = stripS keepD s := by
  cases s; rfl

attribute [local simp, local arm64_norm, local wp_norm]
  setMem_pc setMem_status setMem_sp setMem_spAligned setMem_pstate
  setMem_readReg64 setMem_readReg32 setMem_readVReg128 setMem_regs setMem_vregs

private theorem firstWordProg_externAt_none (P : Program) (pc : BitVec 64) :
    (firstWordProg P).externAt? pc = none := by
  simp [firstWordProg, Program.externAt?, Program.hookAtOff?]

private theorem dropFirstWord_externAt_none (P : Program) (pc : BitVec 64) :
    (dropFirstWord P).externAt? pc = none := by
  simp [dropFirstWord, Program.externAt?, Program.hookAtOff?]

private theorem firstWordProg_codeLoaded_strip {P : Program} {m : Memory}
    (hcl : P.CodeLoaded m) (hlen : 4 ≤ P.code.length) :
    (firstWordProg P).CodeLoaded (stripExecOutside (progKeep (firstWordProg P)) m) := by
  have htlen : (firstWordProg P).code.length = 4 := by
    simp [firstWordProg, List.length_take, Nat.min_eq_left hlen]
  have hnw : P.base.toNat + 4 ≤ 2 ^ 64 := Nat.le_trans (by omega) hcl.no_wrap
  refine Program.CodeLoaded.intro hcl.aligned
    (by rw [show (firstWordProg P).base = P.base from rfl, htlen]; exact hnw)
    fun i hi => ?_
  rw [htlen] at hi
  have hsub : P.base + BitVec.ofNat 64 i - P.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (P.base + BitVec.ofNat 64 i - (firstWordProg P).base).toNat <
      (firstWordProg P).code.length := by
    change (P.base + BitVec.ofNat 64 i - P.base).toNat < (firstWordProg P).code.length
    rw [hsub, htlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  have hk : progKeep (firstWordProg P) (P.base + BitVec.ofNat 64 i) = true := decide_eq_true hin
  have htake_i : (firstWordProg P).code[i]'(by rw [htlen]; exact hi) =
      P.code[i]'(by omega) := by
    simp [firstWordProg]
  have haddr : (firstWordProg P).base + BitVec.ofNat 64 i = P.base + BitVec.ofNat 64 i := rfl
  rw [haddr, strip_read8, strip_perm_of_keep hk, strip_isLazyFree, htake_i]
  exact ⟨hcl.byte_eq i (by omega), hcl.perm_eq i (by omega), hcl.isLazyFree_eq i (by omega)⟩

private theorem dropFirstWord_codeLoaded_strip {P : Program} {m : Memory}
    (hcl : P.CodeLoaded m) (hlen : 8 ≤ P.code.length) :
    (dropFirstWord P).CodeLoaded (stripExecOutside (progKeep (dropFirstWord P)) m) := by
  have hdlen : (dropFirstWord P).code.length = P.code.length - 4 := by
    simp [dropFirstWord]
  have hnw0 := hcl.no_wrap
  have hb4_nat : (P.base + 4#64).toNat = P.base.toNat + 4 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hal4 : (dropFirstWord P).base.toNat % 4 = 0 := by
    change (P.base + 4#64).toNat % 4 = 0
    have ha0 := hcl.aligned
    omega
  have hnw4 : (dropFirstWord P).base.toNat + (dropFirstWord P).code.length ≤ 2 ^ 64 := by
    change (P.base + 4#64).toNat + (dropFirstWord P).code.length ≤ 2 ^ 64
    omega
  refine Program.CodeLoaded.intro hal4 hnw4 fun i hi => ?_
  rw [hdlen] at hi
  have haddr : (dropFirstWord P).base + BitVec.ofNat 64 i = P.base + BitVec.ofNat 64 (4 + i) := by
    change P.base + 4#64 + BitVec.ofNat 64 i = P.base + BitVec.ofNat 64 (4 + i)
    bv_omega
  have hsub : (dropFirstWord P).base + BitVec.ofNat 64 i - (dropFirstWord P).base =
      BitVec.ofNat 64 i := by bv_omega
  have hin : ((dropFirstWord P).base + BitVec.ofNat 64 i - (dropFirstWord P).base).toNat <
      (dropFirstWord P).code.length := by
    rw [hsub, hdlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  have hk : progKeep (dropFirstWord P) ((dropFirstWord P).base + BitVec.ofNat 64 i) = true :=
    decide_eq_true hin
  have hdrop_i : (dropFirstWord P).code[i]'(by rw [hdlen]; exact hi) =
      P.code[4 + i]'(by omega) := by
    simp [dropFirstWord]
  rw [strip_read8, strip_perm_of_keep hk, strip_isLazyFree, hdrop_i, haddr]
  exact ⟨hcl.byte_eq (4 + i) (by omega), hcl.perm_eq (4 + i) (by omega),
    hcl.isLazyFree_eq (4 + i) (by omega)⟩

private theorem firstWordProg_fetch_base {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hlen : 4 ≤ P.code.length) :
    (firstWordProg P).fetch P.base = P.fetch P.base := by
  have h0 : (P.base - P.base).toNat = 0 := by simp
  have h0' : (P.base - (firstWordProg P).base).toNat = 0 := h0
  have hrw : (firstWordProg P).readWordOff 0 = P.readWordOff 0 := by
    unfold Program.readWordOff
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, firstWordProg, List.drop_zero]
    rcases hp : P.code with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;>
      simp [hp] at hlen ⊢
  unfold Program.fetch
  rw [firstWordProg_externAt_none, hext, h0', h0, hrw]

private theorem firstWordProg_fetch_zero {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hlen : 4 ≤ P.code.length) :
    (firstWordProg P).fetch (P.base + 0#64) = P.fetch (P.base + 0#64) := by
  rw [BitVec.add_zero, firstWordProg_fetch_base hext hlen]

private theorem dropFirstWord_fetch_add {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    (off : Nat) (hoff4 : 4 ≤ off) (hoff_lt : off < 256) :
    (dropFirstWord P).fetch (P.base + BitVec.ofNat 64 off) =
      P.fetch (P.base + BitVec.ofNat 64 off) := by
  have hu64 : off < 2 ^ 64 := by omega
  have hsubP : (P.base + BitVec.ofNat 64 off - P.base).toNat = off := by
    have h1 : P.base + BitVec.ofNat 64 off - P.base = BitVec.ofNat 64 off := by bv_omega
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64]
  have hsubD : (P.base + BitVec.ofNat 64 off - (dropFirstWord P).base).toNat = off - 4 := by
    have h1 : P.base + BitVec.ofNat 64 off - (P.base + 4#64) = BitVec.ofNat 64 (off - 4) := by
      bv_omega
    change (P.base + BitVec.ofNat 64 off - (P.base + 4#64)).toNat = off - 4
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmod4 : (off - 4) % 4 = off % 4 := by omega
  have hrw : (dropFirstWord P).readWordOff (off - 4) = P.readWordOff off := by
    unfold Program.readWordOff
    simp only [dropFirstWord, hmod4, List.drop_drop, show 4 + (off - 4) = off by omega]
  unfold Program.fetch
  rw [dropFirstWord_externAt_none, hext, hsubD, hsubP, hrw]

private theorem dropFirstWord_fetch_bv {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    (off : BitVec 64) (h1 : 4#64 ≤ off) (h2 : off < 256#64) :
    (dropFirstWord P).fetch (P.base + off) = P.fetch (P.base + off) := by
  have hoff4 : 4 ≤ off.toNat := BitVec.le_def.mp h1
  have hoff_lt : off.toNat < 256 := BitVec.lt_def.mp h2
  have heq : BitVec.ofNat 64 off.toNat = off := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt off.isLt]
  rw [← heq]
  exact dropFirstWord_fetch_add hext off.toNat hoff4 hoff_lt

private theorem emptyStdProg_fetchMem_base_eq {P : Program} {m : Memory} {inst : Instr}
    (hcl : P.CodeLoaded m) (hlen : 4 ≤ P.code.length)
    (hext : ∀ pc, P.externAt? pc = none)
    (hfm : emptyStdProg.fetchMem m P.base = some inst) :
    P.fetch P.base = some inst := by
  have hrw : P.readWordOff 0 = some (m.read32 P.base) := by
    have hb0 := hcl.byte_eq 0 (by omega)
    have hb1 := hcl.byte_eq 1 (by omega)
    have hb2 := hcl.byte_eq 2 (by omega)
    have hb3 := hcl.byte_eq 3 (by omega)
    have ha0 : P.base + 0#64 = P.base + BitVec.ofNat 64 0 := by bv_omega
    unfold Program.readWordOff
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.drop_zero]
    rcases hp : P.code with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
    · simp [hp] at hlen
    · simp [hp] at hlen
    · simp [hp] at hlen
    · simp [hp] at hlen
    · simp only [hp, List.getElem_cons_zero, List.getElem_cons_succ] at hb0 hb1 hb2 hb3
      dsimp only [Memory.read32]
      rw [← ha0] at hb0
      rw [hb0, hb1, hb2, hb3]
  have hdec : decode (m.read32 P.base) = some inst := by
    unfold Program.fetchMem at hfm
    rw [emptyStdProg_externAt_none] at hfm
    split at hfm
    · simp at hfm
    · split at hfm
      · simp at hfm
      · split at hfm
        · simp at hfm
        · exact hfm
  unfold Program.fetch
  have h0 : (P.base - P.base).toNat = 0 := by simp
  rw [hext P.base, h0, hrw]
  exact hdec

private theorem run_firstWord_sepWP
    {mpl : MultiPlacement} {j : Nat} (hj : j < mlkemMultiLib.blocks.length)
    {u : State} {Pre R : SepProp} {Post : State → SepProp → Prop}
    (P : Program) (hP : P = mlkemMultiLib.blockProgram c2MlkemMpl j)
    (hlen : 4 ≤ P.code.length)
    (hpc : u.pc = P.base)
    (hcl : P.CodeLoaded u.mem)
    (hFr : ExecFrozen u.mem)
    (hnb_u : ¬ BadSntt mpl u)
    (hadv0 : ∃ inst0 : Instr,
      P.fetch P.base = some inst0 ∧
      ∀ s : State, s.pc = P.base →
        (emptyStdProg.evalInst inst0 s).status = .Running →
        (emptyStdProg.evalInst inst0 s).pc = P.base + 4#64)
    (hsat : u.mem ⊨ Pre ∗ R)
    (hwp : SepWP (firstWordProg P) (P.base + 4#64)
      (stripS (progKeep (firstWordProg P)) u) Pre
      (fun sf' Pf => Post sf' Pf)) :
    ∃ sf1 Pf,
      EmptyAvoid mpl u sf1 ∧
      sf1.pc = P.base + 4#64 ∧
      sf1.status = .Running ∧
      u.mem.KeepsFrozen sf1.mem ∧
      ExecFrozen sf1.mem ∧
      (sf1.mem ⊨ Pf ∗ R) ∧
      Post (stripS (progKeep (firstWordProg P)) sf1) Pf := by
  obtain ⟨inst0, hfetch0, hadv⟩ := hadv0
  let keep0 := progKeep (firstWordProg P)
  have hcl0 : (firstWordProg P).CodeLoaded (stripS keep0 u).mem := by
    rw [stripS_mem]; exact firstWordProg_codeLoaded_strip hcl hlen
  have hsat0 : (stripS keep0 u).mem ⊨ Pre ∗ R := by
    rw [stripS_mem]; exact satisfies_stripExecOutside keep0 hsat
  obtain ⟨sf1', hsteps', ⟨hpc1', hrun1', Pf, hsat1', hpost1'⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.elim hwp hsat0 hcl0
  · let s_stop := sf1'.writeReg64 .lr (P.base + 4#64)
    have hlr_stop : s_stop.readReg64 .lr = P.base + 4#64 := by simp [s_stop]
    have hstop' : SubroutineStop s_stop sf1' :=
      Or.inl ⟨hpc1'.trans hlr_stop.symm, rfl, hrun1'⟩
    have hlr_out : keep0 (s_stop.readReg64 .lr) = false := by
      rw [hlr_stop]
      unfold keep0 progKeep firstWordProg
      dsimp only
      have hsub : P.base + 4#64 - P.base = 4#64 := by bv_omega
      have htlen : (P.code.take 4).length = 4 := by
        rw [List.length_take, Nat.min_eq_left hlen]
      rw [hsub, htlen]
      decide
    obtain ⟨sf1, huntil1, _, hsf1_eq, hFr1, hvis1⟩ :=
      h2fsgen_stepsVisitedIn_of_stripS_standard (s0 := s_stop)
        emptyStdProg_svc rfl
        (fun pc _ => emptyStdProg_externAt_none pc)
        (firstWordProg_externAt_none P)
        hlr_out hsteps' hstop' (by rw [hrun1']; decide) hFr
    have hrun1 : sf1.status = .Running := by
      have h := stripS_status keep0 sf1
      rw [← hsf1_eq] at h
      exact h.symm.trans hrun1'
    have hpc1 : sf1.pc = P.base + 4#64 := by
      have h := stripS_pc keep0 sf1
      rw [← hsf1_eq] at h
      exact h.symm.trans hpc1'
    have hsat1 : sf1.mem ⊨ Pf ∗ R := by
      rw [hsf1_eq, stripS_mem] at hsat1'
      exact satisfies_of_stripExecOutside hFr1 hsat1'
    have hc2_u : c2MlkemKeep c2MlkemMpl u.pc = true := by
      unfold c2MlkemKeep
      rw [List.any_eq_true]
      refine ⟨j, List.mem_range.mpr hj, ?_⟩
      rw [← hP, hpc]
      unfold progKeep
      have hsub0 : (P.base - P.base).toNat = 0 := by simp
      rw [hsub0]
      exact decide_eq_true (by omega)
    have hEA : EmptyAvoid mpl u sf1 := by
      cases hvis1 with
      | refl =>
        exfalso
        have hne : P.base ≠ P.base + 4#64 := by bv_omega
        exact hne (hpc.symm.trans hpc1)
      | @step _ z1 _ _ hstep1 hrest =>
        cases hrest with
        | refl => exact .step hnb_u hc2_u hstep1 (.refl _)
        | @step _ z2 _ hk_z1 hstep2 _ =>
          exfalso
          have hrun_z1 : z1.status = .Running := hstep2.status_running
          have hextP : ∀ pc, P.externAt? pc = none :=
            hP ▸ externAt?_mlkemBlockProgram_ext_none c2MlkemMpl hj (fun _ => none)
          cases hstep1 with
          | halt_unmapped => cases hrun_z1
          | extern _ he _ _ => rw [emptyStdProg_externAt_none] at he; cases he
          | extern_fault _ he _ => rw [emptyStdProg_externAt_none] at he; cases he
          | exec _ hfm =>
            have hfm0 := hpc ▸ hfm
            have hf_eq := emptyStdProg_fetchMem_base_eq hcl hlen hextP hfm0
            rw [hfetch0] at hf_eq
            injection hf_eq with hinst
            rw [← hinst] at hrun_z1 hk_z1
            have hz1_pc : (emptyStdProg.evalInst inst0 u).pc = P.base + 4#64 :=
              hadv u hpc hrun_z1
            have hk_false : keep0 (P.base + 4#64) = false := by
              rw [← hlr_stop]; exact hlr_out
            rw [hz1_pc, hk_false] at hk_z1
            cases hk_z1
    rw [hsf1_eq] at hpost1'
    exact ⟨sf1, Pf, hEA, hpc1, hrun1, huntil1.toSteps.keepsFrozen, hFr1, hsat1, hpost1'⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem emptyAvoid_of_visitedIn_sub
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {D : BitVec 64 → Bool}
    (hNoS5 : ∀ pc : BitVec 64, D pc = true → ∀ k ∈ mlkemS5Blocks, pc ≠ c2MlkemMpl.base k)
    (hSub : ∀ pc : BitVec 64, D pc = true → c2MlkemKeep c2MlkemMpl pc = true)
    {s0 sf : State} (hvis : h2fsgen_StepsVisitedIn D emptyStdProg s0 sf) :
    EmptyAvoid mpl s0 sf := by
  induction hvis with
  | refl z => exact .refl z
  | @step s1 _ _ hk hs _ ih =>
    have hnb : ¬ BadSntt mpl s1 := fun ⟨_, hst⟩ =>
      not_mlKemSampleNttStuckAt_of_ne_s5 hLs (hNoS5 s1.pc hk) hst
    exact .step hnb (hSub s1.pc hk) hs ih

private theorem run_dropFirstWord_sepWP
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {j : Nat} (hj : j < mlkemMultiLib.blocks.length)
    {s : State} {target : BitVec 64} {Pre R : SepProp} {Post : State → SepProp → Prop}
    (P : Program) (hP : P = mlkemMultiLib.blockProgram c2MlkemMpl j)
    (hlen : 8 ≤ P.code.length)
    (hNoS5 : ∀ pc : BitVec 64, progKeep (dropFirstWord P) pc = true →
      ∀ k ∈ mlkemS5Blocks, pc ≠ c2MlkemMpl.base k)
    (htarget_out : progKeep (dropFirstWord P) target = false)
    (hcl : P.CodeLoaded s.mem)
    (hFr : ExecFrozen s.mem)
    (hsat : s.mem ⊨ Pre ∗ R)
    (hwp : SepWP (dropFirstWord P) target
      (stripS (progKeep (dropFirstWord P)) s) Pre
      (fun sf' Pf => Post sf' Pf)) :
    ∃ sf Pf,
      EmptyAvoid mpl s sf ∧
      sf.pc = target ∧
      sf.status = .Running ∧
      s.mem.KeepsFrozen sf.mem ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ Pf ∗ R) ∧
      Post (stripS (progKeep (dropFirstWord P)) sf) Pf := by
  let keepD := progKeep (dropFirstWord P)
  have hclD : (dropFirstWord P).CodeLoaded (stripS keepD s).mem := by
    rw [stripS_mem]; exact dropFirstWord_codeLoaded_strip hcl hlen
  have hsatD : (stripS keepD s).mem ⊨ Pre ∗ R := by
    rw [stripS_mem]; exact satisfies_stripExecOutside keepD hsat
  obtain ⟨sf', hsteps', ⟨hpcf', hrunf', Pf, hsatf', hpostf'⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.elim hwp hsatD hclD
  · let s_stop := sf'.writeReg64 .lr target
    have hlr_stop : s_stop.readReg64 .lr = target := by simp [s_stop]
    have hstop' : SubroutineStop s_stop sf' :=
      Or.inl ⟨hpcf'.trans hlr_stop.symm, rfl, hrunf'⟩
    have hlr_out : keepD (s_stop.readReg64 .lr) = false := hlr_stop ▸ htarget_out
    obtain ⟨sf, huntil, _, hsf_eq, hFrf, hvis⟩ :=
      h2fsgen_stepsVisitedIn_of_stripS_standard (s0 := s_stop)
        emptyStdProg_svc rfl
        (fun pc _ => emptyStdProg_externAt_none pc)
        (dropFirstWord_externAt_none P)
        hlr_out hsteps' hstop' (by rw [hrunf']; decide) hFr
    have hrunf : sf.status = .Running := by
      have h := stripS_status keepD sf
      rw [← hsf_eq] at h
      exact h.symm.trans hrunf'
    have hpcf : sf.pc = target := by
      have h := stripS_pc keepD sf
      rw [← hsf_eq] at h
      exact h.symm.trans hpcf'
    have hsatf : sf.mem ⊨ Pf ∗ R := by
      rw [hsf_eq, stripS_mem] at hsatf'
      exact satisfies_of_stripExecOutside hFrf hsatf'
    have hsub_keep : ∀ pc : BitVec 64, keepD pc = true → c2MlkemKeep c2MlkemMpl pc = true := by
      intro pc hk
      have hnw := hcl.no_wrap
      unfold keepD progKeep dropFirstWord at hk
      dsimp only at hk
      have hlt : (pc - (P.base + 4#64)).toNat < P.code.length - 4 := by
        simpa [List.length_drop] using of_decide_eq_true hk
      have hinP : (pc - P.base).toNat < P.code.length := by bv_omega
      unfold c2MlkemKeep
      rw [List.any_eq_true]
      exact ⟨j, List.mem_range.mpr hj, hP ▸ decide_eq_true hinP⟩
    have hEA : EmptyAvoid mpl s sf :=
      emptyAvoid_of_visitedIn_sub hLs hNoS5 hsub_keep hvis
    rw [hsf_eq] at hpostf'
    exact ⟨sf, Pf, hEA, hpcf, hrunf, huntil.toSteps.keepsFrozen, hFrf, hsatf, hpostf'⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem dropFirstWord_keep_false_of_c2Keep_false
    {j : Nat} (hj : j < mlkemMultiLib.blocks.length)
    (_hnw : (mlkemMultiLib.blockProgram c2MlkemMpl j).base.toNat +
      (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length ≤ 2 ^ 64)
    {pc : BitVec 64} (hc2 : c2MlkemKeep c2MlkemMpl pc = false) :
    progKeep (dropFirstWord (mlkemMultiLib.blockProgram c2MlkemMpl j)) pc = false := by
  by_cases hk : progKeep (dropFirstWord (mlkemMultiLib.blockProgram c2MlkemMpl j)) pc = true
  · exfalso
    let P := mlkemMultiLib.blockProgram c2MlkemMpl j
    unfold progKeep dropFirstWord at hk
    dsimp only at hk
    have hlt : (pc - (P.base + 4#64)).toNat < P.code.length - 4 := by
      simpa [List.length_drop] using of_decide_eq_true hk
    have hinP : (pc - P.base).toNat < P.code.length := by bv_omega
    have hc2_t : c2MlkemKeep c2MlkemMpl pc = true := by
      unfold c2MlkemKeep; rw [List.any_eq_true]
      exact ⟨j, List.mem_range.mpr hj, decide_eq_true hinP⟩
    rw [hc2] at hc2_t; cases hc2_t
  · exact Bool.eq_false_iff.mpr hk

/-! ## 4. Active Sub-Block Runners (`B29` `memset`, `B28` `memcpy`, `B05`, `B03`) -/

private def memset2400Spec : Spec (BitVec 64 × BitVec 8) where
  pre := fun (ptr, c) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧
      (s0.readReg32 .x1).truncate 8 = c ∧
      (s0.readReg64 .x2).toNat = 2400⌝ ∗
      memRegion ptr 2400
  post := fun (ptr, c) _s0 sf =>
    ⌜sf.readReg64 .x0 = ptr⌝ ∗ (ptr ↦ₛ List.replicate 2400 c)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def memcpy2400Spec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = 2400 ∧
      bs.length = 2400⌝ ∗
      memRegion dst 2400 ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) _s0 sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private noncomputable def genKeypair31216Spec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (seedA, seed, outPtr) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x1 = outPtr ∧
      seed.length = 64 ∧
      Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion outPtr 2400 ∗ stackAt s0.sp 31216
  post := fun (seedA, seed, outPtr) s0 _sf =>
    (seedA ↦ₛ seed) ∗ (outPtr ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 31216
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem active_call_memset2400
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} {ptr : BitVec 64} {c : BitVec 8} {R : SepProp}
    (hpc : s0.pc = c2MlkemMpl.base 29) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvM : mlkemInvMem c2MlkemMpl s0.mem) (hFr0 : ExecFrozen s0.mem)
    (hpre : s0.mem ⊨ memset2400Spec.pre (ptr, c) s0 ∗ R) :
    ∃ sf : State,
      EmptyAvoid mpl s0 sf ∧
      Returned s0 sf ∧
      CalleeSavedPreserved s0 sf ∧
      (sf.mem ⊨ memset2400Spec.post (ptr, c) s0 sf ∗ R) ∧
      s0.mem.KeepsFrozen sf.mem ∧
      ExecFrozen sf.mem := by
  have hsim : ∀ mpl', SpecSimulates mlkemMemsetSpec (withMlKemRoOk mpl' memset2400Spec) := by
    intro mpl' ⟨p, v⟩ R1 st h
    dsimp only [withMlKemRoOk, memset2400Spec] at h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨_, h⟩ := h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨⟨hx0, hx1, hx2⟩, hmr⟩ := h
    refine ⟨(p, v, 2400), R1, ?_, ?_⟩
    · dsimp only [mlkemMemsetSpec]
      rw [sepConj_assoc, pure_sepConj_of_true ⟨hx0, hx1, hx2, by decide⟩]
      exact hmr
    · intro sf hout
      rcases hout with ⟨hret, hcc, hpst⟩ | ⟨hp, hpan⟩ | ⟨cd, he, hex⟩ | ⟨ho, hoom⟩
      · dsimp only [mlkemMemsetSpec] at hpst
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpst
        obtain ⟨⟨_, hx0f⟩, hbytes⟩ := hpst
        refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withMlKemRoOk, memset2400Spec]
        rw [sepConj_assoc, pure_sepConj_of_true hx0f]
        exact hbytes
      · exact Or.inr (Or.inl ⟨hp, hpan⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cd, he, hex⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))
  obtain ⟨sf, hvis, hret, ⟨_, hcs⟩, hpost, hkf, hnsp, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 29) (by decide)
      (blockSpec := fun _ => mlkemMemsetSpec) (master := memset2400Spec) c2MlkemMpl
      blk29_memset_ok hsim rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun ⟨p, _⟩ _ h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_memRegion p 2400) hh)
      (fun ⟨p, _⟩ _ h hh => boundedHeapIntervals_mono (k₁ := 0 + 1) (by decide) (Nat.le_refl _)
        (boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
          (fun _ => boundedHeapIntervals_memRegion p 2400 (by decide)) hh))
      (fun ⟨p, v⟩ _ _ h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_pointsToBytes p (List.replicate 2400 v)) hh)
      hpc hrun hsp (c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2) hpre
  exact ⟨sf, emptyAvoid_of_activeVisitedIn hLs hvis, hret, hcs, hpost, hkf,
    ExecFrozen.of_perm_eq hFr0 (fun a => congrFun hnsp.2.1 a)⟩

private theorem active_call_memcpy2400
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} {dst src : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (hpc : s0.pc = c2MlkemMpl.base 28) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvM : mlkemInvMem c2MlkemMpl s0.mem) (hFr0 : ExecFrozen s0.mem)
    (hpre : s0.mem ⊨ memcpy2400Spec.pre (dst, src, bs) s0 ∗ R) :
    ∃ sf : State,
      EmptyAvoid mpl s0 sf ∧
      Returned s0 sf ∧
      CalleeSavedPreserved s0 sf ∧
      (sf.mem ⊨ memcpy2400Spec.post (dst, src, bs) s0 sf ∗ R) ∧
      s0.mem.KeepsFrozen sf.mem ∧
      ExecFrozen sf.mem := by
  have hsim : ∀ mpl', SpecSimulates mlkemMemcpySpec (withMlKemRoOk mpl' memcpy2400Spec) := by
    intro mpl' ⟨d, sr, b⟩ R1 st h
    dsimp only [withMlKemRoOk, memcpy2400Spec] at h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨_, h⟩ := h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨⟨hx0, hx1, hx2, hblen⟩, hspat⟩ := h
    refine ⟨(d, sr, b), R1, ?_, ?_⟩
    · dsimp only [mlkemMemcpySpec]
      rw [hblen, sepConj_assoc, pure_sepConj_of_true ⟨hx0, hx1, hx2, by decide⟩]
      exact hspat
    · intro sf hout
      rcases hout with ⟨hret, hcc, hpst⟩ | ⟨hp, hpan⟩ | ⟨cd, he, hex⟩ | ⟨ho, hoom⟩
      · dsimp only [mlkemMemcpySpec] at hpst
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpst
        obtain ⟨⟨_, hx0f⟩, hbytes⟩ := hpst
        refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withMlKemRoOk, memcpy2400Spec]
        rw [sepConj_assoc, pure_sepConj_of_true hx0f]
        exact hbytes
      · exact Or.inr (Or.inl ⟨hp, hpan⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cd, he, hex⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))
  obtain ⟨sf, hvis, hret, ⟨_, hcs⟩, hpost, hkf, hnsp, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 28) (by decide)
      (blockSpec := fun _ => mlkemMemcpySpec) (master := memcpy2400Spec) c2MlkemMpl
      blk28_memcpy_ok hsim rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun ⟨d, sr, b⟩ _ h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_memRegion d 2400)
          (fun _ => rwOnlyHeap_pointsToBytes sr b)) hh)
      (fun ⟨d, sr, b⟩ _ h hh => by
        rcases SepProp.holds_sepConj_iff.mp hh with ⟨h1, _, _, rfl, hp1, _⟩
        obtain ⟨_, _, _, _, hblen⟩ := SepProp.holds_pure_iff.mp hp1
        exact boundedHeapIntervals_mono (k₁ := 0 + (1 + 1)) (by decide) (Nat.le_refl _)
          (boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj
              (fun _ => boundedHeapIntervals_memRegion d 2400 (by decide))
              (fun _ => boundedHeapIntervals_pointsToBytes sr b (by omega))) hh))
      (fun ⟨d, sr, b⟩ _ _ h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes d b)
          (fun _ => rwOnlyHeap_pointsToBytes sr b)) hh)
      hpc hrun hsp (c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2) hpre
  exact ⟨sf, emptyAvoid_of_activeVisitedIn hLs hvis, hret, hcs, hpost, hkf,
    ExecFrozen.of_perm_eq hFr0 (fun a => congrFun hnsp.2.1 a)⟩

private theorem active_call_blk05
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} {seedA outPtr : BitVec 64} {seed : List (BitVec 8)} {R : SepProp}
    (hpc : s0.pc = c2MlkemMpl.base 5) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvM : mlkemInvMem c2MlkemMpl s0.mem) (hFr0 : ExecFrozen s0.mem)
    (hpre : s0.mem ⊨ genKeypair31216Spec.pre (seedA, seed, outPtr) s0 ∗ R) :
    ∃ sf : State,
      EmptyAvoid mpl s0 sf ∧
      Returned s0 sf ∧
      CalleeSavedPreserved s0 sf ∧
      (sf.mem ⊨ genKeypair31216Spec.post (seedA, seed, outPtr) s0 sf ∗ R) ∧
      s0.mem.KeepsFrozen sf.mem ∧
      ExecFrozen sf.mem := by
  have hsim : ∀ mpl', SpecSimulates (mlkemGenKeypairTermRawSpec mpl')
      (withMlKemRoOk mpl' genKeypair31216Spec) := by
    intro mpl' ⟨sA, sd, oP⟩ R1 st h
    dsimp only [withMlKemRoOk, genKeypair31216Spec] at h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨hro, h⟩ := h
    rw [sepConj_assoc, satisfies_pure_sepConj] at h
    obtain ⟨⟨hx0, hx1, hlen, hterm⟩, hspat⟩ := h
    refine ⟨(sA, sd, oP), R1, ?_, fun _ hout => hout⟩
    dsimp only [mlkemGenKeypairTermRawSpec]
    rw [sepConj_assoc, pure_sepConj_of_true ⟨hx0, hx1, hlen, hterm, hro⟩]
    exact hspat
  obtain ⟨sf, hvis, hret, ⟨_, hcs⟩, hpost, hkf, hnsp, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 5) (by decide)
      (blockSpec := mlkemGenKeypairTermRawSpec) (master := genKeypair31216Spec) c2MlkemMpl
      blk05_generate_keypair_raw_ok hsim rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun ⟨sA, sd, oP⟩ s h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes sA sd)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_memRegion oP 2400)
            (fun _ => rwOnlyHeap_stackAt s.sp 31216))) hh)
      (fun ⟨sA, sd, oP⟩ s h hh => by
        rcases SepProp.holds_sepConj_iff.mp hh with ⟨h1, _, _, rfl, hp1, _⟩
        obtain ⟨_, _, _, hslen, _⟩ := SepProp.holds_pure_iff.mp hp1
        exact boundedHeapIntervals_mono (k₁ := 0 + (1 + (1 + 1))) (by decide) (Nat.le_refl _)
          (boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj
              (fun _ => boundedHeapIntervals_pointsToBytes sA sd (by omega))
              (fun _ => boundedHeapIntervals_sepConj
                (fun _ => boundedHeapIntervals_memRegion oP 2400 (by decide))
                (fun _ => boundedHeapIntervals_stackAt s.sp 31216 (by decide)))) hh))
      (fun ⟨sA, sd, oP⟩ s0 _ h hh => rwOnlyHeap_sepConj
        (fun _ => rwOnlyHeap_pointsToBytes sA sd)
        (fun _ => rwOnlyHeap_sepConj
          (fun _ => rwOnlyHeap_pointsToBytes oP (mlkem768KeyPairWith sampleNtt sd))
          (fun _ => rwOnlyHeap_stackAt s0.sp 31216)) hh)
      hpc hrun hsp (c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2) hpre
  exact ⟨sf, emptyAvoid_of_activeVisitedIn hLs hvis, hret, hcs, hpost, hkf,
    ExecFrozen.of_perm_eq hFr0 (fun a => congrFun hnsp.2.1 a)⟩

private theorem active_call_blk03
    {mpl : MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} {args : MlkemBlk03Args} {R : SepProp}
    (hpc : s0.pc = c2MlkemMpl.base 3) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvM : mlkemInvMem c2MlkemMpl s0.mem) (hFr0 : ExecFrozen s0.mem)
    (hpre : s0.mem ⊨ mlkemBlk03TermRawSpec.pre args s0 ∗ R) :
    ∃ sf : State,
      EmptyAvoid mpl s0 sf ∧
      Returned s0 sf ∧
      CalleeSavedPreserved s0 sf ∧
      (sf.mem ⊨ mlkemBlk03TermRawSpec.post args s0 sf ∗ R) ∧
      s0.mem.KeepsFrozen sf.mem ∧
      ExecFrozen sf.mem := by
  have hsim : ∀ mpl', SpecSimulates (withMlKemRoOk mpl' mlkemBlk03TermRawSpec)
      (withMlKemRoOk mpl' mlkemBlk03TermRawSpec) :=
    fun _ a R1 _ h => ⟨a, R1, h, fun _ hout => hout⟩
  obtain ⟨sf, hvis, hret, ⟨_, hcs⟩, hpost, hkf, hnsp, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 3) (by decide)
      (blockSpec := fun mpl' => withMlKemRoOk mpl' mlkemBlk03TermRawSpec)
      (master := mlkemBlk03TermRawSpec) c2MlkemMpl
      blk03_encaps1_raw_ok hsim rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun a s h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes a.hdrA a.hdr64)
            (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes a.randA a.rand)
              (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_memRegion a.ret 961)
                (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_memRegion a.esA 2080)
                  (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_memRegion a.ssA 32)
                    (fun _ => rwOnlyHeap_stackAt s.sp 18160))))))) hh)
      (fun a s h hh => by
        rcases SepProp.holds_sepConj_iff.mp hh with ⟨_, h2, _, rfl, _, hq2⟩
        rcases SepProp.holds_sepConj_iff.mp hq2 with ⟨h2a, _, _, rfl, hp2a, _⟩
        obtain ⟨_, _, _, _, _, _, _, _, hhlen, hrlen⟩ := SepProp.holds_pure_iff.mp hp2a
        exact boundedHeapIntervals_mono (k₁ := 0 + (0 + (1 + (1 + (1 + (1 + (1 + 1)))))))
          (by decide) (Nat.le_refl _)
          (boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
            (fun _ => boundedHeapIntervals_sepConj (fun _ => boundedHeapIntervals_pure)
              (fun _ => boundedHeapIntervals_sepConj
                (fun _ => boundedHeapIntervals_pointsToBytes a.hdrA a.hdr64 (by omega))
                (fun _ => boundedHeapIntervals_sepConj
                  (fun _ => boundedHeapIntervals_pointsToBytes a.randA a.rand (by omega))
                  (fun _ => boundedHeapIntervals_sepConj
                    (fun _ => boundedHeapIntervals_memRegion a.ret 961 (by decide))
                    (fun _ => boundedHeapIntervals_sepConj
                      (fun _ => boundedHeapIntervals_memRegion a.esA 2080 (by decide))
                      (fun _ => boundedHeapIntervals_sepConj
                        (fun _ => boundedHeapIntervals_memRegion a.ssA 32 (by decide))
                        (fun _ => boundedHeapIntervals_stackAt s.sp 18160 (by decide)))))))) hh))
      (fun a s0 _ h hh => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure)
        (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes a.hdrA a.hdr64)
          (fun _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsToBytes a.randA a.rand)
            (fun _ => rwOnlyHeap_sepConj
              (fun _ => rwOnlyHeap_of_isBlock (IsBlock.pointsTo8 a.ret 0#8))
              (fun _ => rwOnlyHeap_sepConj
                (fun _ => rwOnlyHeap_pointsToBytes (a.ret + 1#64) (encaps1OutCt1 a.hdr64 a.rand))
                (fun _ => rwOnlyHeap_sepConj
                  (fun _ => rwOnlyHeap_pointsToBytes a.esA (encaps1OutEs a.hdr64 a.rand))
                  (fun _ => rwOnlyHeap_sepConj
                    (fun _ => rwOnlyHeap_pointsToBytes a.ssA (encaps1OutSs a.hdr64 a.rand))
                    (fun _ => rwOnlyHeap_stackAt s0.sp 18160))))))) hh)
      hpc hrun hsp (c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2) hpre
  exact ⟨sf, emptyAvoid_of_activeVisitedIn hLs hvis, hret, hcs, hpost, hkf,
    ExecFrozen.of_perm_eq hFr0 (fun a => congrFun hnsp.2.1 a)⟩

/-! ## 5. Placed Fetch Forwarding for `B10` & `B19` -/

@[instance_reducible]
private def c2MlKemPlacementInst : MlKemPlacement :=
  ⟨c2MlkemMpl, c2_mlkem_placeable⟩

section
set_option linter.literalFetch false
gen_placed_fetches blkPC10 blkLib10 blkTree10 blk10_code_eq blk10_tree_size
  via_placement blkPl10 blkPlaceable10 [0 → 92]
gen_placed_fetches blkPC19 blkLib19 blkTree19 blk19_code_eq blk19_tree_size
  via_placement blkPl19 blkPlaceable19 [0x0000 → 0x006c]
end

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blkPC10_rebase_fetch_base blkPC10_rebase_fetch_0x4 blkPC10_rebase_fetch_0x8
  blkPC10_rebase_fetch_0xc blkPC10_rebase_fetch_0x10 blkPC10_rebase_fetch_0x14
  blkPC10_rebase_fetch_0x18 blkPC10_rebase_fetch_0x1c blkPC10_rebase_fetch_0x20
  blkPC10_rebase_fetch_0x24 blkPC10_rebase_fetch_0x28 blkPC10_rebase_fetch_0x2c
  blkPC10_rebase_fetch_0x30 blkPC10_rebase_fetch_0x34 blkPC10_rebase_fetch_0x38
  blkPC10_rebase_fetch_0x3c blkPC10_rebase_fetch_0x40 blkPC10_rebase_fetch_0x44
  blkPC10_rebase_fetch_0x48 blkPC10_rebase_fetch_0x4c blkPC10_rebase_fetch_0x50
  blkPC10_rebase_fetch_0x54 blkPC10_rebase_fetch_0x58 blkPC10_rebase_fetch_0x5c
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blkPC19_rebase_fetch_base blkPC19_rebase_fetch_0x4 blkPC19_rebase_fetch_0x8
  blkPC19_rebase_fetch_0xc blkPC19_rebase_fetch_0x10 blkPC19_rebase_fetch_0x14
  blkPC19_rebase_fetch_0x18 blkPC19_rebase_fetch_0x1c blkPC19_rebase_fetch_0x20
  blkPC19_rebase_fetch_0x24 blkPC19_rebase_fetch_0x28 blkPC19_rebase_fetch_0x2c
  blkPC19_rebase_fetch_0x30 blkPC19_rebase_fetch_0x34 blkPC19_rebase_fetch_0x38
  blkPC19_rebase_fetch_0x3c blkPC19_rebase_fetch_0x40 blkPC19_rebase_fetch_0x44
  blkPC19_rebase_fetch_0x48 blkPC19_rebase_fetch_0x4c blkPC19_rebase_fetch_0x50
  blkPC19_rebase_fetch_0x54 blkPC19_rebase_fetch_0x58 blkPC19_rebase_fetch_0x5c
  blkPC19_rebase_fetch_0x60 blkPC19_rebase_fetch_0x64 blkPC19_rebase_fetch_0x68
  blkPC19_rebase_fetch_0x6c
)

private theorem blkPl10_ρ [MlKemPlacement] (sym : String) :
    blkPl10.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem blkPl19_ρ [MlKemPlacement] (sym : String) :
    blkPl19.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local simp, local arm64_norm, local wp_norm]
  blkPl10_ρ blkPl19_ρ resolve_blk03 resolve_blk05 resolve_blk28 resolve_blk29

private abbrev p10Prog [MlKemPlacement] : Program := blkPC10.rebase blkPl10.base (fun _ => none)
private abbrev p19Prog [MlKemPlacement] : Program := blkPC19.rebase blkPl19.base (fun _ => none)

private theorem p10Prog_eq_blockProgram [MlKemPlacement] :
    p10Prog = mlkemMultiLib.blockProgram mlkemMpl 10 := rfl

private theorem p19Prog_eq_blockProgram [MlKemPlacement] :
    p19Prog = mlkemMultiLib.blockProgram mlkemMpl 19 := rfl

private theorem p10Prog_code_len [MlKemPlacement] : p10Prog.code.length = 96 := by
  have h : (blkLib10.text.patched blkPl10).length = blkLib10.text.code.length :=
    CodeBlock.length_patched_of_aligned _
      (by rw [ProofLib.GenPlacedFetches.length_text_of_tree blk10_code_eq blk10_tree_size])
  change (blkLib10.text.patched blkPl10).length = 96
  rw [h, ProofLib.GenPlacedFetches.length_text_of_tree blk10_code_eq blk10_tree_size]

private theorem p19Prog_code_len [MlKemPlacement] : p19Prog.code.length = 112 := by
  have h : (blkLib19.text.patched blkPl19).length = blkLib19.text.code.length :=
    CodeBlock.length_patched_of_aligned _
      (by rw [ProofLib.GenPlacedFetches.length_text_of_tree blk19_code_eq blk19_tree_size])
  change (blkLib19.text.patched blkPl19).length = 112
  rw [h, ProofLib.GenPlacedFetches.length_text_of_tree blk19_code_eq blk19_tree_size]

private theorem firstWord_p10_fetch [MlKemPlacement] :
    (firstWordProg p10Prog).fetch blkPl10.base =
      (blkPC10.rebase blkPl10.base (fun _ => none)).fetch blkPl10.base :=
  firstWordProg_fetch_base
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 10) (by decide) (fun _ => none))
    (by rw [p10Prog_code_len]; decide)

private theorem firstWord_p10_fetch_zero [MlKemPlacement] :
    (firstWordProg p10Prog).fetch (blkPl10.base + 0#64) =
      (blkPC10.rebase blkPl10.base (fun _ => none)).fetch (blkPl10.base + 0#64) :=
  firstWordProg_fetch_zero
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 10) (by decide) (fun _ => none))
    (by rw [p10Prog_code_len]; decide)

private theorem firstWord_p19_fetch [MlKemPlacement] :
    (firstWordProg p19Prog).fetch blkPl19.base =
      (blkPC19.rebase blkPl19.base (fun _ => none)).fetch blkPl19.base :=
  firstWordProg_fetch_base
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 19) (by decide) (fun _ => none))
    (by rw [p19Prog_code_len]; decide)

private theorem firstWord_p19_fetch_zero [MlKemPlacement] :
    (firstWordProg p19Prog).fetch (blkPl19.base + 0#64) =
      (blkPC19.rebase blkPl19.base (fun _ => none)).fetch (blkPl19.base + 0#64) :=
  firstWordProg_fetch_zero
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 19) (by decide) (fun _ => none))
    (by rw [p19Prog_code_len]; decide)

private theorem dropFirst_p10_fetch [MlKemPlacement] (off : BitVec 64)
    (h1 : 4#64 ≤ off) (h2 : off < 256#64) :
    (dropFirstWord p10Prog).fetch (blkPl10.base + off) =
      (blkPC10.rebase blkPl10.base (fun _ => none)).fetch (blkPl10.base + off) :=
  dropFirstWord_fetch_bv
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 10) (by decide) (fun _ => none))
    off h1 h2

private theorem dropFirst_p19_fetch [MlKemPlacement] (off : BitVec 64)
    (h1 : 4#64 ≤ off) (h2 : off < 256#64) :
    (dropFirstWord p19Prog).fetch (blkPl19.base + off) =
      (blkPC19.rebase blkPl19.base (fun _ => none)).fetch (blkPl19.base + off) :=
  dropFirstWord_fetch_bv
    (externAt?_mlkemBlockProgram_ext_none mlkemMpl (j := 19) (by decide) (fun _ => none))
    off h1 h2

private theorem df10 [MlKemPlacement] (off : BitVec 64) {inst : Instr}
    (hf : (blkPC10.rebase blkPl10.base (fun _ => none)).fetch (blkPl10.base + off) = some inst)
    (h1 : 4#64 ≤ off := by decide) (h2 : off < 256#64 := by decide) :
    (dropFirstWord p10Prog).fetch (blkPl10.base + off) = some inst :=
  (dropFirst_p10_fetch off h1 h2).trans hf

private theorem df19 [MlKemPlacement] (off : BitVec 64) {inst : Instr}
    (hf : (blkPC19.rebase blkPl19.base (fun _ => none)).fetch (blkPl19.base + off) = some inst)
    (h1 : 4#64 ≤ off := by decide) (h2 : off < 256#64 := by decide) :
    (dropFirstWord p19Prog).fetch (blkPl19.base + off) = some inst :=
  (dropFirst_p19_fetch off h1 h2).trans hf

private theorem p10_eval_firstWord_pc [MlKemPlacement] :
    ∃ inst0 : Instr,
      p10Prog.fetch blkPl10.base = some inst0 ∧
      ∀ s : State, s.pc = blkPl10.base →
        (emptyStdProg.evalInst inst0 s).status = .Running →
        (emptyStdProg.evalInst inst0 s).pc = blkPl10.base + 4#64 := by
  refine ⟨_, blkPC10_rebase_fetch_base blkPl10.base (fun _ => none), ?_⟩
  intro s hpc hrun
  dsimp only [Program.evalInst, execInst, execInstWithSvc, execStp] at hrun ⊢
  repeat (split <;> simp_all [evalAddrMode, State.advancePC, State.writeReg64, State.setMem,
    State.setStatus])

private theorem p19_eval_firstWord_pc [MlKemPlacement] :
    ∃ inst0 : Instr,
      p19Prog.fetch blkPl19.base = some inst0 ∧
      ∀ s : State, s.pc = blkPl19.base →
        (emptyStdProg.evalInst inst0 s).status = .Running →
        (emptyStdProg.evalInst inst0 s).pc = blkPl19.base + 4#64 := by
  refine ⟨_, blkPC19_rebase_fetch_base blkPl19.base (fun _ => none), ?_⟩
  intro s hpc _hrun
  dsimp only [Program.evalInst, execInst, execInstWithSvc, execAddSubImm, State.advancePC,
    State.setPState, State.writeReg, State.writeReg64]
  rw [hpc]
  split <;> rfl

section C2FetchBounds
attribute [local instance] c2MlKemPlacementInst

private theorem p10Prog_no_wrap : p10Prog.base.toNat + p10Prog.code.length ≤ 2 ^ 64 := by
  rw [p10Prog_code_len]
  change (c2MlkemMpl.base 10).toNat + 96 ≤ 2 ^ 64
  decide

private theorem p19Prog_no_wrap : p19Prog.base.toNat + p19Prog.code.length ≤ 2 ^ 64 := by
  rw [p19Prog_code_len]
  change (c2MlkemMpl.base 19).toNat + 112 ≤ 2 ^ 64
  decide

private theorem p10Prog_codeLoaded_of_inv {m : Memory} (hInvM : mlkemInvMem c2MlkemMpl m) :
    p10Prog.CodeLoaded m :=
  hInvM.2.1 10 (by decide)

private theorem p19Prog_codeLoaded_of_inv {m : Memory} (hInvM : mlkemInvMem c2MlkemMpl m) :
    p19Prog.CodeLoaded m :=
  hInvM.2.1 19 (by decide)

private theorem dropFirst_p10_keep_false_of_c2Keep_false {pc : BitVec 64}
    (hc2 : c2MlkemKeep c2MlkemMpl pc = false) :
    progKeep (dropFirstWord p10Prog) pc = false :=
  dropFirstWord_keep_false_of_c2Keep_false (j := 10) (by decide) p10Prog_no_wrap hc2

private theorem dropFirst_p19_keep_false_of_c2Keep_false {pc : BitVec 64}
    (hc2 : c2MlkemKeep c2MlkemMpl pc = false) :
    progKeep (dropFirstWord p19Prog) pc = false :=
  dropFirstWord_keep_false_of_c2Keep_false (j := 19) (by decide) p19Prog_no_wrap hc2

private theorem c2_s5_outside_drop10_bounds :
    (mlkemS5Blocks.all fun k =>
      let bk := (c2MlkemMpl.base k).toNat
      let b10 := (c2MlkemMpl.base 10).toNat
      decide (bk < b10 + 4 ∨ b10 + 96 ≤ bk)) = true := by
  decide

private theorem c2_s5_outside_drop19_bounds :
    (mlkemS5Blocks.all fun k =>
      let bk := (c2MlkemMpl.base k).toNat
      let b19 := (c2MlkemMpl.base 19).toNat
      decide (bk < b19 + 4 ∨ b19 + 112 ≤ bk)) = true := by
  decide

private theorem dropFirst_p10_ne_s5 (pc : BitVec 64)
    (hk : progKeep (dropFirstWord p10Prog) pc = true) :
    ∀ k ∈ mlkemS5Blocks, pc ≠ c2MlkemMpl.base k := by
  have hnw := p10Prog_no_wrap
  have hlen := p10Prog_code_len
  unfold progKeep dropFirstWord at hk
  dsimp only at hk
  rw [List.length_drop, hlen] at hk
  have hlt : (pc - (p10Prog.base + 4#64)).toNat < 92 := of_decide_eq_true hk
  have hb_eq : p10Prog.base = c2MlkemMpl.base 10 := rfl
  rw [hb_eq] at hlt hnw
  rw [hlen] at hnw
  intro k hk_s5 heq
  have hbnd := of_decide_eq_true (List.all_eq_true.mp c2_s5_outside_drop10_bounds k hk_s5)
  subst heq
  bv_omega

private theorem dropFirst_p19_ne_s5 (pc : BitVec 64)
    (hk : progKeep (dropFirstWord p19Prog) pc = true) :
    ∀ k ∈ mlkemS5Blocks, pc ≠ c2MlkemMpl.base k := by
  have hnw := p19Prog_no_wrap
  have hlen := p19Prog_code_len
  unfold progKeep dropFirstWord at hk
  dsimp only at hk
  rw [List.length_drop, hlen] at hk
  have hlt : (pc - (p19Prog.base + 4#64)).toNat < 108 := of_decide_eq_true hk
  have hb_eq : p19Prog.base = c2MlkemMpl.base 19 := rfl
  rw [hb_eq] at hlt hnw
  rw [hlen] at hnw
  intro k hk_s5 heq
  have hbnd := of_decide_eq_true (List.all_eq_true.mp c2_s5_outside_drop19_bounds k hk_s5)
  subst heq
  bv_omega

private theorem dropFirst_p10_keep_active_false :
    progKeep (dropFirstWord p10Prog) (c2MlkemMpl.base 29) = false ∧
    progKeep (dropFirstWord p10Prog) (c2MlkemMpl.base 5) = false ∧
    progKeep (dropFirstWord p10Prog) (c2MlkemMpl.base 28) = false := by
  have hlen := p10Prog_code_len
  unfold progKeep dropFirstWord
  dsimp only
  rw [List.length_drop, hlen]
  change decide ((c2MlkemMpl.base 29 - (c2MlkemMpl.base 10 + 4#64)).toNat < 92) = false ∧
    decide ((c2MlkemMpl.base 5 - (c2MlkemMpl.base 10 + 4#64)).toNat < 92) = false ∧
    decide ((c2MlkemMpl.base 28 - (c2MlkemMpl.base 10 + 4#64)).toNat < 92) = false
  decide

private theorem dropFirst_p19_keep_b03_false :
    progKeep (dropFirstWord p19Prog) (c2MlkemMpl.base 3) = false := by
  have hlen := p19Prog_code_len
  unfold progKeep dropFirstWord
  dsimp only
  rw [List.length_drop, hlen]
  change decide ((c2MlkemMpl.base 3 - (c2MlkemMpl.base 19 + 4#64)).toNat < 108) = false
  decide

end C2FetchBounds

attribute [local irreducible] blkLib10 blkLib19

/-! ## 6. Row `B10` (`lsMlkemFromSeedSym`): `c2_mlkemFromSeed_snttStrictAvoid[_at]` -/

private def UnspilledSaved10 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem unspilledSaved10_of_cs {s0 s1 s2 : State}
    (h01 : UnspilledSaved10 s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    UnspilledSaved10 s0 s2 := by
  rcases h01 with ⟨h21, h22, h23, h24, h25, h26, h27, hv⟩
  rcases h12 with ⟨_, _, g21, g22, g23, g24, g25, g26, g27, _, _, gv⟩
  exact ⟨g21.trans h21, g22.trans h22, g23.trans h23, g24.trans h24,
    g25.trans h25, g26.trans h26, g27.trans h27, gv.trans hv⟩

private theorem unspilledSaved10_stripS_iff (keep : BitVec 64 → Bool) (s0 s : State) :
    UnspilledSaved10 s0 (stripS keep s) ↔ UnspilledSaved10 s0 s := by
  cases s; rfl

private theorem stackAt33664_split (sp0 : BitVec 64) :
    stackAt sp0 33664 =
      stackAt (sp0 - 2448#64) 31216 ∗
      memRegion (sp0 - 2448#64) 2400 ∗
      memRegion (sp0 - 48#64) 48 := by
  dsimp only [stackAt]
  have hsub : sp0 - 2448#64 - 31216#64 = sp0 - 33664#64 := by bv_omega
  change memRegion (sp0 - 33664#64) 33664 =
    memRegion (sp0 - 2448#64 - 31216#64) 31216 ∗
    memRegion (sp0 - 2448#64) 2400 ∗
    memRegion (sp0 - 48#64) 48
  rw [hsub,
    memRegion_split' (b := sp0 - 33664#64) (b' := sp0 - 2448#64) (n := 31216) (k := (2448 : Nat))
      rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp0 - 2448#64) (b' := sp0 - 48#64) (n := 2400) (k := 48)
      rfl (by bv_omega) (by omega)]

private theorem memRegion48_save_split (sp0 : BitVec 64) :
    memRegion (sp0 - 48#64) 48 =
      memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
      memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
      memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
  rw [memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]

private theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n 0#8)
  rwa [List.length_replicate] at h

private theorem vregs_writeReg64' (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).vregs = s.vregs := by cases s; rfl
private theorem vregs_setPC' (s : State) (pc : BitVec 64) :
    (s.setPC pc).vregs = s.vregs := by cases s; rfl
private theorem vregs_setMem' (s : State) (m : Memory) :
    (s.setMem m).vregs = s.vregs := by cases s; rfl
private theorem vregs_stripS' (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).vregs = s.vregs := by cases s; rfl

private theorem p10_seg_to_b29_wp [MlKemPlacement] (u : State) (seedA kpA : BitVec 64) (F : SepProp)
    (hpc : u.pc = blkPl10.base) (hrun : u.status = .Running) (hsp0 : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = seedA) (hx8 : u.readReg64 .x8 = kpA) :
    let u' := stripS (progKeep (firstWordProg p10Prog)) u
    SepWP (firstWordProg p10Prog) (blkPl10.base + 4#64) u'
      (memRegion (u.sp - 2448#64) 2400 ∗ memRegion (u.sp - 48#64) 48 ∗ F)
      (fun s1 P1 => ∀ m : Memory,
        SepWP (dropFirstWord p10Prog) (mlkemMpl.base 29) (s1.setMem m) P1
          (fun s2 P2 =>
            s2.sp = u.sp - 2448#64 ∧
            s2.spAligned = true ∧
            s2.readReg64 .lr = blkPl10.base + 0x0030#64 ∧
            s2.readReg64 .x0 = u.sp - 2448#64 ∧
            (s2.readReg32 .x1).truncate 8 = 0#8 ∧
            (s2.readReg64 .x2).toNat = 2400 ∧
            s2.readReg64 .x19 = seedA ∧
            s2.readReg64 .x20 = kpA ∧
            UnspilledSaved10 u s2 ∧
            (P2 ⊢ memRegion (u.sp - 2448#64) 2400 ∗ SavedFrame10 u.sp u ∗ F))) := by
  intro u'
  have hpc' : u'.pc = blkPl10.base := by simpa [u', stripS_pc] using hpc
  have hrun' : u'.status = .Running := by simpa [u', stripS_status] using hrun
  have hsp0' : u'.spAligned = true := by simpa [u', stripS_spAligned] using hsp0
  have hsp_eq : u'.sp = u.sp := stripS_sp _ u
  have hx0' : u'.readReg64 .x0 = seedA := by simpa [u', stripS_readReg64] using hx0
  have hx8' : u'.readReg64 .x8 = kpA := by simpa [u', stripS_readReg64] using hx8
  have hsp1_chk : ((u.sp - 2448#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub u.sp 2448#64 hsp0 (by decide)
  rw [memRegion48_save_split u.sp,
    memRegion_split' (b := u.sp - 2448#64) (b' := u.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 2448#64)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 48#64)); intro cfp
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 40#64)); intro clr
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 32#64)); intro c28
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 16#64)); intro c20
  sep_frame_apply (sepWP_elim_cell8 (a := u.sp - 8#64)); intro c19
  have _hf0 := firstWord_p10_fetch.trans (blkPC10_rebase_fetch_base blkPl10.base (fun _ => none))
  wp_step
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun']
  intro m
  have _f4  := df10 0x4#64  (blkPC10_rebase_fetch_0x4  blkPl10.base (fun _ => none))
  have _f8  := df10 0x8#64  (blkPC10_rebase_fetch_0x8  blkPl10.base (fun _ => none))
  have _fc  := df10 0xc#64  (blkPC10_rebase_fetch_0xc  blkPl10.base (fun _ => none))
  have _f10 := df10 0x10#64 (blkPC10_rebase_fetch_0x10 blkPl10.base (fun _ => none))
  have _f14 := df10 0x14#64 (blkPC10_rebase_fetch_0x14 blkPl10.base (fun _ => none))
  have _f18 := df10 0x18#64 (blkPC10_rebase_fetch_0x18 blkPl10.base (fun _ => none))
  have _f1c := df10 0x1c#64 (blkPC10_rebase_fetch_0x1c blkPl10.base (fun _ => none))
  have _f20 := df10 0x20#64 (blkPC10_rebase_fetch_0x20 blkPl10.base (fun _ => none))
  have _f24 := df10 0x24#64 (blkPC10_rebase_fetch_0x24 blkPl10.base (fun _ => none))
  have _f28 := df10 0x28#64 (blkPC10_rebase_fetch_0x28 blkPl10.base (fun _ => none))
  have _f2c := df10 0x2c#64 (blkPC10_rebase_fetch_0x2c blkPl10.base (fun _ => none))
  wp_steps 11
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun']
  have hfold2400 : ((u.sp - 2448#64) ↦₆₄ 0#64) ∗ memRegion (u.sp - 2440#64) 2392 ⊢
      memRegion (u.sp - 2448#64) 2400 := by
    rw [memRegion_split' (b := u.sp - 2448#64) (b' := u.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  have hreg_u' : ∀ r, u'.readReg64 r = u.readReg64 r := stripS_readReg64 _ u
  refine ⟨by wp_norm_lhs,
    by rw [State.spAligned]; wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by dsimp only [calleeSavedVRegs, VRegFile.calleeSaved, State.readVReg128]
        simp only [vregs_writeReg64', vregs_setPC', vregs_setMem', u', vregs_stripS']⟩,
    ?_⟩
  dsimp only [SavedFrame10]
  simp only [hreg_u']
  exact entails_sub hfold2400 (by sep_frame) (by sep_frame)

private theorem p10_seg_b29_to_b05_wp [MlKemPlacement]
    (u s : State) (seedA kpA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = blkPl10.base + 0x0030#64) (hrun : s.status = .Running)
    (hsp : s.sp = u.sp - 2448#64) (hsp0 : u.spAligned = true)
    (hx19 : s.readReg64 .x19 = seedA) (hx20 : s.readReg64 .x20 = kpA)
    (hus : UnspilledSaved10 u s) :
    let s' := stripS (progKeep (dropFirstWord p10Prog)) s
    SepWP (dropFirstWord p10Prog) (mlkemMpl.base 5) s' Rest
      (fun s1 P1 =>
        s1.sp = u.sp - 2448#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .lr = blkPl10.base + 0x003c#64 ∧
        s1.readReg64 .x0 = seedA ∧
        s1.readReg64 .x1 = u.sp - 2448#64 ∧
        s1.readReg64 .x20 = kpA ∧
        UnspilledSaved10 u s1 ∧
        (P1 ⊢ Rest)) := by
  intro s'
  have hpc' : s'.pc = blkPl10.base + 0x0030#64 := by simpa [s', stripS_pc] using hpc
  have hrun' : s'.status = .Running := by simpa [s', stripS_status] using hrun
  have hsp' : s'.sp = u.sp - 2448#64 := by simpa [s', stripS_sp] using hsp
  have hx19' : s'.readReg64 .x19 = seedA := by simpa [s', stripS_readReg64] using hx19
  have hx20' : s'.readReg64 .x20 = kpA := by simpa [s', stripS_readReg64] using hx20
  have hus' : UnspilledSaved10 u s' := (unspilledSaved10_stripS_iff _ u s).mpr hus
  have hsp1_chk : ((u.sp - 2448#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub u.sp 2448#64 hsp0 (by decide)
  rcases hus' with ⟨h21, h22, h23, h24, h25, h26, h27, hvregs⟩
  have _f30 := df10 0x30#64 (blkPC10_rebase_fetch_0x30 blkPl10.base (fun _ => none))
  have _f34 := df10 0x34#64 (blkPC10_rebase_fetch_0x34 blkPl10.base (fun _ => none))
  have _f38 := df10 0x38#64 (blkPC10_rebase_fetch_0x38 blkPl10.base (fun _ => none))
  wp_steps 3
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun']
  refine ⟨by wp_norm_lhs,
    by rw [State.spAligned]; wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by
       dsimp only [calleeSavedVRegs, VRegFile.calleeSaved, State.readVReg128] at hvregs ⊢
       simpa only [vregs_writeReg64', vregs_setPC', vregs_setMem'] using hvregs⟩,
    Entails.refl _⟩

private theorem p10_seg_b05_to_b28_wp [MlKemPlacement]
    (u s2 : State) (kpA : BitVec 64) (Rest : SepProp)
    (hpc2 : s2.pc = blkPl10.base + 0x003c#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = u.sp - 2448#64) (hsp0 : u.spAligned = true)
    (hx20 : s2.readReg64 .x20 = kpA) (hus2 : UnspilledSaved10 u s2) :
    let s2' := stripS (progKeep (dropFirstWord p10Prog)) s2
    SepWP (dropFirstWord p10Prog) (mlkemMpl.base 28) s2' Rest
      (fun s3 P3 =>
        s3.sp = u.sp - 2448#64 ∧
        s3.spAligned = true ∧
        s3.readReg64 .lr = blkPl10.base + 0x004c#64 ∧
        s3.readReg64 .x0 = kpA ∧
        s3.readReg64 .x1 = u.sp - 2448#64 ∧
        (s3.readReg64 .x2).toNat = 2400 ∧
        UnspilledSaved10 u s3 ∧
        (P3 ⊢ Rest)) := by
  intro s2'
  have hpc2' : s2'.pc = blkPl10.base + 0x003c#64 := by simpa [s2', stripS_pc] using hpc2
  have hrun2' : s2'.status = .Running := by simpa [s2', stripS_status] using hrun2
  have hsp2' : s2'.sp = u.sp - 2448#64 := by simpa [s2', stripS_sp] using hsp2
  have hx20' : s2'.readReg64 .x20 = kpA := by simpa [s2', stripS_readReg64] using hx20
  have hus2' : UnspilledSaved10 u s2' := (unspilledSaved10_stripS_iff _ u s2).mpr hus2
  have hsp1_chk : ((u.sp - 2448#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub u.sp 2448#64 hsp0 (by decide)
  rcases hus2' with ⟨h21, h22, h23, h24, h25, h26, h27, hvregs⟩
  have _f3c := df10 0x3c#64 (blkPC10_rebase_fetch_0x3c blkPl10.base (fun _ => none))
  have _f40 := df10 0x40#64 (blkPC10_rebase_fetch_0x40 blkPl10.base (fun _ => none))
  have _f44 := df10 0x44#64 (blkPC10_rebase_fetch_0x44 blkPl10.base (fun _ => none))
  have _f48 := df10 0x48#64 (blkPC10_rebase_fetch_0x48 blkPl10.base (fun _ => none))
  wp_steps 4
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun2']
  refine ⟨by wp_norm_lhs,
    by rw [State.spAligned]; wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    by wp_norm_lhs,
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by
       dsimp only [calleeSavedVRegs, VRegFile.calleeSaved, State.readVReg128] at hvregs ⊢
       simpa only [vregs_writeReg64', vregs_setPC', vregs_setMem'] using hvregs⟩,
    Entails.refl _⟩

private theorem p10_seg_b28_to_ret_wp [MlKemPlacement]
    (u s4 : State) (Rest : SepProp)
    (hpc4 : s4.pc = blkPl10.base + 0x004c#64) (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = u.sp - 2448#64) (hsp0 : u.spAligned = true) :
    let s4' := stripS (progKeep (dropFirstWord p10Prog)) s4
    SepWP (dropFirstWord p10Prog) (u.readReg64 .lr) s4'
      (SavedFrame10 u.sp u ∗ Rest)
      (fun sf _Pf => sf.sp = u.sp) := by
  intro s4'
  have hpc4' : s4'.pc = blkPl10.base + 0x004c#64 := by simpa [s4', stripS_pc] using hpc4
  have hrun4' : s4'.status = .Running := by simpa [s4', stripS_status] using hrun4
  have hsp4' : s4'.sp = u.sp - 2448#64 := by simpa [s4', stripS_sp] using hsp4
  have hsp_chk : ((u.sp - 48#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub u.sp 48#64 hsp0 (by decide)
  have _f4c := df10 0x4c#64 (blkPC10_rebase_fetch_0x4c blkPl10.base (fun _ => none))
  have _f50 := df10 0x50#64 (blkPC10_rebase_fetch_0x50 blkPl10.base (fun _ => none))
  have _f54 := df10 0x54#64 (blkPC10_rebase_fetch_0x54 blkPl10.base (fun _ => none))
  have _f58 := df10 0x58#64 (blkPC10_rebase_fetch_0x58 blkPl10.base (fun _ => none))
  have _f5c := df10 0x5c#64 (blkPC10_rebase_fetch_0x5c blkPl10.base (fun _ => none))
  refine SepWP.seq (mid := blkPl10.base + 80#64)
    (Mid := fun sm Pm => sm.sp = u.sp - 48#64 ∧ (Pm ⊢ SavedFrame10 u.sp u ∗ Rest))
    (prog := dropFirstWord p10Prog) (target := u.readReg64 .lr) ?_ ?_
  · wp_steps 1
    apply SepWP.done
    · wp_norm_lhs
    · simp [hrun4']
    exact ⟨by wp_norm_lhs, Entails.refl _⟩
  · intro sm Pm hpcm hrunm ⟨hspm, hPm⟩
    refine SepWP.weaken_pre hPm ?_
    dsimp only [SavedFrame10]
    wp_steps 4
    apply SepWP.done
    · wp_norm_lhs
    · simp [hrunm]
    wp_norm_lhs

section C2FromSeed
attribute [local instance] c2MlKemPlacementInst

/-- **Row `B10` (`lsMlkemFromSeedSym`, generic placement `mpl`):**
    When `mlkemSampleNttTermOf lsMlkemFromSeedSym u` holds at entry `u`, the 0-hook real program
    steps strictly avoiding `.Running ∧ MlKemSampleNttStuckAt mpl` from `u` to
    `mlkemFromSeedGhostAt c2MlkemMpl stk u` and preserves `ExecFrozen`. -/
theorem c2_mlkemFromSeed_snttStrictAvoid_at [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    (stk : Nat) (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) (u : State)
    (hTerm : mlkemSampleNttTermOf lsMlkemFromSeedSym u)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkemFromSeedSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemFromSeedGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (mlkemFromSeedGhostAt c2MlkemMpl stk u).mem)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemFromSeedGhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (mlkemFromSeedGhostAt c2MlkemMpl stk u).mem := by
  let _ := hkf
  have hpc10 : u.pc = c2MlkemMpl.base 10 := hpc.trans (c2_resolve_mlkem768FromSeed_eq hLs)
  have hInvM0 : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hTu : MlkemFromSeedStateTerminates u := by rwa [← mlkemSampleNttTermOf_mlkemFromSeed]
  have hActPre : ActiveRealPre
      (withLsRet (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental))) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  obtain ⟨_, hsp0, x, R0, hpre_ls⟩ := hActPre
  obtain ⟨hlr624, hpre_kfs⟩ := extract_withLsRet hpre_ls
  have hlr_out : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false :=
    c2_mlkemKeep_lr_false hLsLs hlr624
  dsimp only [keepsFs, mlkemFromSeedAtSpec] at hpre_kfs
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre_kfs
  obtain ⟨⟨hx0, hx8⟩, hspat0⟩ := hpre_kfs
  have hread_seed : readVecN u.mem x.seedA 64 = x.seed := readVecN_eq_of_pointsToBytes hspat0
  have hSeedTerm : Mlkem768FromSeedTerminates x.seed := by
    unfold MlkemFromSeedStateTerminates at hTu
    rwa [hx0, hread_seed] at hTu
  have hMatTerm : Shake128MatrixTerminates
      ((sha3_512List (x.seed.toList.take 32 ++ [3#8])).take 32) 3 :=
    mlkem768FromSeedTerminates_iff_list.mp hSeedTerm
  have hseed_len : x.seed.toList.length = 64 := x.seed.toList_length
  have hstk33664 : 33664 ≤ stk := hstk
  rw [stackAt_split_ge hstk33664 hfit, stackAt33664_split u.sp] at hspat0
  set R_top : SepProp := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 33664) ∗ R0
  set F0 : SepProp :=
    (x.seedA ↦ₛ x.seed.toList) ∗ stackAt (u.sp - 2448#64) 31216 ∗ memRegion x.kpA 2400
  have hsat_u : u.mem ⊨
      (memRegion (u.sp - 2448#64) 2400 ∗ memRegion (u.sp - 48#64) 48 ∗ F0) ∗ R_top :=
    Satisfies.mono (by dsimp only [F0, R_top]; sep_frame) hspat0
  have hlen10_4 : 4 ≤ p10Prog.code.length := by rw [p10Prog_code_len]; decide
  have hlen10 : 8 ≤ p10Prog.code.length := by rw [p10Prog_code_len]; decide
  -- Segment 1a: word 0 (u → sw1)
  obtain ⟨sw1, Pw1, hEA1a, hpc_w1, _, hkf1a, hFr_w1, hsat_w1, hwp_cont⟩ :=
    run_firstWord_sepWP (mpl := mpl) (j := 10) (by decide) p10Prog p10Prog_eq_blockProgram hlen10_4
      hpc10 (p10Prog_codeLoaded_of_inv hInvM0) hFr (not_badSntt_entry10 hLs hpc10 hTerm)
      p10_eval_firstWord_pc hsat_u
      (p10_seg_to_b29_wp u x.seedA x.kpA F0 hpc10 hrun hsp0 hx0 hx8)
  have hInvM_w1 : mlkemInvMem c2MlkemMpl sw1.mem := mlkemInvMem_of_keepsFrozen hkf1a hInvM0
  have hwp_d1 := hwp_cont (stripExecOutside (progKeep (dropFirstWord p10Prog)) sw1.mem)
  rw [stripS_setMem_eq] at hwp_d1
  -- Segment 1b: dropFirstWord (sw1 → s_pre29)
  obtain ⟨s_pre29, P_pre29, hEA1b, hpc_pre29, hrun_pre29, hkf1b, hFr_pre29, hsat_pre29,
      hsp_pre29, hspA_pre29, hlr_pre29, hx0_pre29, hx1_pre29, hx2_pre29, hx19_pre29, hx20_pre29,
      hus_pre29, hP_pre29⟩ :=
    run_dropFirstWord_sepWP hLs (j := 10) (by decide) p10Prog p10Prog_eq_blockProgram hlen10
      dropFirst_p10_ne_s5 dropFirst_p10_keep_active_false.1
      (p10Prog_codeLoaded_of_inv hInvM_w1) hFr_w1 hsat_w1 hwp_d1
  have hInvM_pre29 : mlkemInvMem c2MlkemMpl s_pre29.mem :=
    mlkemInvMem_of_keepsFrozen hkf1b hInvM_w1
  -- Segment 2: Active call B29 (memset 2400)
  have hpre29 : s_pre29.mem ⊨ memset2400Spec.pre (u.sp - 2448#64, 0#8) s_pre29 ∗
      (SavedFrame10 u.sp u ∗ F0 ∗ R_top) := by
    dsimp only [memset2400Spec]
    have hm1 := Satisfies.mono (sepConj_mono_left hP_pre29) hsat_pre29
    rw [sepConj_assoc, pure_sepConj_of_true
      ⟨by simpa [stripS_readReg64] using hx0_pre29,
       by simpa [stripS_readReg32] using hx1_pre29,
       by simpa [stripS_readReg64] using hx2_pre29⟩]
    exact Satisfies.mono (by sep_frame) hm1
  obtain ⟨s_post29, hEA2, hret29, hcs29, hpost29, hkf2, hFr_post29⟩ :=
    active_call_memset2400 hLs hpc_pre29 hrun_pre29
      (by simpa [stripS_spAligned] using hspA_pre29) hInvM_pre29 hFr_pre29 hpre29
  have hInvM_post29 : mlkemInvMem c2MlkemMpl s_post29.mem :=
    mlkemInvMem_of_keepsFrozen hkf2 hInvM_pre29
  have hpc_post29 : s_post29.pc = blkPl10.base + 0x0030#64 :=
    hret29.1.trans (by simpa [stripS_readReg64] using hlr_pre29)
  have hsp_post29 : s_post29.sp = u.sp - 2448#64 :=
    hret29.2.1.trans (by simpa [stripS_sp] using hsp_pre29)
  have hus_post29 : UnspilledSaved10 u s_post29 :=
    unspilledSaved10_of_cs ((unspilledSaved10_stripS_iff _ u s_pre29).mp hus_pre29) hcs29
  have hx19_post29 : s_post29.readReg64 .x19 = x.seedA :=
    hcs29.1.trans (by simpa [stripS_readReg64] using hx19_pre29)
  have hx20_post29 : s_post29.readReg64 .x20 = x.kpA :=
    hcs29.2.1.trans (by simpa [stripS_readReg64] using hx20_pre29)
  have hsat_post29 : s_post29.mem ⊨
      (memRegion (u.sp - 2448#64) 2400 ∗ SavedFrame10 u.sp u ∗ F0) ∗ R_top := by
    dsimp only [memset2400Spec] at hpost29
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost29
    have hm1 := Satisfies.mono
      (sepConj_mono_left (replicate_entails_memRegion (u.sp - 2448#64) 2400)) hpost29.2
    exact Satisfies.mono (by sep_frame) hm1
  -- Segment 3: dropFirstWord (s_post29 → s1 at B05)
  obtain ⟨s1, P1, hEA3, hpc_s1, hrun_s1, hkf3, hFr_s1, hsat_s1,
      hsp_s1, hspA_s1, hlr_s1, hx0_s1, hx1_s1, hx20_s1, hus_s1, hP1⟩ :=
    run_dropFirstWord_sepWP hLs (j := 10) (by decide) p10Prog p10Prog_eq_blockProgram hlen10
      dropFirst_p10_ne_s5 dropFirst_p10_keep_active_false.2.1
      (p10Prog_codeLoaded_of_inv hInvM_post29) hFr_post29 hsat_post29
      (p10_seg_b29_to_b05_wp u s_post29 x.seedA x.kpA _ hpc_post29 hret29.2.2
        hsp_post29 hsp0 hx19_post29 hx20_post29 hus_post29)
  have hInvM_s1 : mlkemInvMem c2MlkemMpl s1.mem := mlkemInvMem_of_keepsFrozen hkf3 hInvM_post29
  -- Segment 4: Active call B05 (generate_keypair_compressed)
  have hsp_s1_plain : s1.sp = u.sp - 2448#64 := by simpa [stripS_sp] using hsp_s1
  have hpre05 : s1.mem ⊨
      genKeypair31216Spec.pre (x.seedA, x.seed.toList, u.sp - 2448#64) s1 ∗
        (memRegion x.kpA 2400 ∗ SavedFrame10 u.sp u ∗ R_top) := by
    dsimp only [genKeypair31216Spec]
    have hm1 := Satisfies.mono (sepConj_mono_left hP1) hsat_s1
    rw [hsp_s1_plain, sepConj_assoc, pure_sepConj_of_true
      ⟨by simpa [stripS_readReg64] using hx0_s1,
       by simpa [stripS_readReg64] using hx1_s1,
       hseed_len, hMatTerm⟩]
    exact Satisfies.mono (by dsimp only [F0]; sep_frame) hm1
  obtain ⟨s2, hEA4, hret05, hcs05, hpost05, hkf4, hFr_s2⟩ :=
    active_call_blk05 hLs hpc_s1 hrun_s1
      (by simpa [stripS_spAligned] using hspA_s1) hInvM_s1 hFr_s1 hpre05
  have hInvM_s2 : mlkemInvMem c2MlkemMpl s2.mem := mlkemInvMem_of_keepsFrozen hkf4 hInvM_s1
  have hpc_s2 : s2.pc = blkPl10.base + 0x003c#64 :=
    hret05.1.trans (by simpa [stripS_readReg64] using hlr_s1)
  have hsp_s2 : s2.sp = u.sp - 2448#64 := hret05.2.1.trans hsp_s1_plain
  have hx20_s2 : s2.readReg64 .x20 = x.kpA :=
    hcs05.2.1.trans (by simpa [stripS_readReg64] using hx20_s1)
  have hus_s2 : UnspilledSaved10 u s2 :=
    unspilledSaved10_of_cs ((unspilledSaved10_stripS_iff _ u s1).mp hus_s1) hcs05
  -- Segment 5: dropFirstWord (s2 → s3 at B28)
  obtain ⟨s3, P3, hEA5, hpc_s3, hrun_s3, hkf5, hFr_s3, hsat_s3,
      hsp_s3, hspA_s3, hlr_s3, hx0_s3, hx1_s3, hx2_s3, _, hP3⟩ :=
    run_dropFirstWord_sepWP hLs (j := 10) (by decide) p10Prog p10Prog_eq_blockProgram hlen10
      dropFirst_p10_ne_s5 dropFirst_p10_keep_active_false.2.2
      (p10Prog_codeLoaded_of_inv hInvM_s2) hFr_s2 hpost05
      (p10_seg_b05_to_b28_wp u s2 x.kpA _ hpc_s2 hret05.2.2 hsp_s2 hsp0 hx20_s2 hus_s2)
  have hInvM_s3 : mlkemInvMem c2MlkemMpl s3.mem := mlkemInvMem_of_keepsFrozen hkf5 hInvM_s2
  -- Segment 6: Active call B28 (memcpy 2400)
  have hkp_len : (mlkem768KeyPairWith sampleNtt x.seed.toList).length = 2400 :=
    mlkem768KeyPairWith_length sampleNtt hseed_len
  have hpre28 : s3.mem ⊨
      memcpy2400Spec.pre (x.kpA, u.sp - 2448#64, mlkem768KeyPairWith sampleNtt x.seed.toList) s3 ∗
        (SavedFrame10 u.sp u ∗ (x.seedA ↦ₛ x.seed.toList) ∗ stackAt s1.sp 31216 ∗ R_top) := by
    dsimp only [memcpy2400Spec, genKeypair31216Spec] at hsat_s3 ⊢
    have hm1 := Satisfies.mono (sepConj_mono_left hP3) hsat_s3
    rw [sepConj_assoc, pure_sepConj_of_true
      ⟨by simpa [stripS_readReg64] using hx0_s3,
       by simpa [stripS_readReg64] using hx1_s3,
       by simpa [stripS_readReg64] using hx2_s3,
       hkp_len⟩]
    exact Satisfies.mono (by sep_frame) hm1
  obtain ⟨s4, hEA6, hret28, _, hpost28, hkf6, hFr_s4⟩ :=
    active_call_memcpy2400 hLs hpc_s3 hrun_s3
      (by simpa [stripS_spAligned] using hspA_s3) hInvM_s3 hFr_s3 hpre28
  have hInvM_s4 : mlkemInvMem c2MlkemMpl s4.mem := mlkemInvMem_of_keepsFrozen hkf6 hInvM_s3
  have hpc_s4 : s4.pc = blkPl10.base + 0x004c#64 :=
    hret28.1.trans (by simpa [stripS_readReg64] using hlr_s3)
  have hsp_s4 : s4.sp = u.sp - 2448#64 :=
    hret28.2.1.trans (by simpa [stripS_sp] using hsp_s3)
  have hsat_s4 : s4.mem ⊨
      (SavedFrame10 u.sp u ∗
        ((x.kpA ↦ₛ mlkem768KeyPairWith sampleNtt x.seed.toList) ∗
         ((u.sp - 2448#64) ↦ₛ mlkem768KeyPairWith sampleNtt x.seed.toList))) ∗
        ((x.seedA ↦ₛ x.seed.toList) ∗ stackAt s1.sp 31216 ∗ R_top) := by
    dsimp only [memcpy2400Spec] at hpost28
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost28
    exact Satisfies.mono (by sep_frame) hpost28.2
  -- Segment 7: dropFirstWord (s4 → sf at u.lr)
  have hlr_drop_out : progKeep (dropFirstWord p10Prog) (u.readReg64 .lr) = false :=
    dropFirst_p10_keep_false_of_c2Keep_false hlr_out
  obtain ⟨sf, _, hEA7, hpc_sf, hrun_sf, _, _, _, hsp_sf⟩ :=
    run_dropFirstWord_sepWP hLs (j := 10) (by decide) p10Prog p10Prog_eq_blockProgram hlen10
      dropFirst_p10_ne_s5 hlr_drop_out
      (p10Prog_codeLoaded_of_inv hInvM_s4) hFr_s4 hsat_s4
      (p10_seg_b28_to_ret_wp u s4 _ hpc_s4 hret28.2.2 hsp_s4 hsp0)
  have hEA_all : EmptyAvoid mpl u sf :=
    hEA1a.trans (hEA1b.trans (hEA2.trans (hEA3.trans (hEA4.trans (hEA5.trans (hEA6.trans hEA7))))))
  have hRet_sf : Returned u sf := ⟨hpc_sf, by simpa [stripS_sp] using hsp_sf, hrun_sf⟩
  -- Identify mlkemFromSeedGhostAt c2MlkemMpl stk u = sf via first-stop determinism
  let B := mlkemFromSeedSafeBridge stk hstk hfit
  have hSub := mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList stk hstk hfit (fun _ => none)
  obtain ⟨hGhostEq, hFrGhost⟩ :=
    mlkemBlockGhost_eq_of_emptyAvoid_ret B MlkemFromSeedStateTerminates
      (mlkemFromSeedStateTerminates_stripS_setPC (mlkemKeep c2MlkemMpl) (c2MlkemMpl.base 10))
      (subroutineOk_guarded_from_multi c2MlkemMpl B.hsym hSub fun y _ s hT hpre => by
        dsimp only [mlkemFromSeedAtSpec] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨⟨hy0, _⟩, hmem⟩ := hpre
        have hrd : readVecN s.mem y.seedA 64 = y.seed := readVecN_eq_of_pointsToBytes hmem
        unfold MlkemFromSeedCallTerminates
        unfold MlkemFromSeedStateTerminates at hT
        rwa [hy0, hrd] at hT)
      hLsLs hpc10 hTu hInvM0 hFr hnoex hEA_all hRet_sf
  have hEq : mlkemFromSeedGhostAt c2MlkemMpl stk u = sf := hGhostEq
  refine ⟨?_, hFrGhost⟩
  rw [hEq]
  exact hEA_all.toRealAvoid hExt W

/-- **Row `B10` (`lsMlkemFromSeedSym`, `lsmpl` specialization).** -/
theorem c2_mlkemFromSeed_snttStrictAvoid [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (stk : Nat) (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) (u : State)
    (hTerm : mlkemSampleNttTermOf lsMlkemFromSeedSym u)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsMlkemFromSeedSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemFromSeedGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (mlkemFromSeedGhostAt c2MlkemMpl stk u).mem)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt lsmpl z)
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemFromSeedGhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (mlkemFromSeedGhostAt c2MlkemMpl stk u).mem :=
  c2_mlkemFromSeed_snttStrictAvoid_at hLs hLs hExt stk hstk hfit W u
    hTerm hpc hrun hnoex hkf hFr hInv

end C2FromSeed

/-! ## 7. Row `B19` (`lsMlkemEncaps1Sym`): `c2_mlkemEncaps1_snttStrictAvoid[_at]` -/

private theorem stackAt18304_split (sp0 : BitVec 64) :
    stackAt sp0 18304 =
      stackAt (sp0 - 144#64) 18160 ∗
      memRegion (sp0 - 144#64) 128 ∗
      memRegion ((sp0 - 144#64) + 128#64) 16 := by
  unfold stackAt
  have h1 : (sp0 - 144#64) - BitVec.ofNat 64 18160 = sp0 - BitVec.ofNat 64 18304 := by bv_omega
  rw [h1,
    memRegion_split' (b := sp0 - BitVec.ofNat 64 18304) (b' := sp0 - 144#64)
      (n := 18160) (k := (144 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 144#64) (b' := (sp0 - 144#64) + 128#64)
      (n := 128) (k := (16 : Nat)) rfl (by bv_omega) (by decide)]

private def blk19Mid (h64 stk : List (BitVec 8)) : List (BitVec 8) :=
  ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 stk
        79 (ByteSlice.readLE h64 16 8)) 87 (ByteSlice.readLE h64 24 8))
      95 (ByteSlice.readLE h64 32 8)) 103 (ByteSlice.readLE h64 40 8))
    111 (ByteSlice.readLE h64 48 8)) 119 (ByteSlice.readLE h64 56 8))
  48 (ByteSlice.readLE h64 48 8)) 56 (ByteSlice.readLE h64 56 8))
  64 (ByteSlice.readLE h64 1 8)) 72 (ByteSlice.readLE h64 9 8)

private def blk19Fin (h64 mid : List (BitVec 8)) : List (BitVec 8) :=
  ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 (h64.getD 0 0#8))
      33 (ByteSlice.readLE mid 96 8)) 41 (ByteSlice.readLE mid 104 8))
    17 (ByteSlice.readLE mid 80 8)) 25 (ByteSlice.readLE mid 88 8))
  1 (ByteSlice.readLE mid 64 8)) 9 (ByteSlice.readLE mid 72 8)

private theorem write64_readLE8_step {bs h64 : List (BitVec 8)} (off src i : Nat)
    (hlen : bs.length = 128) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write64 bs off (ByteSlice.readLE h64 src 8)).getD i 0#8 =
      if off ≤ i ∧ i < off + 8 then h64.getD (src + (i - off)) 0#8 else bs.getD i 0#8 := by
  rw [ByteSlice.getD_write64 bs off _ i 0#8 (by omega)]
  split
  · rw [ByteSlice.extractLsb'_readLE h64 src 8 (i - off)]; simp [show i - off < 8 by omega]
  · rfl

private theorem write64_len128 {bs : List (BitVec 8)} {off : Nat} {v : BitVec 64}
    (h : bs.length = 128) (ho : off + 8 ≤ 128 := by decide) :
    (ByteSlice.write64 bs off v).length = 128 := by
  rw [ByteSlice.write64_length bs off v (by omega), h]

private theorem write8_len128 {bs : List (BitVec 8)} {off : Nat} {v : BitVec 8}
    (h : bs.length = 128) (ho : off + 1 ≤ 128 := by decide) :
    (ByteSlice.write8 bs off v).length = 128 := by
  rw [ByteSlice.write8_length bs off v (by omega), h]

private theorem getD_write8_128 {bs : List (BitVec 8)} (off : Nat) (v : BitVec 8) (i : Nat)
    (h : bs.length = 128) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write8 bs off v).getD i 0#8 = if i = off then v else bs.getD i 0#8 :=
  ByteSlice.getD_write8 bs off v i 0#8 (by omega)

private theorem getD_write64_disj_128 {bs : List (BitVec 8)} (off : Nat) (v : BitVec 64) (i : Nat)
    (h : bs.length = 128) (hd : off + 8 ≤ i) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write64 bs off v).getD i 0#8 = bs.getD i 0#8 := by
  rw [ByteSlice.getD_write64 bs off v i 0#8 (by omega)]
  simp [show ¬(off ≤ i ∧ i < off + 8) by omega]

private theorem readLE_congr {bs bs' : List (BitVec 8)} (off src n : Nat)
    (h : ∀ j, j < n → bs.getD (off + j) 0#8 = bs'.getD (src + j) 0#8) :
    ByteSlice.readLE bs off n = ByteSlice.readLE bs' src n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih (fun j hj => h j (by omega)),
      h n (by omega)]

section Blk19CopyHelpers
attribute [local irreducible] ByteSlice.write64 ByteSlice.write8 ByteSlice.readLE List.getD

private theorem readLE_m1_eq {mid : List (BitVec 8)} (b0 : BitVec 8) (w33 w41 : BitVec 64)
    (off : Nat) (hmid : mid.length = 128) (hoff : 64 ≤ off) :
    ByteSlice.readLE
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 b0) 33 w33) 41 w41) off 8 =
      ByteSlice.readLE mid off 8 := by
  apply readLE_congr; intro j _
  have h1 : (ByteSlice.write8 mid 0 b0).length = 128 := write8_len128 hmid
  have h2 : (ByteSlice.write64 (ByteSlice.write8 mid 0 b0) 33 w33).length = 128 := write64_len128 h1
  rw [getD_write64_disj_128 41 w41 _ h2 (by omega),
      getD_write64_disj_128 33 w33 _ h1 (by omega),
      getD_write8_128 0 b0 _ hmid]
  split <;> first | rfl | omega

private theorem blk19Mid_getD {h64 stk : List (BitVec 8)} (hs : stk.length = 128)
    (i : Nat) (_hi : i < 128) :
    (blk19Mid h64 stk).getD i 0#8 =
      if 64 ≤ i ∧ i < 80 then h64.getD (i - 63) 0#8
      else if 48 ≤ i ∧ i < 64 then h64.getD i 0#8
      else if 80 ≤ i ∧ i < 127 then h64.getD (i - 63) 0#8
      else stk.getD i 0#8 := by
  unfold blk19Mid
  repeat' (rw [write64_readLE8_step _ _ i (by repeat' first | exact hs | refine write64_len128 ?_)])
  repeat' (split <;> try omega)
  all_goals first | rfl | (congr 1; omega)

private theorem blk19Fin_entails (sp1 : BitVec 64) {h64 stk : List (BitVec 8)}
    (hh : h64.length = 64) (hs : stk.length = 128) :
    (sp1 ↦ₛ blk19Fin h64 (blk19Mid h64 stk)) ⊢
      (sp1 ↦ₛ h64) ∗ memRegion (sp1 + 64#64) 64 := by
  set mid := blk19Mid h64 stk with hmid_def
  have hmid : mid.length = 128 := by
    rw [hmid_def]; unfold blk19Mid; repeat' first | exact hs | refine write64_len128 ?_
  have hrmid (off src : Nat) (hb : 64 ≤ off ∧ off + 8 ≤ 127) (hsrc : src + 63 = off) :
      ByteSlice.readLE mid off 8 = ByteSlice.readLE h64 src 8 := by
    apply readLE_congr; intro j hj
    rw [hmid_def, blk19Mid_getD hs (off + j) (by omega)]
    repeat' (split <;> try omega)
    all_goals (congr 1; omega)
  set fin := blk19Fin h64 mid with hfin_def
  have hfin : fin.length = 128 := by
    rw [hfin_def]; unfold blk19Fin
    repeat' first | exact hmid | refine write64_len128 ?_ | refine write8_len128 ?_
  have htake : fin.take 64 = h64 := by
    apply ByteSlice.ext_getD (by simp [hfin, hh])
    intro i hi; simp only [List.length_take, hfin] at hi
    have hgi : (fin.take 64).getD i 0#8 = fin.getD i 0#8 := by
      unfold List.getD; rw [List.getElem?_take_of_lt (by omega)]
    rw [hgi, hfin_def]; unfold blk19Fin
    rw [hrmid 64 1 ⟨by omega, by omega⟩ (by omega), hrmid 72 9 ⟨by omega, by omega⟩ (by omega),
        hrmid 80 17 ⟨by omega, by omega⟩ (by omega), hrmid 88 25 ⟨by omega, by omega⟩ (by omega),
        hrmid 96 33 ⟨by omega, by omega⟩ (by omega), hrmid 104 41 ⟨by omega, by omega⟩ (by omega)]
    repeat' (rw [write64_readLE8_step _ _ i
      (by repeat' first | exact hmid | refine write64_len128 ?_ | refine write8_len128 ?_)])
    rw [getD_write8_128 0 _ i hmid, hmid_def, blk19Mid_getD hs i (by omega)]
    repeat' (split <;> try omega)
    all_goals first | rfl | (congr 1; omega)
  conv => lhs; rw [← List.take_append_drop 64 fin]
  rw [pointsToBytes_append, htake, hh]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion_of_length (by simp [hfin]))

private theorem blk19Mid_len {h64 stk : List (BitVec 8)} (hs : stk.length = 128) :
    (blk19Mid h64 stk).length = 128 := by
  unfold blk19Mid; repeat' first | exact hs | refine write64_len128 ?_

end Blk19CopyHelpers

private theorem p19_short_wp [MlKemPlacement]
    (u : State) (retA : BitVec 64) (hdrLen : Nat) (Rest : SepProp)
    (hlt : hdrLen < 64)
    (hpc : u.pc = blkPl19.base) (hrun : u.status = .Running)
    (hx8 : u.readReg64 .x8 = retA) (hx1 : (u.readReg64 .x1).toNat = hdrLen) :
    let u' := stripS (progKeep (firstWordProg p19Prog)) u
    SepWP (firstWordProg p19Prog) (blkPl19.base + 4#64) u'
      (memRegion retA 961 ∗ Rest)
      (fun s1 P1 => ∀ m : Memory,
        SepWP (dropFirstWord p19Prog) (u.readReg64 .lr) (s1.setMem m) P1
          (fun sf _Pf => sf.sp = u.sp)) := by
  intro u'
  have hpc' : u'.pc = blkPl19.base := by simpa [u', stripS_pc] using hpc
  have hrun' : u'.status = .Running := by simpa [u', stripS_status] using hrun
  have hx8' : u'.readReg64 .x8 = retA := by simpa [u', stripS_readReg64] using hx8
  have hx1' : (u'.readReg64 .x1).toNat = hdrLen := by simpa [u', stripS_readReg64] using hx1
  have hlr' : u'.readReg64 .lr = u.readReg64 .lr := stripS_readReg64 _ u .lr
  have hsp' : u'.sp = u.sp := stripS_sp _ u
  rw [memRegion_split' (b := retA) (b' := retA + 1#64) (n := 1) (k := (960 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := retA + 1#64) (b' := retA + 2#64) (n := 1) (k := (959 : Nat)) rfl (by bv_omega) (by decide),
      sepConj_assoc, sepConj_assoc]
  apply sepWP_elim_byte; intro b0
  rw [← sepConj_assoc, sepConj_comm (retA ↦₈ b0), sepConj_assoc]
  apply sepWP_elim_byte; intro b1
  refine SepWP.weaken_pre (P' := (retA ↦ₛ [b0, b1]) ∗ memRegion (retA + 2#64) 959 ∗ Rest)
    (by simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]; sep_frame) ?_
  simp only [Reg.x1] at hx1'
  have _hf0 := firstWord_p19_fetch.trans (blkPC19_rebase_fetch_base blkPl19.base (fun _ => none))
  wp_step
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun']
  intro m
  have _f4  := df19 0x4#64  (blkPC19_rebase_fetch_0x4  blkPl19.base (fun _ => none))
  have _f8  := df19 0x8#64  (blkPC19_rebase_fetch_0x8  blkPl19.base (fun _ => none))
  have _fc  := df19 0xc#64  (blkPC19_rebase_fetch_0xc  blkPl19.base (fun _ => none))
  have _f10 := df19 0x10#64 (blkPC19_rebase_fetch_0x10 blkPl19.base (fun _ => none))
  refine step_bCond_not_taken (pc := blkPl19.base + 4#64) (off := 16#64)
    (dst := blkPl19.base + 8#64) (c := .HI)
    (by wp_norm_lhs) (by simp [hrun']) (by exact _f4)
    (by simp only [wp_norm, arm64_norm, conditionHolds_hi_subsPState64, BitVec.ult]
        rw [hx1']; exact decide_eq_false (by omega))
    (by bv_omega) ?_
  wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun']) (by wp_norm_lhs)

private theorem p19_prologue_wp [MlKemPlacement]
    (u : State) (a : MlkemEncaps1Args) (Rest : SepProp)
    (hge : 64 ≤ a.hdr.length)
    (hpc : u.pc = blkPl19.base) (hrun : u.status = .Running) (hsp0 : u.spAligned = true)
    (hx8 : u.readReg64 .x8 = a.ret) (hx0 : u.readReg64 .x0 = a.hdrA)
    (hx1 : (u.readReg64 .x1).toNat = a.hdr.length)
    (hx2 : u.readReg64 .x2 = a.randA) (hx3 : u.readReg64 .x3 = a.esA)
    (hx4 : u.readReg64 .x4 = 2080#64) (hx5 : u.readReg64 .x5 = a.ssA)
    (hx6 : u.readReg64 .x6 = 32#64) :
    let u' := stripS (progKeep (firstWordProg p19Prog)) u
    SepWP (firstWordProg p19Prog) (blkPl19.base + 4#64) u'
      ((a.hdrA ↦ₛ a.hdr.take 64) ∗
        memRegion (u.sp - 144#64) 128 ∗
        memRegion ((u.sp - 144#64) + 128#64) 16 ∗ Rest)
      (fun s1 P1 => ∀ m : Memory,
        SepWP (dropFirstWord p19Prog) (mlkemMpl.base 3) (s1.setMem m) P1
          (fun s2 P2 =>
            s2.sp = u.sp - 144#64 ∧
            s2.spAligned = true ∧
            s2.readReg64 .lr = blkPl19.base + 0x0064#64 ∧
            s2.readReg64 .x0 = a.ret ∧ s2.readReg64 .x1 = u.sp - 144#64 ∧
            s2.readReg64 .x2 = a.randA ∧ s2.readReg64 .x3 = a.esA ∧
            s2.readReg64 .x4 = 2080#64 ∧ s2.readReg64 .x5 = a.ssA ∧
            s2.readReg64 .x6 = 32#64 ∧
            (P2 ⊢ (a.hdrA ↦ₛ a.hdr.take 64) ∗
              ((u.sp - 144#64) ↦ₛ a.hdr.take 64) ∗
              memRegion ((u.sp - 144#64) + 64#64) 64 ∗
              SavedFrame19 ((u.sp - 144#64) + 128#64) u ∗ Rest))) := by
  intro u'
  have hpc' : u'.pc = blkPl19.base := by simpa [u', stripS_pc] using hpc
  have hrun' : u'.status = .Running := by simpa [u', stripS_status] using hrun
  have hsp0' : u'.spAligned = true := by simpa [u', stripS_spAligned] using hsp0
  have hsp_eq : u'.sp = u.sp := stripS_sp _ u
  have hx8' : u'.readReg64 .x8 = a.ret := by simpa [u', stripS_readReg64] using hx8
  have hx0' : u'.readReg64 .x0 = a.hdrA := by simpa [u', stripS_readReg64] using hx0
  have hx1' : (u'.readReg64 .x1).toNat = a.hdr.length := by simpa [u', stripS_readReg64] using hx1
  have hx2' : u'.readReg64 .x2 = a.randA := by simpa [u', stripS_readReg64] using hx2
  have hx3' : u'.readReg64 .x3 = a.esA := by simpa [u', stripS_readReg64] using hx3
  have hx4' : u'.readReg64 .x4 = 2080#64 := by simpa [u', stripS_readReg64] using hx4
  have hx5' : u'.readReg64 .x5 = a.ssA := by simpa [u', stripS_readReg64] using hx5
  have hx6' : u'.readReg64 .x6 = 32#64 := by simpa [u', stripS_readReg64] using hx6
  have hh64 : (a.hdr.take 64).length = 64 := List.length_take_of_le hge
  generalize a.hdr.take 64 = h64 at hh64 ⊢
  rw [memRegion_split' (b := (u.sp - 144#64) + 128#64) (b' := (u.sp - 144#64) + 136#64)
        (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  apply SepWP.memRegion8_cell ((u.sp - 144#64) + 128#64); intro sf0
  apply SepWP.memRegion8_cell ((u.sp - 144#64) + 136#64); intro sf1
  apply SepWP.of_memRegion_vecRangeMem 8 (u.sp - 144#64); intro stkV
  rw [vecRangeMem_eq_pointsToBytes]
  have hstk128 : (vecRangeBytes 8 stkV).length = 128 := vecRangeBytes_length 8 stkV
  generalize vecRangeBytes 8 stkV = stk0 at hstk128 ⊢
  simp only [Reg.x1] at hx1'
  have _hf0 := firstWord_p19_fetch.trans (blkPC19_rebase_fetch_base blkPl19.base (fun _ => none))
  wp_step
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun']
  intro m
  have _f4  := df19 0x4#64  (blkPC19_rebase_fetch_0x4  blkPl19.base (fun _ => none))
  have _f14 := df19 0x14#64 (blkPC19_rebase_fetch_0x14 blkPl19.base (fun _ => none))
  have _f18 := df19 0x18#64 (blkPC19_rebase_fetch_0x18 blkPl19.base (fun _ => none))
  have _f1c := df19 0x1c#64 (blkPC19_rebase_fetch_0x1c blkPl19.base (fun _ => none))
  have _f20 := df19 0x20#64 (blkPC19_rebase_fetch_0x20 blkPl19.base (fun _ => none))
  have _f24 := df19 0x24#64 (blkPC19_rebase_fetch_0x24 blkPl19.base (fun _ => none))
  have _f28 := df19 0x28#64 (blkPC19_rebase_fetch_0x28 blkPl19.base (fun _ => none))
  have _f2c := df19 0x2c#64 (blkPC19_rebase_fetch_0x2c blkPl19.base (fun _ => none))
  have _f30 := df19 0x30#64 (blkPC19_rebase_fetch_0x30 blkPl19.base (fun _ => none))
  have _f34 := df19 0x34#64 (blkPC19_rebase_fetch_0x34 blkPl19.base (fun _ => none))
  have _f38 := df19 0x38#64 (blkPC19_rebase_fetch_0x38 blkPl19.base (fun _ => none))
  have _f3c := df19 0x3c#64 (blkPC19_rebase_fetch_0x3c blkPl19.base (fun _ => none))
  have _f40 := df19 0x40#64 (blkPC19_rebase_fetch_0x40 blkPl19.base (fun _ => none))
  have _f44 := df19 0x44#64 (blkPC19_rebase_fetch_0x44 blkPl19.base (fun _ => none))
  have _f48 := df19 0x48#64 (blkPC19_rebase_fetch_0x48 blkPl19.base (fun _ => none))
  have _f4c := df19 0x4c#64 (blkPC19_rebase_fetch_0x4c blkPl19.base (fun _ => none))
  have _f50 := df19 0x50#64 (blkPC19_rebase_fetch_0x50 blkPl19.base (fun _ => none))
  have _f54 := df19 0x54#64 (blkPC19_rebase_fetch_0x54 blkPl19.base (fun _ => none))
  have _f58 := df19 0x58#64 (blkPC19_rebase_fetch_0x58 blkPl19.base (fun _ => none))
  have _f5c := df19 0x5c#64 (blkPC19_rebase_fetch_0x5c blkPl19.base (fun _ => none))
  have _f60 := df19 0x60#64 (blkPC19_rebase_fetch_0x60 blkPl19.base (fun _ => none))
  refine step_bCond_taken (pc := blkPl19.base + 4#64) (off := 16#64)
    (dst := blkPl19.base + 20#64) (c := .HI)
    (by wp_norm_lhs) (by simp [hrun']) (by exact _f4)
    (by simp only [wp_norm, arm64_norm, conditionHolds_hi_subsPState64, BitVec.ult]
        rw [hx1']; exact decide_eq_true (by omega))
    (by bv_omega) ?_
  rw [← hsp_eq]
  wp_steps 13
  have hmid_fold : ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 stk0
        79 (ByteSlice.readLE h64 16 8)) 87 (ByteSlice.readLE h64 24 8))
      95 (ByteSlice.readLE h64 32 8)) 103 (ByteSlice.readLE h64 40 8))
    111 (ByteSlice.readLE h64 48 8)) 119 (ByteSlice.readLE h64 56 8))
    48 (ByteSlice.readLE h64 48 8)) 56 (ByteSlice.readLE h64 56 8))
    64 (ByteSlice.readLE h64 1 8)) 72 (ByteSlice.readLE h64 9 8) = blk19Mid h64 stk0 := rfl
  rw [hmid_fold]
  have hmid128 : (blk19Mid h64 stk0).length = 128 := blk19Mid_len hstk128
  generalize hmid_eq : blk19Mid h64 stk0 = mid at hmid128 ⊢
  wp_steps 7
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun'])
    ⟨by wp_norm_lhs,
     by rw [State.spAligned] at hsp0' ⊢; simp only [wp_norm, arm64_norm]; exact hsp0',
     by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
  rw [readLE_m1_eq _ _ _ 64 hmid128 (by decide),
      readLE_m1_eq _ _ _ 72 hmid128 (by decide)]
  have hfin_fold : ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 (h64.getD 0 0#8))
      33 (ByteSlice.readLE mid 96 8)) 41 (ByteSlice.readLE mid 104 8))
    17 (ByteSlice.readLE mid 80 8)) 25 (ByteSlice.readLE mid 88 8))
    1 (ByteSlice.readLE mid 64 8)) 9 (ByteSlice.readLE mid 72 8) = blk19Fin h64 mid := rfl
  rw [hfin_fold, ← hmid_eq]
  dsimp only [SavedFrame19, Reg.x29, Reg.lr]
  have ha16 : (u.sp - 144#64) + 128#64 = u.sp - 16#64 := by bv_omega
  have hreg_u' : ∀ r, u'.readReg64 r = u.readReg64 r := stripS_readReg64 _ u
  simp only [hsp_eq, ha16, hreg_u']
  refine Entails.trans (sepConj_mono_left (blk19Fin_entails (u.sp - 144#64) hh64 hstk128)) ?_
  sep_frame

private theorem p19_epilogue_wp [MlKemPlacement] (u s : State) (Rest : SepProp)
    (hpc : s.pc = blkPl19.base + 0x0064#64) (hrun : s.status = .Running)
    (hsp : s.sp = u.sp - 144#64) (hsp0 : u.spAligned = true) :
    let s' := stripS (progKeep (dropFirstWord p19Prog)) s
    SepWP (dropFirstWord p19Prog) (u.readReg64 .lr) s'
      (SavedFrame19 ((u.sp - 144#64) + 128#64) u ∗ Rest)
      (fun sf _Pf => sf.sp = u.sp) := by
  intro s'
  have hpc' : s'.pc = blkPl19.base + 0x0064#64 := by simpa [s', stripS_pc] using hpc
  have hrun' : s'.status = .Running := by simpa [s', stripS_status] using hrun
  have hsp' : s'.sp = u.sp - 144#64 := by simpa [s', stripS_sp] using hsp
  have hspA : s'.spAligned = true := by
    rw [State.spAligned, hsp']
    exact spAligned_sub u.sp 144#64 hsp0 (by decide)
  have _f64 := df19 0x64#64 (blkPC19_rebase_fetch_0x64 blkPl19.base (fun _ => none))
  have _f68 := df19 0x68#64 (blkPC19_rebase_fetch_0x68 blkPl19.base (fun _ => none))
  have _f6c := df19 0x6c#64 (blkPC19_rebase_fetch_0x6c blkPl19.base (fun _ => none))
  dsimp only [SavedFrame19]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)

section C2Encaps1
attribute [local instance] c2MlKemPlacementInst

/-- **Row `B19` (`lsMlkemEncaps1Sym`, generic placement `mpl`):**
    When `mlkemSampleNttTermOf lsMlkemEncaps1Sym u` holds at entry `u`, the 0-hook real program
    steps strictly avoiding `.Running ∧ MlKemSampleNttStuckAt mpl` from `u` to
    `mlkemEncaps1GhostAt c2MlkemMpl stk u` and preserves `ExecFrozen`. -/
theorem c2_mlkemEncaps1_snttStrictAvoid_at [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    (stk : Nat) (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) (u : State)
    (hTerm : mlkemSampleNttTermOf lsMlkemEncaps1Sym u)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkemEncaps1Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemEncaps1GhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (mlkemEncaps1GhostAt c2MlkemMpl stk u).mem)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemEncaps1GhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (mlkemEncaps1GhostAt c2MlkemMpl stk u).mem := by
  let _ := hkf
  have hpc19 : u.pc = c2MlkemMpl.base 19 := hpc.trans (c2_resolve_mlkem768Encaps1_eq hLs)
  have hInvM0 : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hTu : MlkemEncaps1StateTerminates u := by rwa [← mlkemSampleNttTermOf_mlkemEncaps1]
  have hActPre : ActiveRealPre
      (withLsRet (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental))) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  obtain ⟨_, hsp0, x, R0, hpre_ls⟩ := hActPre
  obtain ⟨hlr624, hpre_kfs⟩ := extract_withLsRet hpre_ls
  have hlr_out : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false :=
    c2_mlkemKeep_lr_false hLsLs hlr624
  have hlr_drop_out : progKeep (dropFirstWord p19Prog) (u.readReg64 .lr) = false :=
    dropFirst_p19_keep_false_of_c2Keep_false hlr_out
  dsimp only [keepsFs, mlkemEncaps1AtSpec] at hpre_kfs
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre_kfs
  obtain ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hspat0⟩ := hpre_kfs
  obtain ⟨_, hread_hdr⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hspat0
  have hHdrTerm : Mlkem768Encaps1Terminates x.hdr := by
    unfold MlkemEncaps1StateTerminates at hTu
    rwa [hx0, hx1, hread_hdr] at hTu
  have hstk18304 : 18304 ≤ stk := hstk
  rw [stackAt_split_ge hstk18304 hfit] at hspat0
  set R_top : SepProp := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 18304) ∗ R0
  have hlen19_4 : 4 ≤ p19Prog.code.length := by rw [p19Prog_code_len]; decide
  have hlen19 : 8 ≤ p19Prog.code.length := by rw [p19Prog_code_len]; decide
  -- Build avoiding return witness (sf : State, EmptyAvoid mpl u sf ∧ Returned u sf)
  have hRunAvoid : ∃ sf : State, EmptyAvoid mpl u sf ∧ Returned u sf := by
    by_cases hlt : x.hdr.length < 64
    · -- Short-header error branch (hdr.length < 64)
      have hsat_short : u.mem ⊨
          (memRegion x.ret 961 ∗
            ((x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
             memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗ stackAt u.sp 18304)) ∗ R_top :=
        Satisfies.mono (by dsimp only [R_top]; sep_frame) hspat0
      obtain ⟨sw1, Pw1, hEA1, _, _, hkf1, hFr_w1, hsat_w1, hwp_cont⟩ :=
        run_firstWord_sepWP (mpl := mpl) (j := 19) (by decide) p19Prog p19Prog_eq_blockProgram hlen19_4
          hpc19 (p19Prog_codeLoaded_of_inv hInvM0) hFr (not_badSntt_entry19 hLs hpc19 hTerm)
          p19_eval_firstWord_pc hsat_short
          (p19_short_wp u x.ret x.hdr.length _ hlt hpc19 hrun hx8 hx1)
      have hInvM_w1 : mlkemInvMem c2MlkemMpl sw1.mem := mlkemInvMem_of_keepsFrozen hkf1 hInvM0
      have hwp_d1 := hwp_cont (stripExecOutside (progKeep (dropFirstWord p19Prog)) sw1.mem)
      rw [stripS_setMem_eq] at hwp_d1
      obtain ⟨sf, _, hEA2, hpc_sf, hrun_sf, _, _, _, hsp_sf⟩ :=
        run_dropFirstWord_sepWP hLs (j := 19) (by decide) p19Prog p19Prog_eq_blockProgram hlen19
          dropFirst_p19_ne_s5 hlr_drop_out
          (p19Prog_codeLoaded_of_inv hInvM_w1) hFr_w1 hsat_w1 hwp_d1
      exact ⟨sf, hEA1.trans hEA2, ⟨hpc_sf, by simpa [stripS_sp] using hsp_sf, hrun_sf⟩⟩
    · -- Long-header branch (64 ≤ hdr.length): prologue → B03 → epilogue
      have hge : 64 ≤ x.hdr.length := Nat.le_of_not_lt hlt
      have hMatTerm : Shake128MatrixTerminates (x.hdr.take 32) 3 :=
        Mlkem768Encaps1Terminates_matrix hHdrTerm hge
      have htake32_eq : (x.hdr.take 64).take 32 = x.hdr.take 32 := by
        rw [List.take_take, Nat.min_eq_left (by decide)]
      have hMatTerm64 : Shake128MatrixTerminates ((x.hdr.take 64).take 32) 3 := by
        rwa [htake32_eq]
      have hh64_len : (x.hdr.take 64).length = 64 := List.length_take_of_le hge
      let a19 : MlkemEncaps1Args :=
        { ret := x.ret, hdrA := x.hdrA, hdr := x.hdr, randA := x.randA,
          rand := x.rand, esA := x.esA, ssA := x.ssA }
      have hhdr_split : (x.hdrA ↦ₛ x.hdr) =
          (x.hdrA ↦ₛ x.hdr.take 64) ∗ ((x.hdrA + 64#64) ↦ₛ x.hdr.drop 64) := by
        conv => lhs; rw [← List.take_append_drop 64 x.hdr]
        rw [pointsToBytes_append, hh64_len]
      rw [hhdr_split, stackAt18304_split u.sp] at hspat0
      set RestPro : SepProp :=
        ((x.hdrA + 64#64) ↦ₛ x.hdr.drop 64) ∗ (x.randA ↦ₛ x.rand.toList) ∗
        memRegion x.ret 961 ∗ memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗
        stackAt (u.sp - 144#64) 18160
      have hsat_long : u.mem ⊨
          ((a19.hdrA ↦ₛ a19.hdr.take 64) ∗
            memRegion (u.sp - 144#64) 128 ∗
            memRegion ((u.sp - 144#64) + 128#64) 16 ∗ RestPro) ∗ R_top :=
        Satisfies.mono (by dsimp only [a19, RestPro, R_top]; sep_frame) hspat0
      obtain ⟨sw1, Pw1, hEA1a, _, _, hkf1a, hFr_w1, hsat_w1, hwp_cont⟩ :=
        run_firstWord_sepWP (mpl := mpl) (j := 19) (by decide) p19Prog p19Prog_eq_blockProgram hlen19_4
          hpc19 (p19Prog_codeLoaded_of_inv hInvM0) hFr (not_badSntt_entry19 hLs hpc19 hTerm)
          p19_eval_firstWord_pc hsat_long
          (p19_prologue_wp u a19 RestPro hge hpc19 hrun hsp0 hx8 hx0 hx1 hx2 hx3 hx4 hx5 hx6)
      have hInvM_w1 : mlkemInvMem c2MlkemMpl sw1.mem := mlkemInvMem_of_keepsFrozen hkf1a hInvM0
      have hwp_d1 := hwp_cont (stripExecOutside (progKeep (dropFirstWord p19Prog)) sw1.mem)
      rw [stripS_setMem_eq] at hwp_d1
      obtain ⟨s1, P1, hEA1b, hpc_s1, hrun_s1, hkf1b, hFr_s1, hsat_s1,
          hsp_s1, hspA_s1, hlr_s1, hx0_s1, hx1_s1, hx2_s1, hx3_s1, hx4_s1, hx5_s1, hx6_s1,
          hP1⟩ :=
        run_dropFirstWord_sepWP hLs (j := 19) (by decide) p19Prog p19Prog_eq_blockProgram hlen19
          dropFirst_p19_ne_s5 dropFirst_p19_keep_b03_false
          (p19Prog_codeLoaded_of_inv hInvM_w1) hFr_w1 hsat_w1 hwp_d1
      have hInvM_s1 : mlkemInvMem c2MlkemMpl s1.mem := mlkemInvMem_of_keepsFrozen hkf1b hInvM_w1
      have hsp_s1_plain : s1.sp = u.sp - 144#64 := by simpa [stripS_sp] using hsp_s1
      let b03 : MlkemBlk03Args :=
        { ret := x.ret, hdrA := u.sp - 144#64, hdr64 := x.hdr.take 64,
          randA := x.randA, rand := x.rand.toList, esA := x.esA, ssA := x.ssA }
      set Frame03 : SepProp :=
        SavedFrame19 ((u.sp - 144#64) + 128#64) u ∗
        memRegion ((u.sp - 144#64) + 64#64) 64 ∗
        (x.hdrA ↦ₛ x.hdr.take 64) ∗ ((x.hdrA + 64#64) ↦ₛ x.hdr.drop 64) ∗ R_top
      have hpre03 : s1.mem ⊨ mlkemBlk03TermRawSpec.pre b03 s1 ∗ Frame03 := by
        dsimp only [mlkemBlk03TermRawSpec, mlkemBlk03RawSpec, b03]
        have hm1 := Satisfies.mono (sepConj_mono_left hP1) hsat_s1
        rw [hsp_s1_plain, sepConj_assoc, pure_sepConj_of_true hMatTerm64,
          sepConj_assoc, pure_sepConj_of_true
            ⟨by simpa [a19, stripS_readReg64] using hx0_s1,
             by simpa [stripS_readReg64] using hx1_s1,
             by simpa [a19, stripS_readReg64] using hx2_s1,
             by simpa [a19, stripS_readReg64] using hx3_s1,
             by simpa [stripS_readReg64] using hx4_s1,
             by simpa [a19, stripS_readReg64] using hx5_s1,
             by simpa [stripS_readReg64] using hx6_s1,
             hh64_len, x.rand.toList_length⟩]
        exact Satisfies.mono (by dsimp only [a19, RestPro, Frame03]; sep_frame) hm1
      obtain ⟨s2, hEA2, hret03, _, hpost03, hkf2, hFr_s2⟩ :=
        active_call_blk03 hLs hpc_s1 hrun_s1
          (by simpa [stripS_spAligned] using hspA_s1) hInvM_s1 hFr_s1 hpre03
      have hInvM_s2 : mlkemInvMem c2MlkemMpl s2.mem := mlkemInvMem_of_keepsFrozen hkf2 hInvM_s1
      have hpc_s2 : s2.pc = blkPl19.base + 0x0064#64 :=
        hret03.1.trans (by simpa [stripS_readReg64] using hlr_s1)
      have hsp_s2 : s2.sp = u.sp - 144#64 := hret03.2.1.trans hsp_s1_plain
      have hsat_s2 : s2.mem ⊨
          (SavedFrame19 ((u.sp - 144#64) + 128#64) u ∗ mlkemBlk03TermRawSpec.post b03 s1 s2) ∗
            (memRegion ((u.sp - 144#64) + 64#64) 64 ∗
             (x.hdrA ↦ₛ x.hdr.take 64) ∗ ((x.hdrA + 64#64) ↦ₛ x.hdr.drop 64) ∗ R_top) := by
        generalize mlkemBlk03TermRawSpec.post b03 s1 s2 = Post03 at hpost03 ⊢
        exact Satisfies.mono (by dsimp only [Frame03]; sep_frame) hpost03
      obtain ⟨sf, _, hEA3, hpc_sf, hrun_sf, _, _, _, hsp_sf⟩ :=
        run_dropFirstWord_sepWP hLs (j := 19) (by decide) p19Prog p19Prog_eq_blockProgram hlen19
          dropFirst_p19_ne_s5 hlr_drop_out
          (p19Prog_codeLoaded_of_inv hInvM_s2) hFr_s2 hsat_s2
          (p19_epilogue_wp u s2 _ hpc_s2 hret03.2.2 hsp_s2 hsp0)
      exact ⟨sf, hEA1a.trans (hEA1b.trans (hEA2.trans hEA3)),
        ⟨hpc_sf, by simpa [stripS_sp] using hsp_sf, hrun_sf⟩⟩
  obtain ⟨sf, hEA_all, hRet_sf⟩ := hRunAvoid
  let B := mlkemEncaps1SafeBridge stk hstk hfit
  have hSub := mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
    (fun _ _ => rfl) stk hstk hfit (fun _ => none)
  obtain ⟨hGhostEq, hFrGhost⟩ :=
    mlkemBlockGhost_eq_of_emptyAvoid_ret B MlkemEncaps1StateTerminates
      (mlkemEncaps1StateTerminates_stripS_setPC (mlkemKeep c2MlkemMpl) (c2MlkemMpl.base 19))
      (subroutineOk_guarded_from_multi c2MlkemMpl B.hsym hSub fun y _ s hT hpre => by
        dsimp only [mlkemEncaps1AtSpec] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
        obtain ⟨⟨_, hy0, hy1, _, _, _, _, _⟩, hmem⟩ := hpre
        obtain ⟨_, hrd⟩ := (IsBlock.pointsToBytes y.hdrA y.hdr).read hmem
        unfold MlkemEncaps1CallTerminates
        unfold MlkemEncaps1StateTerminates at hT
        rwa [hy0, hy1, hrd] at hT)
      hLsLs hpc19 hTu hInvM0 hFr hnoex hEA_all hRet_sf
  have hEq : mlkemEncaps1GhostAt c2MlkemMpl stk u = sf := hGhostEq
  refine ⟨?_, hFrGhost⟩
  rw [hEq]
  exact hEA_all.toRealAvoid hExt W

/-- **Row `B19` (`lsMlkemEncaps1Sym`, `lsmpl` specialization).** -/
theorem c2_mlkemEncaps1_snttStrictAvoid [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (stk : Nat) (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) (u : State)
    (hTerm : mlkemSampleNttTermOf lsMlkemEncaps1Sym u)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsMlkemEncaps1Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemEncaps1GhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (mlkemEncaps1GhostAt c2MlkemMpl stk u).mem)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt lsmpl z)
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemEncaps1GhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (mlkemEncaps1GhostAt c2MlkemMpl stk u).mem :=
  c2_mlkemEncaps1_snttStrictAvoid_at hLs hLs hExt stk hstk hfit W u
    hTerm hpc hrun hnoex hkf hFr hInv

end C2Encaps1

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidWrap
