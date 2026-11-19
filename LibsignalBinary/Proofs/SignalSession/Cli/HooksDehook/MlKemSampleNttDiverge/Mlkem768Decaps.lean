/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
meta import ProofLib.GenPlacedFetches

/-!
# Per-Row Real-Run Divergence for `B22` → `B04` (`mlkem768::incremental::decapsulate_compressed_key`)

Proves `mlkemDecaps_diverge_of_not_stateTerminates` (and `_step`): when execution enters
`lsMlkem768DecapsSym` (`B22`, `26,960` B tight stack) at `u` with `(keepsFs (mlkemDecapsAtSpec stk K)).pre x u ∗ R`
and `¬ MlkemDecapsStateTerminates u`, every reachable state `v` on both
`cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `Placed.cliProgPlacedSig mpl mmpl W`
has `v.status = .Running` (and a `Step` successor).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Decaps

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open CryptoVerification.LibsignalSpqrV1 (MlKem MlkemDecapsCall)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  mlkemDecapsAtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blk04_code_eq blk04_tree_size blk22_code_eq blk22_tree_size
  blkLib04 blkLib22 blkPC04 blkPC22 blkPl04 blkPl22 blkPlaceable04 blkPlaceable22
  blkTree04 blkTree22 safeSepWP_of_sepWP_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4 (Seg4Spatial seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b (offSeg4End)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  WordRangeMem modTHatPoly16 msgWordFn
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp (
  checkSegRegGprs04 extract_segRegInv04 mkSegBaseState04 mkSegEnv04 mkSegState04
  mkSegState04_matches with_frozen_env04
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init (
  Seg5ConstWordsInv Seg5RegInv Seg5RowDone entry_treeMem04_join
  offSeg5Memset seg5_prologue step_bCond_seg5
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  fetch_blk04_seg5 runKRange04 sepWP_of_runKRange04
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop (
  offRowEntry04 seg5_row_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (fetchWordTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (toByteVec_toList_of_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (sepWP_elim_cell8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem btreeOfWords bytesToWords memRegion_entails_exists_treeMem
  pointsToBytes_eq_treeMem sepLoad64_treeMem treeMem_entails_memRegion zeroTree9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf KSpatial KStateMatches matches_advancePC matches_setPC matches_writeGpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KState evalKExpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  eval_checked_gpr eval_checked_pstate rowSeeds
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  eq_some_getD sepWP_drop_left
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (keccakRc_intro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row (sepWP_mono_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit (
  checkPStateEq setPC_fall_w_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockSafeOk MlKemPlacement mlkemMpl
  mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSepFrom MultiLaneSlots
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE packHalfwordsLE_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768DecapsTerminates Shake128MatrixTerminates indCpaDecrypt
  keccakZeroState sha3_512List shake256List toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2_resolve_mlkem768Decaps_eq lsMlkem768DecapsSym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  MlkemDecapsStateTerminates mlkemDecapsStateTerminates_iff_of_atSpec_pre
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common (
  c2_mlkem_diverge_of_blockSafeOk_false falsePostSpec matrixTerminates3_of_rows_ij
  safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  mlkemDecapsTightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

/-! ## 1. `B04` Segment 5 Row-Copy (`row < 2`) & 3-Row Divergence (`+0x4058 .. +0x7110`) -/

section Blk04Seg5Diverge
attribute [local irreducible] blkPC04

private theorem multiLaneSlots3_eq_treeMem04 (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (hlen : ∀ c, c < 3 → (hws c).length = 272) :
    let bs := packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2))
    MultiLaneSlots (sp + 5680#64) 544 3 hws =
      TreeMem (sp + 5680#64) 204 (btreeOfWords 0 (bytesToWords 204 bs) zeroTree9) := by
  intro bs
  have h0 : (packHalfwordsLE (hws 0)).length = 544 := by rw [packHalfwordsLE_length, hlen 0 (by omega)]
  have h1 : (packHalfwordsLE (hws 1)).length = 544 := by rw [packHalfwordsLE_length, hlen 1 (by omega)]
  have h2 : (packHalfwordsLE (hws 2)).length = 544 := by rw [packHalfwordsLE_length, hlen 2 (by omega)]
  have hbs : bs.length = 8 * 204 := by simp [bs, h0, h1, h2]
  rw [← pointsToBytes_eq_treeMem hbs (by decide)]
  simp only [bs, pointsToBytes_append, h0, h1, MultiLaneSlots, MultiLaneSepFrom,
    sepConj_emp, BitVec.add_assoc]
  rfl

private def cfgCopy04 (row : Nat) : KCfg :=
  { offA := 5680, lenA := 204, offB := 13392 + 1536 * row, lenB := 192 }

private theorem cfgCopy04_wf {row : Nat} (hrow : row < 2) : KCfgWf (cfgCopy04 row) := by
  unfold KCfgWf cfgCopy04
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;> decide

private def stCopy0_04 : KState :=
  { mkSegBaseState04 false with gprs := (mkSegBaseState04 false).gprs.set 9 (.spAdd 13392#64) }

private def stCopyPre04 (row : Nat) : KState :=
  (runKRange04 (cfgCopy04 row) 4151 2 stCopy0_04).getD stCopy0_04

private def stCopyMid04 (row : Nat) : KState :=
  { stCopyPre04 row with gprs := (stCopyPre04 row).gprs.set 9 (.spAdd (BitVec.ofNat 64 (13392 + 1536 * row))) }

private def stCopyEnd04 (row : Nat) : KState :=
  (runKRange04 (cfgCopy04 row) 4154 160 (stCopyMid04 row)).getD (stCopyMid04 row)

private def checkCopyPre04 (st : KState) : Bool :=
  (st.gprs.get 9).beq (.spAdd 13392#64) &&
  (st.gprs.get 10).beq (.const64 1536#64) &&
  (st.gprs.get 19).beq (.var 100)

private def checkCopyEndLt2_04 (st : KState) : Bool :=
  checkSegRegGprs04 st (.var 101) &&
  checkPStateEq st (.var 101) (.const64 3#64)

private theorem cert_copyPre04 {row : Nat} (hrow : row < 2) :
    runKRange04 (cfgCopy04 row) 4151 2 stCopy0_04 = some (stCopyPre04 row) ∧
    checkCopyPre04 (stCopyPre04 row) = true := by
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;>
    exact ⟨eq_some_getD stCopy0_04 (by decide +kernel), by decide +kernel⟩

private theorem cert_copyEndLt2_04 {row : Nat} (hrow : row < 2) :
    runKRange04 (cfgCopy04 row) 4154 160 (stCopyMid04 row) = some (stCopyEnd04 row) ∧
    checkCopyEndLt2_04 (stCopyEnd04 row) = true := by
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;>
    exact ⟨eq_some_getD (stCopyMid04 _) (by decide +kernel), by decide +kernel⟩

attribute [local irreducible] stCopyPre04 stCopyEnd04

private theorem step_gpr_pure04 {prog : Program} {tgt pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    {inst : Instr} {rd : BitVec 5} {e : KExpr} {res : BitVec 64}
    (hrd : rd.toNat < 31) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeReg64 (.gpr rd) res).advancePC)
    (hres : res = evalKExpr env e) (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with gprs := st.gprs.set rd.toNat e } s' →
      SepWP prog tgt s' (KSpatial cfg env { st with gprs := st.gprs.set rd.toNat e } F) post) :
    SepWP prog tgt s (KSpatial cfg env st F) post :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeGpr (matches_setPC hm pc) hrd e hres)))

private theorem eval_madd_x9_x19_x10 {prog : Program} {pc v9 v10 v19 : BitVec 64} {s : State}
    (hx9 : s.readReg64 .x9 = v9) (hx10 : s.readReg64 .x10 = v10) (hx19 : s.readReg64 .x19 = v19) :
    prog.evalInst (.dataProc3 .W64 .MADD .x9 .x19 .x10 .x9) (s.setPC pc) =
      ((s.setPC pc).writeReg64 (.gpr 9#5) (v9 + v19 * v10)).advancePC := by
  simp [Program.evalInst, execInstWithSvc, execDataProc3,
    State.readReg64, RegFile.read] at hx9 hx10 hx19 ⊢
  simp [State.setPC, hx9, hx10, hx19]

private theorem step_ldr_4150 [MlKemPlacement] {b tgt sp : BitVec 64}
    {tA : BTree (BitVec 64) 9} {Rest : SepProp} {post : State → SepProp → Prop} {s : State}
    (htA6 : tA.get 6 = sp + 13392#64)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4150)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hnext : ∀ s1 : State, s1 = (s.writeReg64 (.gpr 9#5) (sp + 13392#64)).setPC (b + BitVec.ofNat 64 (4 * 4151)) →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt s1 (TreeMem (sp + 144#64) 264 tA ∗ Rest) post) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s (TreeMem (sp + 144#64) 264 tA ∗ Rest) post := by
  have hfw : fetchWordTree04 4150 = some (.ldr .W64 .X64 false .x9 (.Offset .sp 192#64)) := by decide +kernel
  have hfetch := fetch_blk04_seg5 (b := b) (Or.inl ⟨by omega, by omega⟩) hfw
  have hsp_chk : checkAddrSPAligned s (.Offset .sp 192#64) = true := by
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al]
  have haddr : evalAddrMode s (.Offset .sp 192#64) = (sp + 192#64, none) := by
    simp [evalAddrMode, State.readReg64, hsp]
  have hl0 : SepLoad64 (sp + 192#64) (TreeMem (sp + 144#64) 264 tA ∗ Rest) (sp + 13392#64) := by
    rw [← htA6]
    exact sepLoad64_treeMem (idx := 6) (by decide) (by decide) rfl (by bv_omega)
  have hpc4151 : b + BitVec.ofNat 64 (4 * 4150) + 4#64 = b + BitVec.ofNat 64 (4 * 4151) := by
    bv_omega
  exact SepWP.step_ldr64 hpc hrun hfetch hsp_chk haddr hl0 rfl (by
    rw [hpc4151]; exact hnext _ rfl)

private theorem step_madd_4153 [MlKemPlacement] {b tgt sp : BitVec 64} {row : Nat} (hrow : row < 2)
    {env : KEnv} {F : SepProp} {post : State → SepProp → Prop} {s : State}
    (hsp : env.sp = sp) (hv100 : env.vars 100 = BitVec.ofNat 64 row)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4153)) (hrun : s.status = .Running)
    (hm : KStateMatches env (stCopyPre04 row) s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * 4154) → s'.status = .Running →
      KStateMatches env (stCopyMid04 row) s' →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt s'
        (KSpatial (cfgCopy04 row) env (stCopyMid04 row) F) post) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s
      (KSpatial (cfgCopy04 row) env (stCopyPre04 row) F) post := by
  have hc := (cert_copyPre04 hrow).2
  simp only [checkCopyPre04, Bool.and_eq_true] at hc
  have hx9 : s.readReg64 .x9 = sp + 13392#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 9#5 (by decide) (.spAdd 13392#64) hc.1.1 rfl
    simpa [evalKExpr, hsp] using h
  have hx10 : s.readReg64 .x10 = 1536#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 10#5 (by decide) (.const64 1536#64) hc.1.2 rfl
    simpa [evalKExpr] using h
  have hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 19#5 (by decide) (.var 100) hc.2 rfl
    simpa [evalKExpr, hv100] using h
  have hfw : fetchWordTree04 4153 = some (.dataProc3 .W64 .MADD .x9 .x19 .x10 .x9) := by decide +kernel
  have hres : (sp + 13392#64) + BitVec.ofNat 64 row * 1536#64 =
      evalKExpr env (.spAdd (BitVec.ofNat 64 (13392 + 1536 * row))) := by
    change (sp + 13392#64) + BitVec.ofNat 64 row * 1536#64 =
      env.sp + BitVec.ofNat 64 (13392 + 1536 * row)
    rw [hsp]
    rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;> (clear *- ; bv_omega)
  have hpc4154 : (b + BitVec.ofNat 64 (4 * 4153)) + 4#64 = b + BitVec.ofNat 64 (4 * 4154) := by
    bv_omega
  exact step_gpr_pure04 (by decide) hpc hrun (fetch_blk04_seg5 (Or.inl ⟨by omega, by omega⟩) hfw)
    (eval_madd_x9_x19_x10 hx9 hx10 hx19) hres hm
    (fun s' hs' hrun' hm' => hnext s' (hs'.trans hpc4154) hrun' hm')

attribute [local irreducible] stCopyMid04

private theorem mkSegEnv04_var101 [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat)
    (rho : List (BitVec 8)) (s : State) (tA tB : BTree (BitVec 64) 9) :
    (mkSegEnv04 sp fpVal row rho keccakZeroState keccakZeroState keccakZeroState
      (fun _ => 0#64) s tA tB).vars 101 = s.readReg64 .x8 := by
  simp only [mkSegEnv04, Bool.false_eq_true, ↓reduceIte,
    show ¬((101 : Nat) < 25) by decide, show ¬((101 : Nat) < 50) by decide,
    show ¬((101 : Nat) < 75) by decide, show ¬((101 : Nat) < 100) by decide,
    beq_false_of_ne (show (101 : Nat) ≠ 100 by decide), beq_self_eq_true]

private theorem seg5_row_copy_lt2_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} (hrow : row < 2) {F : SepProp}
    {s : State} {P : SepProp}
    (hexit : Seg5RowDone b sp fpVal rho row
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 1536 ∗ F) s P) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offRowEntry04) s P
      (fun sf Pf =>
        sf.pc = b + offRowEntry04 ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg5RegInv sp fpVal sf ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
        (∃ extra : Nat, allLanesDone 3 (rowSeeds rho row) extra = true) ∧
        ∃ tA : BTree (BitVec 64) 9,
          Seg5ConstWordsInv sp rho tA ∧
          (Pf ⊢ TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
            memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
            memRegion (sp + 19168#64) 24 ∗
            memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 1536 ∗ F)) := by
  rcases hexit with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx19,
    extra, tA, sampled, hws, hdone, hinv, htA, hP⟩
  let tSlots := btreeOfWords 0 (bytesToWords 204
    (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9
  have hSlots : MultiLaneSlots (sp + 5680#64) 544 3 hws = TreeMem (sp + 5680#64) 204 tSlots :=
    multiLaneSlots3_eq_treeMem04 sp fun c hc => (hinv c hc).1.1
  let Rest0 := TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
    TreeMem (sp + 5680#64) 204 tSlots ∗ memRegion (sp + 20704#64) 504 ∗
    memRegion (sp + 19168#64) 24 ∗ F
  refine sepWP_mono_pre (Entails.trans (by rw [hSlots] at hP; exact hP)
    (Entails.trans (by dsimp only [Rest0]; rw [show (1536 : Nat) = 8 * 192 from rfl]; sep_frame :
      _ ⊢ memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) (8 * 192) ∗ Rest0)
      (sepConj_mono_left (memRegion_entails_exists_treeMem (len := 192) (by decide))))) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tB0
  refine with_frozen_env04 hcl hro ?_
  refine SepWP.congr_pre (P1 := TreeMem (sp + 144#64) 264 tA ∗
      (TreeMem (sp + 5680#64) 204 tSlots ∗ TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192 tB0 ∗
        memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F))
    (by dsimp only [Rest0]; apply sepProp_ext <;> sep_frame) ?_
  refine step_ldr_4150 htA.2.2.2.2.2.1 hpc hrun hreg.1 hreg.2.1 fun sL hsL => ?_
  refine keccakRc_intro (by rw [hsL]; simpa [State.setPC, State.writeReg64] using hro) ?_
  let env := mkSegEnv04 sp fpVal row rho keccakZeroState keccakZeroState keccakZeroState
    (fun _ => 0#64) s tSlots tB0
  rcases mkSegState04_matches (cfg := cfgCopy04 row) (hasConsts := false) (slots01 := []) (slots2 := [])
    (rho := rho) (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState)
    (k2Hi := fun _ => 0#64) (tA := tSlots) (tB := tB0) (by decide) (by decide) hreg hx19
    (fun h => Bool.noConfusion h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    with ⟨hmBase, htA_eq, htB_eq⟩
  have hm0 : KStateMatches env stCopy0_04 sL := by
    rw [hsL]; unfold stCopy0_04
    exact matches_setPC (matches_writeGpr (rd := 9#5) hmBase (by decide) (.spAdd 13392#64)
      (by simp [evalKExpr, mkSegEnv04])) _
  let FF := TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
    memRegion (sp + 20704#64) 504 ∗ memRegion (sp + 19168#64) 24 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial (cfgCopy04 row) env stCopy0_04 FF)
    (by
      have hmA : (mkSegBaseState04 false).memA =
          (mkSegState04 (cfgCopy04 row) false [] []).memA := rfl
      have hmB : (mkSegBaseState04 false).memB =
          (mkSegState04 (cfgCopy04 row) false [] []).memB := rfl
      dsimp only [KSpatial, cfgCopy04, stCopy0_04, env, FF] at htA_eq htB_eq hmA hmB ⊢
      rw [hmA, hmB, htA_eq, htB_eq]
      change (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ↦ᵣ
          mlkemData01Bytes) ∗
        TreeMem (sp + 5680#64) 204 tSlots ∗
        TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192 tB0 ∗
        TreeMem (sp + 144#64) 264 tA ∗
        memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F = _
      apply sepProp_ext <;> sep_frame) ?_
  refine sepWP_of_runKRange04 (cfgCopy04_wf hrow) (show (0 : Nat) < 24 by decide)
    (fun k hk => Or.inl ⟨by omega, by omega⟩) (cert_copyPre04 hrow).1
    (by rw [hsL]; rfl) (by rw [hsL]; simpa [State.setPC, State.writeReg64] using hrun) hm0
    fun s1 hpc1 hrun1 hm1 => ?_
  refine step_madd_4153 hrow (sp := sp) rfl rfl hpc1 hrun1 hm1 fun s2 hpc2 hrun2 hm2 => ?_
  refine sepWP_of_runKRange04 (cfgCopy04_wf hrow) (show (0 : Nat) < 24 by decide)
    (fun k hk => Or.inl ⟨by omega, by omega⟩) (cert_copyEndLt2_04 hrow).1
    hpc2 hrun2 hm2 fun s3 hpc3 hrun3 hm3 => ?_
  have hcE := (cert_copyEndLt2_04 hrow).2
  simp only [checkCopyEndLt2_04, Bool.and_eq_true] at hcE
  have hpst : s3.pstate = (AddWithCarry64 (BitVec.ofNat 64 (row + 1)) (~~~3#64) true).2 := by
    have hp := eval_checked_pstate (ok := fun _ => true) hm3 (fun _ _ => rfl)
      (.var 101) (.const64 3#64) hcE.2 rfl rfl
    dsimp only [evalKExpr, env] at hp
    rw [mkSegEnv04_var101, hx8] at hp
    exact hp
  have hspOut : TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy04 row).offA) (cfgCopy04 row).lenA
        ((stCopyEnd04 row).memA.map (evalKExpr env)) ∗
      TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy04 row).offB) (cfgCopy04 row).lenB
        ((stCopyEnd04 row).memB.map (evalKExpr env)) ∗ FF ⊢
      TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗
        memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 1536 ∗ F := by
    dsimp only [cfgCopy04, FF]
    rw [show env.sp = sp from rfl, show sp + BitVec.ofNat 64 5680 = sp + 5680#64 from rfl]
    have htmA := treeMem_entails_memRegion (ptr := sp + 5680#64)
      ((stCopyEnd04 row).memA.map (evalKExpr env)) (len := 204) (by decide)
    have htmB := treeMem_entails_memRegion (ptr := sp + BitVec.ofNat 64 (13392 + 1536 * row))
      ((stCopyEnd04 row).memB.map (evalKExpr env)) (len := 192) (by decide)
    rw [show 8 * 204 = 1632 from rfl] at htmA
    rw [show 8 * 192 = 1536 from rfl] at htmB
    exact Entails.trans (sepConj_mono htmA (sepConj_mono_left htmB)) (by sep_frame)
  refine step_bCond_seg5 (w := 4314) (cond := .EQ) (disp := BitVec.ofNat 64 11688)
    (Or.inl ⟨by omega, by omega⟩) (by decide +kernel) hpc3 hrun3 (fun hT => ?_) (fun hF => ?_)
  · rw [hpst] at hT
    rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl
    · exact absurd hT (by decide +kernel)
    · exact absurd hT (by decide +kernel)
  · have hpcF : (s3.setPC (b + BitVec.ofNat 64 (4 * (4314 + 1)))).pc = b + offRowEntry04 :=
      setPC_fall_w_eq s3 b 4314 4315 (by decide +kernel)
    rcases extract_segRegInv04 (row := row) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl rfl hcE.1 with ⟨hregF, hx8F, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcF (by simpa [State.setPC] using hrun3) fun hclF hroF =>
      ⟨hpcF, by simpa [State.setPC] using hrun3, hclF, hroF, hregF,
        by simpa [evalKExpr, env, mkSegEnv04, hx8] using hx8F, ⟨extra, hdone⟩, tA, htA, hspOut⟩

private theorem sepWP_elim_treeMem_04 {prog : Program} {tgt : BitVec 64} {s : State}
    {ptr : BitVec 64} {len : Nat} (hlen : len ≤ 512) {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog tgt s (TreeMem ptr len t ∗ R) post) :
    SepWP prog tgt s (memRegion ptr (8 * len) ∗ R) post := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_entails_exists_treeMem hlen)) ?_
  rw [sepExists_sepConj_left]; exact SepWP.exists_left h

private theorem memRegion_entry_144_208_split (sp : BitVec 64) :
    memRegion (sp + 144#64) 48 ∗ memRegion (sp + 208#64) 2048 =
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32) ∗
      (memRegion (sp + 176#64) 8 ∗ memRegion (sp + 208#64) (8 * 30) ∗
        memRegion (sp + 528#64) (8 * 216)) := by
  rw [memRegion_split' (b := sp + 144#64) (b' := sp + 176#64) (n := 32) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 176#64) (b' := sp + 184#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 208#64) (b' := sp + 448#64) (n := 240) (k := (1808 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 448#64) (b' := sp + 464#64) (n := 16) (k := (1792 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 464#64) (b' := sp + 496#64) (n := 32) (k := (1760 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 496#64) (b' := sp + 528#64) (n := 32) (k := (1728 : Nat)) rfl (by bv_omega) (by decide),
    show (240 : Nat) = 8 * 30 from rfl, show (1728 : Nat) = 8 * 216 from rfl]
  apply sepProp_ext <;> sep_frame

private theorem memRegion_5680_split (sp : BitVec 64) :
    memRegion (sp + 5680#64) 6176 =
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 :=
  memRegion_split' (b := sp + 5680#64) (b' := sp + 7312#64) (n := 1632) (k := (4544 : Nat))
    rfl (by bv_omega) (by decide)

private theorem memRegion_entry_13392_split (sp : BitVec 64) :
    memRegion (sp + 13392#64) 12224 =
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 0)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗ memRegion (sp + 18000#64) 32 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) := by
  rw [memRegion_split' (b := sp + 13392#64) (b' := sp + 14928#64) (n := 1536) (k := (10688 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 14928#64) (b' := sp + 16464#64) (n := 1536) (k := (9152 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16464#64) (b' := sp + 18000#64) (n := 1536) (k := (7616 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18000#64) (b' := sp + 18032#64) (n := 32) (k := (7584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18032#64) (b' := sp + 19168#64) (n := 1136) (k := (6448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19168#64) (b' := sp + 19192#64) (n := 24) (k := (6424 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19192#64) (b' := sp + 20704#64) (n := 1512) (k := (4912 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 20704#64) (b' := sp + 21208#64) (n := 504) (k := (4408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 21208#64) (b' := sp + 22400#64) (n := 1192) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 23912#64) (n := 1512) (k := (1704 : Nat)) rfl (by bv_omega) (by decide),
    show sp + BitVec.ofNat 64 (13392 + 1536 * 0) = sp + 13392#64 from rfl,
    show sp + BitVec.ofNat 64 (13392 + 1536 * 1) = sp + 14928#64 from rfl,
    show sp + BitVec.ofNat 64 (13392 + 1536 * 2) = sp + 16464#64 from rfl]
  apply sepProp_ext <;> sep_frame

private theorem seg5_diverge_safe_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hdk : dk.length = 2400)
    (hNotMat : ¬ Shake128MatrixTerminates ((dk.drop 2304).take 32) 3)
    (hpc : s.pc = b + offSeg4End) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = dkA) (hx10 : s.readReg64 .x10 = 11#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 25824#64) + 16384#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 25824#64) + 20704#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 25824#64) + 5680#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 25824#64) + 20968#64) :
    SafeSepWP (blkPC04.rebase b (fun _ => none)) s
      (Seg4Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)
      (fun _ _ => False) := by
  set sp := s0.sp - 25824#64
  set fpVal := s0.sp - 96#64
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32
  set z := (dk.drop 2368).take 32
  set pk0 := (dk.drop 1152).take 384
  set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  have hrho : rho.length = 32 := by simp [rho, hdk]
  set R_keep := stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
    memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
    ((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 2256#64) ↦ₛ ct) ∗
    ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
    ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
    memRegion (sp + 4560#64) 1120 ∗ ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
    memRegion (sp + 25648#64) 16 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  refine SafeSepWP.of_sepWP (mid := b + offSeg5Memset) ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 176#64) 8 ∗
    (memRegion (sp + 208#64) (8 * 30) ∗ (memRegion (sp + 528#64) (8 * 216) ∗
      ((memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
          memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
          memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
        ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
        memRegion (sp + 13392#64) 12224 ∗ R_keep))))
    (by
      refine Entails.trans (show _ ⊢
        (memRegion (sp + 144#64) 48 ∗ memRegion (sp + 208#64) 2048) ∗
          memRegion (sp + 5680#64) 6176 ∗
          (((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
            PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
            PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
            PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
            memRegion (sp + 13392#64) 12224 ∗ (dkA ↦ₛ dk) ∗ R_keep) by
        unfold Seg4Spatial; dsimp only [sp, ct, m', hPk, z, pk0, pk1, pk2]; sep_frame) ?_
      rw [memRegion_entry_144_208_split sp, memRegion_5680_split sp]; sep_frame) ?_
  refine sepWP_elim_cell8 fun w4 => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 208#64) (8 * 30) ∗
    (memRegion (sp + 528#64) (8 * 216) ∗ (((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep))) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 30) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 528#64) (8 * 216) ∗
    (TreeMem (sp + 208#64) 30 tMid ∗ ((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep)) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 216) (by decide) fun tHi => ?_
  rcases entry_treeMem04_join sp w4 rho tMid tHi with ⟨tA0, htA0, hjoin0⟩
  let Tail0 := TreeMem (sp + 528#64) 216 tHi ∗ TreeMem (sp + 208#64) 30 tMid ∗
    ((sp + 176#64) ↦₆₄ w4) ∗ ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗
    ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
    memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 13392#64) 12224 ∗ R_keep
  refine with_frozen_env04 hcl hro ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
    memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
    memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ Tail0)
    (by dsimp only [Tail0]; sep_frame) ?_
  refine SepWP.mono
    (seg5_prologue hb hbase s sp fpVal dkA dk Tail0 hdk hpc hrun hsp hspA
      hfp hx9 hx10 hx23 hx26 hx27 hx28 hro) ?_
  rintro sP PP hpcP hrunP ⟨hregP, hx8P, hPP⟩ hclP hroP
  let Fixed := memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 18000#64) 32 ∗
    (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
      memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗
    (dkA ↦ₛ dk) ∗ R_keep
  have hpre0 : PP ⊢ TreeMem (sp + 144#64) 264 tA0 ∗ memRegion (sp + 22400#64) 1512 ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 0)) 1536 ∗
        (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
          memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗ Fixed)) := by
    refine Entails.trans hPP ?_
    dsimp only [Tail0, Fixed, rho] at hjoin0 ⊢
    rw [memRegion_entry_13392_split sp, ← hjoin0]; sep_frame
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 0) (by omega) htA0 hpcP hrunP hclP hroP hregP hx8P)
    fun sm0 Pm0 hex0 => SafeSepWP.of_sepWP <| SepWP.mono (seg5_row_copy_lt2_wp (row := 0) (by omega) hex0) ?_) hpre0
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, ⟨e0, hd0⟩, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 1) (by omega) htA1 hpc1 hrun1 hcl1 hro1 hreg1 hx8_1)
    fun sm1 Pm1 hex1 => SafeSepWP.of_sepWP <| SepWP.mono (seg5_row_copy_lt2_wp (row := 1) (by omega) hex1) ?_)
    (Entails.trans hP1 (by sep_frame))
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, ⟨e1, hd1⟩, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 2) (by omega) htA2 hpc2 hrun2 hcl2 hro2 hreg2 hx8_2)
    fun _ _ hex2 => ?_)
    (Entails.trans hP2 (by sep_frame))
  obtain ⟨e2, _, _, _, hd2, _⟩ := hex2.2.2.2.2.2.2.2
  exact False.elim (hNotMat (matrixTerminates3_of_rows_ij hd0 hd1 hd2))

end Blk04Seg5Diverge

/-! ## 2. `B04` & `B22` Block-Level Divergence Contracts (`MlKemBlockSafeOk`) -/

private def mlkemBlk04DivPre :
    (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) → State → SepProp :=
  fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧ s0.readReg64 .x1 = dkA ∧
      s0.readReg64 .x2 = ct1A ∧ s0.readReg64 .x3 = ct2A ∧
      dk.length = 2400 ∧ ct1.length = 960 ∧ ct2.length = 128 ∧
      ¬ Shake128MatrixTerminates ((dk.drop 2304).take 32) 3⌝ ∗
      (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960

private theorem blk04_decaps_diverge_safe_ok :
    MlKemBlockSafeOk 4 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemBlk04DivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC04 blkPl04 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
    fun ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, mlkemBlk04DivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx0, hx1, hx2, hx3, hdk, hct1, hct2, hNotMat⟩ => ?_
  refine SafeSepWP.weaken_pre
    (safeSepWP_of_sepWP_env hcl0 hro0
      (seg4_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
        hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_)
    (by sep_frame)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hfp4, hx9_4, hx10_4, hx23_4, hx26_4, hx27_4, hx28_4, hP4⟩
  exact SafeSepWP.weaken_pre
    (seg5_diverge_safe_ok hb hbase s0 s4 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
      hdk hNotMat hpc4 hrun4 hcl4 hro4 hsp4 hspA4 hfp4 hx9_4 hx10_4 hx23_4 hx26_4 hx27_4 hx28_4)
    hP4

section Blk22Fetches
gen_placed_fetches blkPC22 blkLib22 blkTree22 blk22_code_eq blk22_tree_size
  via_placement blkPl22 blkPlaceable22 [0x0 → 0x10]
end Blk22Fetches

private theorem blk22_prologue_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl22 b) (hbase : blkPl22.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64) (P : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = ret) (hx0 : s0.readReg64 .x0 = dkA)
    (hx1 : s0.readReg64 .x1 = ct1A) (hx2 : s0.readReg64 .x2 = ct2A) :
    SepWP (blkPC22.rebase b (fun _ => none)) (mlkemMpl.base 4) s0 P
      (sepPost (fun s1 =>
        s1.mem = s0.mem ∧ s1.sp = s0.sp ∧ s1.spAligned = s0.spAligned ∧
        s1.readReg64 .lr = s0.readReg64 .lr ∧
        s1.readReg64 .x0 = ret ∧ s1.readReg64 .x1 = dkA ∧
        s1.readReg64 .x2 = ct1A ∧ s1.readReg64 .x3 = ct2A) P) := by
  have _ := hb
  subst hbase
  simp only [Reg.x8, Reg.x0, Reg.x1, Reg.x2] at hx8 hx0 hx1 hx2
  wp_steps 5
  refine SepWP.done
    (by simp [wp_norm, arm64_norm, blkPl22, MultiPlacedLib.blockPlacement])
    (by simp [hrun]) ?_
  rw [sepPost_apply]
  exact ⟨⟨rfl, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm]⟩, Entails.refl P⟩

private def mlkemDecapsDivPre :
    (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) → State → SepProp :=
  fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = dkA ∧
      s0.readReg64 .x1 = ct1A ∧ s0.readReg64 .x2 = ct2A ∧
      dk.length = 2400 ∧ ct1.length = 960 ∧ ct2.length = 128 ∧
      ¬ Shake128MatrixTerminates ((dk.drop 2304).take 32) 3⌝ ∗
      (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960

private theorem blk22_decaps_diverge_safe_ok :
    MlKemBlockSafeOk 22 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemDecapsDivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC22 blkPl22 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
    fun ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, mlkemDecapsDivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx8, hx0, hx1, hx2, hdk, hct1, hct2, hNotMat⟩ => ?_
  let P0 : SepProp :=
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960
  refine SafeSepWP.of_sepWP (SepWP.mono
    (blk22_prologue_wp hb hbase s0 ret dkA ct1A ct2A P0 hpc hrun hx8 hx0 hx1 hx2) ?_)
  intro s1 P1 hpc1 hrun1 hp1; rw [sepPost_apply] at hp1
  rcases hp1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1⟩, hP1⟩
  refine SafeSepWP.call_subroutine_frame
    (mlkemSafeCall_of_blockSafeOk _ blk04_decaps_diverge_safe_ok)
    (x := (ret, dkA, dk, ct1A, ct1, ct2A, ct2)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm1 => by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
        withMlKemRoOk, falsePostSpec, mlkemBlk04DivPre]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
          satisfies_pure_sepConj]
      refine ⟨hmem1 ▸ hcl0, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hmem1 ▸ hro0, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hdk, hct1, hct2, hNotMat⟩, ?_⟩
      rw [hsp1, emp_sepConj]; exact hm1')
    (fun _ _ _ _ _ _ hm_false => False.elim (not_satisfies_false_sepConj (by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
        withMlKemRoOk, falsePostSpec] at hm_false
      rw [sepConj_assoc] at hm_false
      exact hm_false)))

/-! ## 3. Layer 1 Real-ELF Divergence Theorems for `lsMlkem768DecapsSym` -/

/-- Step-witnessed operational divergence for `lsMlkem768DecapsSym` (`B22`,
    `mlkem768::incremental::decapsulate_compressed_key`) when `¬ MlkemDecapsStateTerminates u`. -/
theorem mlkemDecaps_diverge_of_not_stateTerminates_step
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemDecapsStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  have hpre_at : u.mem ⊨ (mlkemDecapsAtSpec stk K).pre x u ∗ R := by
    simpa only [keepsFs] using hpre
  have hNotMat : ¬ Shake128MatrixTerminates ((x.dk.toList.drop 2304).take 32) 3 := by
    intro hMat
    have hCall : Mlkem768DecapsTerminates x.dk := by
      have hvec : toByteVec 2400 x.dk.toList = x.dk := by
        apply Subtype.ext
        exact toByteVec_toList_of_length x.dk.toList_length
      rw [← hvec]
      unfold Mlkem768DecapsTerminates
      rwa [toByteVec_toList_of_length x.dk.toList_length]
    exact hNotTerm ((mlkemDecapsStateTerminates_iff_of_atSpec_pre hpre_at).mpr hCall)
  dsimp only [mlkemDecapsAtSpec] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx8, hx0, hx1, hx2⟩, hspat⟩ := hpre_at
  have hstk26960 : 26960 ≤ stk := hstk
  rw [stackAt_shrink u.sp stk 26960 hstk26960 hfit] at hspat
  set slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 26960)
  have hpre_div : u.mem ⊨
      mlkemDecapsDivPre
        (x.ret, x.dkA, x.dk.toList, x.ct1A, x.ct1.toList, x.ct2A, x.ct2.toList) u ∗
        (slack ∗ R) := by
    dsimp only [mlkemDecapsDivPre]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, x.dk.toList_length, x.ct1.toList_length,
      x.ct2.toList_length, hNotMat⟩, Satisfies.mono (by sep_frame) hspat⟩
  exact c2_mlkem_diverge_of_blockSafeOk_false (by decide) blk22_decaps_diverge_safe_ok
    (by intro ⟨_, _, _, _, _, _, _⟩ s _; cases s; rfl)
    hLs hExt (c2_resolve_mlkem768Decaps_eq hLs) W hpc hrun hsp hInv hFr hpre_div

/-- Layer 1 operational divergence for `lsMlkem768DecapsSym` (`B22`,
    `mlkem768::incremental::decapsulate_compressed_key`): every state `v` reachable from a stuck
    entry `u` has `v.status = .Running`. -/
theorem mlkemDecaps_diverge_of_not_stateTerminates
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemDecapsStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) := by
  have ⟨h1, h2⟩ := mlkemDecaps_diverge_of_not_stateTerminates_step hstk hfit hLs hExt W
    hpc hrun hsp hInv hFr hpre hNotTerm
  exact ⟨fun v hv => (h1 v hv).1, fun v hv => (h2 v hv).1⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Decaps
