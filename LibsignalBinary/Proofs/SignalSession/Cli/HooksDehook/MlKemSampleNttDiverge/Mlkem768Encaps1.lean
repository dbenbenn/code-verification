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
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row

/-!
# Operational Divergence of Stuck `mlkem768::incremental::encapsulate1` (`B19` → `B03`)

Proves that when `¬ MlkemEncaps1StateTerminates u` holds at the entry of `lsMlkem768Encaps1Sym`
(`B19`, calling `B03` `encapsulate1_serialized` with `64 ≤ hdr.length` and
`¬ Shake128MatrixTerminates (hdr.take 32) 3`), every state `v` reachable in the real 0-hook program
(`cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `Placed.cliProgPlacedSig mpl mmpl W`)
has `v.status = .Running` (and a next step `∃ w, Step P_real v w`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Encaps1

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open CryptoVerification.LibsignalSpqrV1 (MlKem MlkemEncaps1Call)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  mlkemEncaps1AtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args MlkemEncaps1Args SavedFrame19 UnspilledSaved19 blk19_code_eq blk19_tree_size
  blkLib19 blkPC03 blkPC19 blkPl03 blkPl19 blkPlaceable19 blkTree19 safeSepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1 (seg1_wp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv Seg2SeedConsts
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp (
  checkSegRegGprs eq_some_getD extract_segRegInv mkSegBaseState mkSegEnv mkSegState
  mkSegState_matches sepWP_drop_left with_frozen_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  Seg2RowExit entry_memA_join keccakRc_intro rowSeeds step_bCond_seg2a
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeOfWords bytesToWords fetch_blk03_seg2a pointsToBytes_eq_treeMem seedConstsWords
  sepWP_elim_treeMem treeMem_entails_memRegion zeroTree9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (kpflagOptBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row (seg2_row_safeSepWP)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit (
  pc_of_eq setPC_fall_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner (
  eval_checked_gpr eval_checked_pstate
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2a
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KConstsLoOpt KStateMatches KSpatial evalMemTree matches_advancePC matches_setPC
  matches_writeGpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KState evalKExpr fetchWordTree03 runKRange
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepWP.of_memRegion_vecRangeMem vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockSafeOk MlKemPlacement mbase mlkemMpl mlkemSafeCall_of_blockSafeOk
  mlkemSafeCaller_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
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
  Mlkem768Encaps1Terminates Shake128MatrixTerminates keccakZeroState
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2_resolve_mlkem768Encaps1_eq lsMlkem768Encaps1Sym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  MlkemEncaps1StateTerminates mlkemEncaps1StateTerminates_iff_of_atSpec_pre
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common (
  c2_mlkem_diverge_of_blockSafeOk_false falsePostSpec matrixTerminates3_of_rows_ij
  safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  mlkemEncaps1TightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

/-! ## 1. `B03` (`encapsulate1_serialized`) Divergence under `¬ Shake128MatrixTerminates` -/

section Blk03Seg2Diverge
attribute [local irreducible] blkPC03

private theorem multiLaneSlots3_eq_treeMem (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (hlen : ∀ c, c < 3 → (hws c).length = 272) :
    let bs := packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2))
    MultiLaneSlots (sp + 4272#64) 544 3 hws =
      TreeMem (sp + 4272#64) 204 (btreeOfWords 0 (bytesToWords 204 bs) zeroTree9) := by
  intro bs
  have h0 : (packHalfwordsLE (hws 0)).length = 544 := by rw [packHalfwordsLE_length, hlen 0 (by omega)]
  have h1 : (packHalfwordsLE (hws 1)).length = 544 := by rw [packHalfwordsLE_length, hlen 1 (by omega)]
  have h2 : (packHalfwordsLE (hws 2)).length = 544 := by rw [packHalfwordsLE_length, hlen 2 (by omega)]
  have hbs : bs.length = 8 * 204 := by simp [bs, h0, h1, h2]
  rw [← pointsToBytes_eq_treeMem hbs (by decide)]
  simp only [bs, pointsToBytes_append, h0, h1, MultiLaneSlots, MultiLaneSepFrom,
    sepConj_emp, BitVec.add_assoc]
  rfl

private def cfgCopy (row : Nat) : KCfg :=
  { offA := 4272, lenA := 204, offB := 6832 + 1536 * row, lenB := 192, hasConstsLo := false }

private theorem cfgCopy_wf {row : Nat} (hrow : row < 2) : KCfgWf (cfgCopy row) := by
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;> decide +kernel

private def stCopyPre (row : Nat) : KState :=
  (runKRange (cfgCopy row) 155 6 (mkSegBaseState false)).getD (mkSegBaseState false)

private def stCopyMid (row : Nat) : KState :=
  { stCopyPre row with gprs := (stCopyPre row).gprs.set 9 (.spAdd (BitVec.ofNat 64 (6832 + 1536 * row))) }

private def stCopyEnd (row : Nat) : KState :=
  (runKRange (cfgCopy row) 162 158 (stCopyMid row)).getD (stCopyMid row)

private def checkCopyPre (st : KState) : Bool :=
  (st.gprs.get 9).beq (.spAdd 6832#64) &&
  (st.gprs.get 10).beq (.const64 1536#64) &&
  (st.gprs.get 22).beq (.var 96)

private def checkCopyEndLt2 (st : KState) : Bool :=
  checkSegRegGprs st (.var 101) &&
  kpflagOptBeq st.pstateFlag (some (.subs64 (.var 101) 3#64))

private theorem cert_copyPre {row : Nat} (hrow : row < 2) :
    runKRange (cfgCopy row) 155 6 (mkSegBaseState false) = some (stCopyPre row) ∧
    checkCopyPre (stCopyPre row) = true := by
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;>
    exact ⟨eq_some_getD (mkSegBaseState false) (by decide +kernel), by decide +kernel⟩

private theorem cert_copyEndLt2 {row : Nat} (hrow : row < 2) :
    runKRange (cfgCopy row) 162 158 (stCopyMid row) = some (stCopyEnd row) ∧
    checkCopyEndLt2 (stCopyEnd row) = true := by
  rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;>
    exact ⟨eq_some_getD (stCopyMid _) (by decide +kernel), by decide +kernel⟩

attribute [local irreducible] stCopyPre stCopyEnd

private theorem step_gpr_pure03 {prog : Program} {tgt pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    {inst : Instr} {rd : BitVec 5} {e : KExpr} {res : BitVec 64}
    (hrd : rd ≠ 31#5) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeReg64 (.gpr rd) res).advancePC)
    (hres : res = evalKExpr env e) (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with gprs := st.gprs.set rd.toNat e } s' →
      SepWP prog tgt s' (KSpatial cfg env { st with gprs := st.gprs.set rd.toNat e } F) post) :
    SepWP prog tgt s (KSpatial cfg env st F) post :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeGpr (matches_setPC hm pc) hrd e hres)))

private theorem eval_madd_x9_x22_x10 {prog : Program} {pc v9 v10 v22 : BitVec 64} {s : State}
    (hx9 : s.readReg64 .x9 = v9) (hx10 : s.readReg64 .x10 = v10) (hx22 : s.readReg64 .x22 = v22) :
    prog.evalInst (.dataProc3 .W64 .MADD .x9 .x22 .x10 .x9) (s.setPC pc) =
      ((s.setPC pc).writeReg64 (.gpr 9#5) (v9 + v22 * v10)).advancePC := by
  simp [Program.evalInst, execInstWithSvc, execDataProc3,
    State.readReg64, RegFile.read] at hx9 hx10 hx22 ⊢
  simp [State.setPC, hx9, hx10, hx22]

private theorem step_madd_161 [MlKemPlacement] {b tgt sp : BitVec 64} {row : Nat} (hrow : row < 2)
    {env : KEnv} {F : SepProp} {post : State → SepProp → Prop} {s : State}
    (hsp : env.sp = sp) (hv96 : env.vars 96 = BitVec.ofNat 64 row)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 161)) (hrun : s.status = .Running)
    (hm : KStateMatches env (stCopyPre row) s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * 162) → s'.status = .Running →
      KStateMatches env (stCopyMid row) s' →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt s'
        (KSpatial (cfgCopy row) env (stCopyMid row) F) post) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s
      (KSpatial (cfgCopy row) env (stCopyPre row) F) post := by
  have hc := (cert_copyPre hrow).2
  simp only [checkCopyPre, Bool.and_eq_true] at hc
  have hx9 : s.readReg64 .x9 = sp + 6832#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 9#5 (by decide) (.spAdd 6832#64) hc.1.1 rfl
    simpa [evalKExpr, hsp] using h
  have hx10 : s.readReg64 .x10 = 1536#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 10#5 (by decide) (.const64 1536#64) hc.1.2 rfl
    simpa [evalKExpr] using h
  have hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 22#5 (by decide) (.var 96) hc.2 rfl
    simpa [evalKExpr, hv96] using h
  have hfw : fetchWordTree03 161 = some (.dataProc3 .W64 .MADD .x9 .x22 .x10 .x9) := by decide +kernel
  have hres : (sp + 6832#64) + BitVec.ofNat 64 row * 1536#64 =
      evalKExpr env (.spAdd (BitVec.ofNat 64 (6832 + 1536 * row))) := by
    change (sp + 6832#64) + BitVec.ofNat 64 row * 1536#64 =
      env.sp + BitVec.ofNat 64 (6832 + 1536 * row)
    rw [hsp]
    rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;> bv_omega
  have hpc162 : (b + BitVec.ofNat 64 (4 * 161)) + 4#64 = b + BitVec.ofNat 64 (4 * 162) := by bv_omega
  exact step_gpr_pure03 (by decide) hpc hrun (fetch_blk03_seg2a (by omega) (by omega) hfw)
    (eval_madd_x9_x22_x10 hx9 hx10 hx22) hres hm
    (fun s' hs' hrun' hm' => hnext s' (hs'.trans hpc162) hrun' hm')

attribute [local irreducible] stCopyMid

private theorem seg2_row_copy_lt2_wp [MlKemPlacement] {b sp : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} (hrow : row < 2) {F : SepProp}
    {s : State} {P : SepProp}
    (hexit : Seg2RowExit b sp rho row
      (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 1536 ∗ F) s P) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0504#64) s P
      (fun sf Pf =>
        sf.pc = b + 0x0504#64 ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp sf ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
        (∃ extra : Nat, allLanesDone 3 (rowSeeds rho row) extra = true) ∧
        ∃ tA : BTree (BitVec 64) 9,
          (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
          (Pf ⊢ Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
            memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
            memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
            memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 1536 ∗ F)) := by
  rcases hexit with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22,
    extra, tA, sampled, hws, hdone, hinv, htA, hP⟩
  let tSlots := btreeOfWords 0 (bytesToWords 204
    (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9
  have hSlots : MultiLaneSlots (sp + 4272#64) 544 3 hws = TreeMem (sp + 4272#64) 204 tSlots :=
    multiLaneSlots3_eq_treeMem sp fun c hc => (hinv c hc).1.1
  let Rest0 := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
    memRegion (sp + 2192#64) 1512 ∗ TreeMem (sp + 4272#64) 204 tSlots ∗
    memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.weaken_pre (P' := memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) (8 * 192) ∗ Rest0)
    (by
      rw [hSlots] at hP
      exact Entails.trans hP (by dsimp only [Rest0]; rw [show 8 * 192 = 1536 from rfl]; sep_frame)) ?_
  refine with_frozen_env hcl hro ?_
  refine sepWP_elim_treeMem (len := 192) (by decide) fun tB0 => ?_
  refine keccakRc_intro hro ?_
  let env := mkSegEnv sp row rho keccakZeroState keccakZeroState keccakZeroState s tSlots tB0
  have hmk : KStateMatches env (mkSegBaseState false) s ∧
      evalMemTree env (mkSegBaseState false).memA = tSlots ∧
      evalMemTree env (mkSegBaseState false).memB = tB0 :=
    mkSegState_matches (cfg := cfgCopy row) (hasSeedConsts := false) (slots01 := []) (slots2 := [])
      (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState)
      (tA := tSlots) (tB := tB0) (by decide) (by decide) hreg hx22
      (fun h => Bool.noConfusion h) (fun _ h => by simp at h) (fun _ h => by simp at h)
  let FF := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
    memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 12448#64) 24 ∗
    memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.weaken_pre (P' := KSpatial (cfgCopy row) env (mkSegBaseState false) FF)
    (by
      dsimp only [KSpatial, KConstsLoOpt, cfgCopy, Rest0, FF]
      rw [hmk.2.1, hmk.2.2, show env.sp = sp from rfl,
          show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
          show sp + BitVec.ofNat 64 4272 = sp + 4272#64 from rfl, emp_sepConj]
      sep_frame) ?_
  refine sepWP_runKRange_seg2a (cfgCopy_wf hrow) (by change 0 < 24; decide : env.rLoop < 24)
    (w := 155) (n := 6) (by omega) (by omega)
    (pc_of_eq hpc (by decide +kernel)) hrun hmk.1 (cert_copyPre hrow).1
    fun s1 hpc1 hrun1 hm1 => ?_
  refine step_madd_161 hrow (sp := sp) rfl rfl hpc1 hrun1 hm1 fun s2 hpc2 hrun2 hm2 => ?_
  refine sepWP_runKRange_seg2a (cfgCopy_wf hrow) (by change 0 < 24; decide : env.rLoop < 24)
    (w := 162) (n := 158) (by omega) (by omega) hpc2 hrun2 hm2 (cert_copyEndLt2 hrow).1
    fun s3 hpc3 hrun3 hm3 => ?_
  have hcE := (cert_copyEndLt2 hrow).2
  simp only [checkCopyEndLt2, Bool.and_eq_true] at hcE
  have hpst : s3.pstate = subsPState64 (BitVec.ofNat 64 (row + 1)) 3#64 := by
    have hp := eval_checked_pstate (ok := fun _ => true) hm3 (fun _ _ => rfl)
      (.var 101) 3#64 hcE.2 rfl
    simpa [evalKExpr, env, mkSegEnv, hx8] using hp
  have hspOut : KConstsLoOpt env.sp (cfgCopy row).hasConstsLo ∗
      (TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy row).offA) (cfgCopy row).lenA
        (evalMemTree env (stCopyEnd row).memA) ∗
        (TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy row).offB) (cfgCopy row).lenB
          (evalMemTree env (stCopyEnd row).memB) ∗ FF)) ⊢
      Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗
        memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 1536 ∗ F := by
    dsimp only [KConstsLoOpt, cfgCopy, FF]
    rw [emp_sepConj, show env.sp = sp from rfl,
        show sp + BitVec.ofNat 64 4272 = sp + 4272#64 from rfl]
    have htmA := treeMem_entails_memRegion (ptr := sp + 4272#64)
      (evalMemTree env (stCopyEnd row).memA) (len := 204) (by decide)
    rw [show 8 * 204 = 1632 from rfl] at htmA
    have htmB := treeMem_entails_memRegion (ptr := sp + BitVec.ofNat 64 (6832 + 1536 * row))
      (evalMemTree env (stCopyEnd row).memB) (len := 192) (by decide)
    rw [show 8 * 192 = 1536 from rfl] at htmB
    exact Entails.trans (sepConj_mono htmA (sepConj_mono_left htmB)) (by sep_frame)
  refine step_bCond_seg2a (w := 320) (cond := .EQ) (disp := 0x2d80#64)
    (by omega) (by omega) (by decide +kernel) hpc3 hrun3 (fun hT => ?_) (fun _hF => ?_)
  · rw [hpst] at hT
    rcases (show row = 0 ∨ row = 1 by omega) with rfl | rfl <;>
      exact absurd hT (by decide +kernel)
  · have hpcF : (s3.setPC (b + BitVec.ofNat 64 (4 * (320 + 1)))).pc = b + 0x0504#64 :=
      setPC_fall_eq s3 b 320 0x0504#64 (by decide +kernel)
    rcases extract_segRegInv (row := row) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl hcE.1 with ⟨hregF, hx8F, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcF (by simpa [State.setPC] using hrun3) fun hclF hroF =>
      ⟨hpcF, by simpa [State.setPC] using hrun3, hclF, hroF, hregF,
        by simpa [evalKExpr, env, mkSegEnv, hx8] using hx8F,
        ⟨extra, hdone⟩, tA, htA, hspOut⟩

private theorem memRegion_4608_split3 (sp : BitVec 64) :
    memRegion (sp + 6832#64) 4608 =
      memRegion (sp + 6832#64) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 := by
  rw [memRegion_split' (b := sp + 6832#64) (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (n := 1536) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 2))
        (n := 1536) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]

private theorem rowSeeds_eq_take32 {rho : List (BitVec 8)} (hrho : rho.length = 32) (row : Nat) :
    rowSeeds rho row = fun col => rho.take 32 ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col] := by
  funext col
  simp [rowSeeds, List.take_of_length_le (Nat.le_of_eq hrho)]

private theorem seg2_diverge_safeSepWP [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (hNotMat : ¬ Shake128MatrixTerminates rho 3) {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = 0#64) :
    SafeSepWP (blkPC03.rebase b (fun _ => none)) s
      (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 96#64) 240 ∗ memRegion (sp + 416#64) 1776 ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (fun _ _ => False) := by
  refine SafeSepWP.of_sepWP (mid := s.pc) ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) (8 * 30) ∗
      (memRegion (sp + 416#64) (8 * 222) ∗
        (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
          memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
          memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
          memRegion (sp + 13984#64) 504 ∗ F)))
    (by rw [show 8 * 30 = 240 from rfl, show 8 * 222 = 1776 from rfl]; sep_frame) ?_
  refine sepWP_elim_treeMem (len := 30) (by decide) fun tLo => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 416#64) (8 * 222) ∗
      (TreeMem (sp + 96#64) 30 tLo ∗ Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_memA_join sp rho tLo tHi with ⟨tA0, htA0, hjoin0⟩
  refine SepWP.done rfl hrun ?_
  have hpre0 : TreeMem (sp + 416#64) 222 tHi ∗
      (TreeMem (sp + 96#64) 30 tLo ∗ Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F) ⊢
      Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA0 ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗
        (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 0)) 1536 ∗
          (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
            memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 ∗ F)) := by
    rw [memRegion_4608_split3 sp, ← hjoin0,
        show sp + BitVec.ofNat 64 (6832 + 1536 * 0) = sp + 6832#64 from rfl]
    sep_frame
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 0) (by omega) hpc hrun hcl hro hreg hx8 htA0)
    fun sm0 Pm0 hex0 => SafeSepWP.of_sepWP <| SepWP.mono (seg2_row_copy_lt2_wp (by omega) hex0) ?_) hpre0
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, ⟨e0, hd0⟩, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 1) (by omega) hpc1 hrun1 hcl1 hro1 hreg1 hx8_1 htA1)
    fun sm1 Pm1 hex1 => SafeSepWP.of_sepWP <| SepWP.mono (seg2_row_copy_lt2_wp (by omega) hex1) ?_)
    (Entails.trans hP1 (by sep_frame))
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, ⟨e1, hd1⟩, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 2) (by omega) hpc2 hrun2 hcl2 hro2 hreg2 hx8_2 htA2)
    fun _sm2 _Pm2 hex2 => ?_)
    (Entails.trans hP2 (by sep_frame))
  rcases hex2 with ⟨_, _, _, _, _, _, _, e2, _, _, _, hd2, _, _, _⟩
  rw [rowSeeds_eq_take32 hrho 0] at hd0
  rw [rowSeeds_eq_take32 hrho 1] at hd1
  rw [rowSeeds_eq_take32 hrho 2] at hd2
  exact False.elim (hNotMat (matrixTerminates3_of_rows_ij hd0 hd1 hd2))

end Blk03Seg2Diverge

private def mlkemBlk03DivPre : MlkemBlk03Args → State → SepProp :=
  fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ret ∧ s0.readReg64 .x1 = a.hdrA ∧
      s0.readReg64 .x2 = a.randA ∧ s0.readReg64 .x3 = a.esA ∧
      s0.readReg64 .x4 = 2080#64 ∧ s0.readReg64 .x5 = a.ssA ∧
      s0.readReg64 .x6 = 32#64 ∧ a.hdr64.length = 64 ∧ a.rand.length = 32 ∧
      ¬ Shake128MatrixTerminates (a.hdr64.take 32) 3⌝ ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗
      memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18160

private theorem blk03_encaps1_diverge_safe_ok :
    MlKemBlockSafeOk 3 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemBlk03DivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC03 blkPl03 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP fun a s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, mlkemBlk03DivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hhdr, hrand, hNotMat⟩ => ?_
  have hrho : (a.hdr64.take 32).length = 32 := by simp [hhdr]
  refine SafeSepWP.weaken_pre
    (P := (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗
      memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18160 ∗ emp)
    ?_ (by sep_frame)
  refine safeSepWP_seq_env hcl0 hro0
    (seg1_wp hb hbase s0 a emp hhdr hrand hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hreg1, hx8_1, hP1⟩
  exact SafeSepWP.weaken_pre
    (seg2_diverge_safeSepWP hb hbase hrho hNotMat hpc1 hrun1 hcl1 hro1 hreg1 hx8_1) hP1

/-! ## 2. `B19` (`mlkem768::incremental::encapsulate1`) Prologue & Divergence -/

section
set_option linter.literalFetch false
gen_placed_fetches blkPC19 blkLib19 blkTree19 blk19_code_eq blk19_tree_size
  via_placement blkPl19 blkPlaceable19 [0x0000 → 0x006c]
end

@[local simp, local arm64_norm, local wp_norm]
private theorem blkPl19_ρ [MlKemPlacement] (sym : String) :
    blkPl19.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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

private theorem blk19_prologue_ok [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl19 b) (hbase : blkPl19.base = b)
    (s0 : State) (a : MlkemEncaps1Args) (Rest : SepProp)
    (hge : 64 ≤ a.hdr.length)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx8 : s0.readReg64 .x8 = a.ret) (hx0 : s0.readReg64 .x0 = a.hdrA)
    (hx1 : (s0.readReg64 .x1).toNat = a.hdr.length)
    (hx2 : s0.readReg64 .x2 = a.randA) (hx3 : s0.readReg64 .x3 = a.esA)
    (hx4 : s0.readReg64 .x4 = 2080#64) (hx5 : s0.readReg64 .x5 = a.ssA)
    (hx6 : s0.readReg64 .x6 = 32#64) :
    SepWP (blkPC19.rebase b (fun _ => none)) (mbase 3) s0
      ((a.hdrA ↦ₛ a.hdr.take 64) ∗
        memRegion (s0.sp - 144#64) 128 ∗
        memRegion ((s0.sp - 144#64) + 128#64) 16 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = s0.sp - 144#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .lr = b + 0x0064#64 ∧
        s1.readReg64 .x0 = a.ret ∧ s1.readReg64 .x1 = s0.sp - 144#64 ∧
        s1.readReg64 .x2 = a.randA ∧ s1.readReg64 .x3 = a.esA ∧
        s1.readReg64 .x4 = 2080#64 ∧ s1.readReg64 .x5 = a.ssA ∧
        s1.readReg64 .x6 = 32#64 ∧ UnspilledSaved19 s0 s1 ∧
        (P1 ⊢ (a.hdrA ↦ₛ a.hdr.take 64) ∗
          ((s0.sp - 144#64) ↦ₛ a.hdr.take 64) ∗
          memRegion ((s0.sp - 144#64) + 64#64) 64 ∗
          SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗ Rest)) := by
  subst hbase
  have hh64 : (a.hdr.take 64).length = 64 := List.length_take_of_le hge
  generalize a.hdr.take 64 = h64 at hh64 ⊢
  rw [memRegion_split' (b := (s0.sp - 144#64) + 128#64) (b' := (s0.sp - 144#64) + 136#64)
        (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  apply SepWP.memRegion8_cell ((s0.sp - 144#64) + 128#64); intro sf0
  apply SepWP.memRegion8_cell ((s0.sp - 144#64) + 136#64); intro sf1
  apply SepWP.of_memRegion_vecRangeMem 8 (s0.sp - 144#64); intro stkV
  rw [vecRangeMem_eq_pointsToBytes]
  have hstk128 : (vecRangeBytes 8 stkV).length = 128 := vecRangeBytes_length 8 stkV
  generalize vecRangeBytes 8 stkV = stk0 at hstk128 ⊢
  simp only [Reg.x1] at hx1
  wp_step
  refine step_bCond_taken (pc := blkPl19.base + 4#64) (off := 16#64)
    (dst := blkPl19.base + 20#64) (c := .HI)
    (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm])
    (by simp only [wp_norm, arm64_norm, conditionHolds_hi_subsPState64, BitVec.ult]
        rw [hx1]; exact decide_eq_true (by omega))
    (by bv_omega) ?_
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
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, ?_⟩
  · rw [State.spAligned] at hsp0 ⊢; simp only [wp_norm, arm64_norm]; exact hsp0
  · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs⟩
  · rw [readLE_m1_eq _ _ _ 64 hmid128 (by decide),
        readLE_m1_eq _ _ _ 72 hmid128 (by decide)]
    have hfin_fold : ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 (h64.getD 0 0#8))
        33 (ByteSlice.readLE mid 96 8)) 41 (ByteSlice.readLE mid 104 8))
      17 (ByteSlice.readLE mid 80 8)) 25 (ByteSlice.readLE mid 88 8))
      1 (ByteSlice.readLE mid 64 8)) 9 (ByteSlice.readLE mid 72 8) = blk19Fin h64 mid := rfl
    rw [hfin_fold, ← hmid_eq]
    dsimp only [SavedFrame19, Reg.x29, Reg.lr]
    have ha16 : (s0.sp - 144#64) + 128#64 = s0.sp - 16#64 := by bv_omega
    have ha8 : ((s0.sp - 144#64) + 128#64) + 8#64 = s0.sp - 8#64 := by bv_omega
    rw [ha8, ha16]
    refine Entails.trans (sepConj_mono_left (blk19Fin_entails (s0.sp - 144#64) hh64 hstk128)) ?_
    sep_frame

private def mlkemEncaps1DivPre : MlkemEncaps1Args → State → SepProp :=
  fun a s0 =>
    ⌜s0.readReg64 .x8 = a.ret ∧ s0.readReg64 .x0 = a.hdrA ∧
      (s0.readReg64 .x1).toNat = a.hdr.length ∧ s0.readReg64 .x2 = a.randA ∧
      s0.readReg64 .x3 = a.esA ∧ s0.readReg64 .x4 = 2080#64 ∧
      s0.readReg64 .x5 = a.ssA ∧ s0.readReg64 .x6 = 32#64 ∧
      ¬ Mlkem768Encaps1Terminates a.hdr⌝ ∗
      (a.hdrA ↦ₛ a.hdr) ∗ (a.randA ↦ₛ a.rand.toList) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      stackAt s0.sp 18304

private theorem blk19_encaps1_diverge_safe_ok :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemEncaps1DivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC19 blkPl19 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP fun a s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, mlkemEncaps1DivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hNotTerm⟩ => ?_
  have hge : 64 ≤ a.hdr.length := Nat.le_of_not_lt fun hlt => hNotTerm (Or.inl hlt)
  have hNotMat : ¬ Shake128MatrixTerminates ((a.hdr.take 64).take 32) 3 := by
    intro hMat
    rw [List.take_take] at hMat
    exact hNotTerm (Or.inr hMat)
  have hhdr_sp : (a.hdrA ↦ₛ a.hdr) =
      (a.hdrA ↦ₛ a.hdr.take 64) ∗ ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) := by
    conv => lhs; rw [← List.take_append_drop 64 a.hdr]
    rw [pointsToBytes_append, List.length_take_of_le hge]
  rw [hhdr_sp, stackAt18304_split s0.sp]
  set Rest0 : SepProp := ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) ∗ (a.randA ↦ₛ a.rand.toList) ∗
    memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
    stackAt (s0.sp - 144#64) 18160
  refine SafeSepWP.weaken_pre
    (P := (a.hdrA ↦ₛ a.hdr.take 64) ∗ memRegion (s0.sp - 144#64) 128 ∗
      memRegion ((s0.sp - 144#64) + 128#64) 16 ∗ Rest0)
    ?_ (by dsimp only [Rest0]; sep_frame)
  refine safeSepWP_seq_env hcl0 hro0
    (blk19_prologue_ok hb hbase s0 a Rest0 hge hpc hrun hsp0 hx8 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, _hus1, hP1⟩
  let b03 : MlkemBlk03Args :=
    { ret := a.ret, hdrA := s0.sp - 144#64, hdr64 := a.hdr.take 64,
      randA := a.randA, rand := a.rand.toList, esA := a.esA, ssA := a.ssA }
  let Frame19 : SepProp := SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
    memRegion ((s0.sp - 144#64) + 64#64) 64 ∗ (a.hdrA ↦ₛ a.hdr.take 64) ∗
    ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64)
  refine SafeSepWP.weaken_pre
    (SafeSepWP.call_subroutine_frame
      (mlkemSafeCall_of_blockSafeOk (blkPC19.rebase b (fun _ => none)) blk03_encaps1_diverge_safe_ok)
      (x := b03) (F := Frame19) (ret_pc := b + 0x0064#64) hpc1 hrun1 hspA1 hlr1
      (fun R1 hm1 => ?_)
      (fun _sf _ _ _ _ _R1 hm_false => False.elim (not_satisfies_false_sepConj (by
        dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
          falsePostSpec] at hm_false
        rw [sepConj_assoc] at hm_false
        exact hm_false))))
    hP1
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    falsePostSpec, mlkemBlk03DivPre, b03, Frame19, Rest0] at hm1 ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
  refine ⟨hcl1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hro1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
    List.length_take_of_le hge, a.rand.toList_length, hNotMat⟩, ?_⟩
  rw [hsp1]; exact Satisfies.mono (by sep_frame) hm1

/-! ## 3. Layer 1 Real-ELF Divergence Theorems for `lsMlkem768Encaps1Sym` -/

/-- Step-witnessed operational divergence for `lsMlkem768Encaps1Sym` (`B19`,
    `mlkem768::incremental::encapsulate1`) when `¬ MlkemEncaps1StateTerminates u`. -/
theorem mlkemEncaps1_diverge_of_not_stateTerminates_step
    {stk : Nat} (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemEncaps1StateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  have hpre_at : u.mem ⊨ (mlkemEncaps1AtSpec stk K).pre x u ∗ R := by
    simpa only [keepsFs] using hpre
  have hNotCall : ¬ Mlkem768Encaps1Terminates x.hdr := by
    intro hCall
    exact hNotTerm ((mlkemEncaps1StateTerminates_iff_of_atSpec_pre hpre_at).mpr hCall)
  dsimp only [mlkemEncaps1AtSpec] at hpre_at
  simp only [sepConj_assoc] at hpre_at
  rw [satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hspat⟩ := hpre_at
  have hstk18304 : 18304 ≤ stk := hstk
  rw [stackAt_shrink u.sp stk 18304 hstk18304 hfit] at hspat
  set slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 18304)
  let a : MlkemEncaps1Args :=
    { ret := x.ret, hdrA := x.hdrA, hdr := x.hdr, randA := x.randA,
      rand := x.rand, esA := x.esA, ssA := x.ssA }
  have hpre_div : u.mem ⊨ mlkemEncaps1DivPre a u ∗ (slack ∗ R) := by
    dsimp only [mlkemEncaps1DivPre, a]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hNotCall⟩,
      Satisfies.mono (by sep_frame) hspat⟩
  exact c2_mlkem_diverge_of_blockSafeOk_false (by decide) blk19_encaps1_diverge_safe_ok
    (by intro _ s _; cases s; rfl)
    hLs hExt (c2_resolve_mlkem768Encaps1_eq hLs) W hpc hrun hsp hInv hFr hpre_div

/-- Layer 1 operational divergence for `lsMlkem768Encaps1Sym` (`B19`,
    `mlkem768::incremental::encapsulate1`): every state `v` reachable from a stuck entry `u` has
    `v.status = .Running`. -/
theorem mlkemEncaps1_diverge_of_not_stateTerminates
    {stk : Nat} (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemEncaps1StateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) := by
  have ⟨h1, h2⟩ := mlkemEncaps1_diverge_of_not_stateTerminates_step hstk hfit hLs hExt W
    hpc hrun hsp hInv hFr hpre hNotTerm
  exact ⟨fun v hv => (h1 v hv).1, fun v hv => (h2 v hv).1⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768Encaps1
