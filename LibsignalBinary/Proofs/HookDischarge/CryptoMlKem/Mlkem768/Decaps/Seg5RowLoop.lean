/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowInit

/-!
# `decapsulate_compressed_key` (`B04`) — `Seg5` Extra-Block Loop & Single-Row `SampleNTT` (`Seg5RowLoop`)

Proves `seg5_row_clamp_extra1`, `seg5_row_bodyA_wp`, `seg5_row_bodyB_wp`, and instantiates
`sampleNttRow_safeSepWP` (`seg5_row_safe_ok`) and `sampleNttRow_sepWP` (`seg5_row_ok`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState Shake128SeedTerminates keccakF1600 shake128BlockAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone sampleNttRow_safeSepWP sampleNttRow_sepWP
  step_rej_site_extra1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem btreeWords btreeWords_length memRegion_entails_exists_treeMem
  treeMem_entails_memRegion wordsToBytes wordsToBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KSpatial KStateMatches matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  readSlot slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  rejBufReadable_of_treeMem wordsToBytes_btreeWords_eq_extractRate_21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memB eval_checked_pstate
  eval_checked_slot exprVarsOk extendLoopVars progBases rhoW rowPermState
  rowPermState_succ rowSeeds shake128BlockAt_rowSeeds_eq specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  condCC_256_of_le271 condCS_256_of_le271 condHI_255_of_le271 keccakRc_intro
  raw_sampled_le271 rowPermState_size slotHoldsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  eq_some_getD sepWP_drop_left)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit (
  checkPStateEq evalExprList25_varRange expVarRange pc_add_eq setPC_disp_w_eq setPC_fall_w_eq
  slotHoldsLo_of_sitePreserved slotHolds_of_sitePreserved status_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row (
  eval_checked_slotLo not_mem_of_dec readReg64_setPC sepWP_mono_pre slotHolds_setPC
  specEnvSteps_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  checkInstrsAt04 fetchesInstrsAt_blk04_seg5 inv01Slots inv2Slots postExtra01Slots
  postExtra2Slots runKRange04 sepWP_of_runKRange04 slotsEA slotsEB)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init (
  Seg5ConstWordsInv Seg5LoopState Seg5RegInv Seg5RowDone cfgClamp04 cfgClamp04_wf cfgExtra04
  cfgExtra04_wf cfgRejExtra1_04 cfgRejExtra1_04_valid multiLaneSampled3_eq_treeMem04
  step_bCond_seg5 step_b_seg5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp (
  checkClampEnd04 checkConstWordsMemA04 checkSegRegGprs04 extract_constWords04
  extract_segRegInv04 finish_clamp_branch04 mkSegEnv04 mkSegState04 mkSegState04_matches
  runAndCheckKProg04 sepWP_of_runAndCheckKProg04 with_frozen_env04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowInit (
  seg5_row_init_wp segRegInv04_of_sitePreserved segRegInv04_setPC)

attribute [local irreducible] keccakF1600 blkPC04

/-! ## 1. Extra-Block Symbolic Certificates (`stepsExtra04`, Clamp & `rej_sample` Fetches) -/

private def stExtra0_04 : KState := mkSegState04 cfgExtra04 true inv01Slots inv2Slots

private def stepsExtra04 : List KProgStep :=
  [ .range 6390 24,
    .loop 6414 197 9#5 slotsEA (expVarRange 0) (expVarRange 25) 2000,
    .range 6612 90,
    .loop 6702 202 11#5 slotsEB (expVarRange 50) (expVarRange 75) 3000,
    .range 6905 74 ]

private def checkExtraEnd04 (st : KState) : Bool :=
  checkSegRegGprs04 st (.var 101) &&
  checkConstWordsMemA04 st &&
  (st.gprs.get 11).beq (.const64 0#64) &&
  (st.gprs.get 9).beq (.spAdd 20715#64) &&
  ((List.range 21).all fun j =>
    (st.memB.get j).beq (.var (2000 + j)) &&
    (st.memB.get (21 + j)).beq (.var (2025 + j)) &&
    (st.memB.get (42 + j)).beq (.var (3000 + j))) &&
  ((List.range 25).all fun idx =>
    let sl01 := postExtra01Slots.getD idx (.vreg 0)
    let sl2 := postExtra2Slots.getD idx (.vreg 0)
    slotValid cfgClamp04 sl01 &&
      (readSlot cfgClamp04 st sl01).1.beq (.var (2000 + idx)) &&
      (readSlot cfgClamp04 st sl01).2.beq (.var (2025 + idx)) &&
      slotValid cfgClamp04 sl2 &&
      (readSlot cfgClamp04 st sl2).1.beq (.var (3000 + idx)))

private theorem cert_stepsExtra04 :
    runAndCheckKProg04 cfgExtra04 6390 6980 6390 6979 1500 stepsExtra04 stExtra0_04
      (fun _ st => checkExtraEnd04 st) = true := by decide +kernel

private def stExtraClamp0_04 : KState := mkSegState04 cfgClamp04 true postExtra01Slots postExtra2Slots
private def stExtraC1_04 : KState := (runKRange04 cfgClamp04 7184 48 stExtraClamp0_04).getD stExtraClamp0_04
private def stExtraCHi_04 : KState := (runKRange04 cfgClamp04 7233 1 stExtraC1_04).getD stExtraC1_04
private def stExtraCEnd_04 : KState := (runKRange04 cfgClamp04 6388 1 stExtraCHi_04).getD stExtraCHi_04

private theorem cert_extraC1_04 : runKRange04 cfgClamp04 7184 48 stExtraClamp0_04 = some stExtraC1_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 7184 48 stExtraClamp0_04) stExtraClamp0_04 (by decide +kernel)
private theorem cert_extraCHi_04 : runKRange04 cfgClamp04 7233 1 stExtraC1_04 = some stExtraCHi_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 7233 1 stExtraC1_04) stExtraC1_04 (by decide +kernel)
private theorem cert_extraCEnd_04 : runKRange04 cfgClamp04 6388 1 stExtraCHi_04 = some stExtraCEnd_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 6388 1 stExtraCHi_04) stExtraCHi_04 (by decide +kernel)
private theorem cert_epstateC1_04 : checkPStateEq stExtraC1_04 (.var 902) (.const64 256#64) = true := by decide +kernel
private theorem cert_epstateCHi_04 : checkPStateEq stExtraCHi_04 (.var 901) (.const64 256#64) = true := by decide +kernel
private theorem cert_epstateCEnd_04 : checkPStateEq stExtraCEnd_04 (.var 900) (.const64 255#64) = true := by decide +kernel
private theorem cert_echkC1_04 : checkClampEnd04 stExtraC1_04 (!false) = true := by decide +kernel
private theorem cert_echkCHi_04 : checkClampEnd04 stExtraCHi_04 (!false) = true := by decide +kernel
private theorem cert_echkCEndT_04 : checkClampEnd04 stExtraCEnd_04 (!true) = true := by decide +kernel
private theorem cert_echkCEndF_04 : checkClampEnd04 stExtraCEnd_04 (!false) = true := by decide +kernel
private theorem cert_rejExtraO04 : checkInstrsAt04 6980 (rejOuterInstrs cfgRejExtra1_04) = true := by decide +kernel
private theorem cert_rejExtraI04 : checkInstrsAt04 6991 (rejInnerInstrs .varA) = true := by decide +kernel

attribute [local irreducible] stExtraC1_04 stExtraCHi_04 stExtraCEnd_04

private theorem okExtra04_all :
    ([2000, 3000].all fun b =>
      (List.range 25).all fun i =>
        validSpecVar 1500 (progBases stepsExtra04) (b + i) &&
        validSpecVar 1500 (progBases stepsExtra04) (b + 25 + i)) = true := by decide +kernel

private theorem okExtra04_lo (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsExtra04) (b + i) = true := by
  have h1 := (List.all_eq_true.mp okExtra04_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).1

private theorem okExtra04_hi (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsExtra04) (b + 25 + i) = true := by
  have h1 := (List.all_eq_true.mp okExtra04_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).2

private theorem okExtra04_low {id : Nat} (h : id < 1500) :
    validSpecVar 1500 (progBases stepsExtra04) id = true := by
  simp [validSpecVar, Nat.blt_eq, h]

private theorem extendLoopVars_lt (e : KEnv) (b : Nat) (lo hi : KeccakState) {id : Nat}
    (h : id < b) : (extendLoopVars e b lo hi).vars id = e.vars id := by simp [extendLoopVars, h]
private theorem extendLoopVars_lo (e : KEnv) (b : Nat) (lo hi : KeccakState) {idx : Nat}
    (h : idx < 25) : (extendLoopVars e b lo hi).vars (b + idx) = (keccakF1600 lo).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + idx < b) by omega,
    show b + idx < b + 25 by omega, show b + idx - b = idx by omega, ↓reduceIte, Array.getD]
private theorem extendLoopVars_hi (e : KEnv) (b : Nat) (lo hi : KeccakState) {idx : Nat}
    (h : idx < 25) : (extendLoopVars e b lo hi).vars (b + 25 + idx) = (keccakF1600 hi).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + 25 + idx < b) by omega,
    show ¬(b + 25 + idx < b + 25) by omega, show b + 25 + idx < b + 50 by omega,
    show b + 25 + idx - (b + 25) = idx by omega, ↓reduceIte, Array.getD]

private theorem specEnv_stepsExtra04_vars {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row extra : Nat} {env0 : KEnv}
    (hv0 : ∀ idx, idx < 25 → env0.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64)
    (hv1 : ∀ idx, idx < 25 → env0.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64)
    (hv2 : ∀ idx, idx < 25 → env0.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64) :
    let envS := specEnvSteps env0 stepsExtra04
    (∀ id, id < 2000 → envS.vars id = env0.vars id) ∧
    (∀ idx, idx < 25 → envS.vars (2000 + idx) = (rowPermState rho row 0 (extra + 3)).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (2025 + idx) = (rowPermState rho row 1 (extra + 3)).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3000 + idx) = (rowPermState rho row 2 (extra + 3)).getD idx 0#64) := by
  dsimp only [stepsExtra04, specEnvSteps]
  set e1 := extendLoopVars env0 2000 (evalExprList25 env0 (expVarRange 0)) (evalExprList25 env0 (expVarRange 25)) with he1
  set e2 := extendLoopVars e1 3000 (evalExprList25 e1 (expVarRange 50)) (evalExprList25 e1 (expVarRange 75)) with he2
  have hp0 : keccakF1600 (evalExprList25 env0 (expVarRange 0)) = rowPermState rho row 0 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 (extra + 2)) (fun idx h => by simpa using hv0 idx h), rowPermState_succ]
  have hp1 : keccakF1600 (evalExprList25 env0 (expVarRange 25)) = rowPermState rho row 1 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 (extra + 2)) hv1, rowPermState_succ]
  have hp2 : keccakF1600 (evalExprList25 e1 (expVarRange 50)) = rowPermState rho row 2 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 (extra + 2))
      (fun idx h => by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hv2 idx h]), rowPermState_succ]
  refine ⟨fun id hid => by rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lt _ _ _ _ hid],
    fun idx h => by rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lo _ _ _ _ h, hp0],
    fun idx h => by rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_hi _ _ _ _ h, hp1],
    fun idx h => by rw [he2, extendLoopVars_lo _ _ _ _ h, hp2]⟩

/-! ## 2. Extra-Block Clamp Dispatch (`seg5_row_clamp_extra1`) -/

@[expose] def offRowEntry04 : BitVec 64 := BitVec.ofNat 64 (4 * 4315)
@[expose] def offRowDone04 : BitVec 64 := BitVec.ofNat 64 (4 * 4150)
@[expose] def offLoopHead04 : BitVec 64 := BitVec.ofNat 64 (4 * 6390)
@[expose] def offMidExtra04 : BitVec 64 := BitVec.ofNat 64 (4 * 6984)
@[expose] def offClampExtra04 : BitVec 64 := BitVec.ofNat 64 (4 * 7184)

private theorem seg5_row_clamp_extra1 [MlKemPlacement] {b sp fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {F : SepProp} {tA : BTree (BitVec 64) 9}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {s : State}
    (hpc : s.pc = b + offClampExtra04) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg5RegInv sp fpVal s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row)
    (htA : Seg5ConstWordsInv sp rho tA)
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) (extra + 1) sampled hws)
    (hs01 : ∀ idx, idx < 25 → slotHolds cfgClamp04 s tA (postExtra01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
      ((rowPermState rho row 1 (extra + 3)).getD idx 0#64))
    (hs2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp04 s tA (postExtra2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 (extra + 3)).getD idx 0#64)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) (extra + 1) then b + offRowDone04 else b + offLoopHead04) s
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗
        MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) (extra + 1) then Seg5RowDone b sp fpVal rho row F sf Pf
        else Seg5LoopState b sp fpVal rho row F (extra + 1) sf Pf) := by
  let tB : BTree (BitVec 64) 9 := BTree.ofFn 9 fun i =>
    if i < 3 then BitVec.ofNat 64 (sampled i) else 0#64
  have htB : ∀ i, i < 3 → tB.get i = BitVec.ofNat 64 (sampled i) := fun i hi => by
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi]
  let k2Hi : Nat → BitVec 64 := fun idx =>
    if h : idx < 25 then Classical.choose (hs2 idx h) else 0#64
  let env := mkSegEnv04 sp fpVal row rho (rowPermState rho row 0 (extra + 3))
    (rowPermState rho row 1 (extra + 3)) (rowPermState rho row 2 (extra + 3)) k2Hi s tA tB
  rcases mkSegState04_matches (cfg := cfgClamp04) (hasConsts := true)
    (slots01 := postExtra01Slots) (slots2 := postExtra2Slots)
    (k0 := rowPermState rho row 0 (extra + 3)) (k1 := rowPermState rho row 1 (extra + 3))
    (k2 := rowPermState rho row 2 (extra + 3)) (k2Hi := k2Hi) (tA := tA) (tB := tB)
    (by decide) (by decide) hreg hx19 (fun _ => htA)
    (fun i hi => hs01 i (by simpa [postExtra01Slots] using hi))
    (fun i hi => by
      have hi25 : i < 25 := by simpa [postExtra2Slots] using hi
      simpa [k2Hi, hi25] using Classical.choose_spec (hs2 i hi25)) with ⟨hm0, htA_eq, htB_eq⟩
  apply with_frozen_env04 hcl hro
  apply keccakRc_intro hro
  let FF := memRegion (sp + 22400#64) 1512 ∗
    MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgClamp04 env stExtraClamp0_04 FF) ?_ ?_
  · dsimp only [KSpatial, stExtraClamp0_04, FF]
    rw [multiLaneSampled3_eq_treeMem04 sp sampled tB
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide)), htA_eq, htB_eq]
    dsimp only [cfgClamp04]
    rw [show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show env.sp = sp from rfl,
      show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
      show sp + BitVec.ofNat 64 19168 = sp + 19168#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0) := by simpa [env, mkSegEnv04] using htB 0 (by decide)
  have hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1) := by simpa [env, mkSegEnv04] using htB 1 (by decide)
  have hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2) := by simpa [env, mkSegEnv04] using htB 2 (by decide)
  have hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, h]
  have hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  have hr0 : env.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 7184) (count := 48)
    (st := stExtraClamp0_04) (st' := stExtraC1_04) (s := s)
    (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_extraC1_04 hpc hrun hm0 ?_
  intro s1 hpc1 hrun1 hm1
  have hp1 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm1
    (fun _ _ => rfl) (.var 902) (.const64 256#64) cert_epstateC1_04 rfl rfl
  refine step_bCond_seg5 (w := 7232) (cond := .CC) (disp := BitVec.ofInt 64 (-3368))
    (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
    (pc_add_eq hpc1 (by decide +kernel)) hrun1 ?_ ?_

  · intro hcc
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcc
    have hs2lt : sampled 2 < 256 := of_decide_eq_true hcc
    have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
      Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 2 (by decide)) (by omega)
    exact finish_clamp_branch04 hraw (matches_setPC hm1 _) rfl rfl
      (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
      (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
      (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
      hv0 hv1 hv2 hb0 hb1 hb2 false hdone
      (setPC_disp_w_eq s1 b 7232 (BitVec.ofInt 64 (-3368)) 6390 (by decide +kernel))
      ((status_setPC _ _).trans hrun1) cert_echkC1_04
  · intro hccF
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hccF
    have hs2ge : 256 ≤ sampled 2 := by have := of_decide_eq_false hccF; omega
    refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 7233) (count := 1)
      (st := stExtraC1_04) (st' := stExtraCHi_04) (s := s1.setPC (b + BitVec.ofNat 64 (4 * (7232 + 1))))
      (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_extraCHi_04
      (setPC_fall_w_eq s1 b 7232 7233 (by decide +kernel)) ((status_setPC _ _).trans hrun1) (matches_setPC hm1 _) ?_
    intro s2 hpc2 hrun2 hm2
    have hp2 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm2
      (fun _ _ => rfl) (.var 901) (.const64 256#64) cert_epstateCHi_04 rfl rfl
    refine step_bCond_seg5 (w := 7234) (cond := .CS) (disp := BitVec.ofInt 64 (-3384))
      (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_ ?_
    · intro hcs
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcs
      have hs1ge : 256 ≤ sampled 1 := of_decide_eq_true hcs
      refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 6388) (count := 1)
        (st := stExtraCHi_04) (st' := stExtraCEnd_04)
        (s := s2.setPC (b + BitVec.ofNat 64 (4 * 7234) + BitVec.ofInt 64 (-3384)))
        (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_extraCEnd_04
        (setPC_disp_w_eq s2 b 7234 (BitVec.ofInt 64 (-3384)) 6388 (by decide +kernel))
        ((status_setPC _ _).trans hrun2) (matches_setPC hm2 _) ?_
      intro s3 hpc3 hrun3 hm3
      have hp3 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm3
        (fun _ _ => rfl) (.var 900) (.const64 255#64) cert_epstateCEnd_04 rfl rfl
      refine step_bCond_seg5 (w := 6389) (cond := .HI) (disp := BitVec.ofInt 64 (-8956))
        (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
        (pc_add_eq hpc3 (by decide +kernel)) hrun3 ?_ ?_
      · intro hhi
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhi
        have hs0ge : 256 ≤ sampled 0 := of_decide_eq_true hhi
        have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = true :=
          hraw.allLanesDone_iff_ge256.mpr fun i hi => by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption
        exact finish_clamp_branch04 hraw (matches_setPC hm3 _) rfl rfl (by simp [env, mkSegEnv04])
          (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          hv0 hv1 hv2 hb0 hb1 hb2 true hdone
          (setPC_disp_w_eq s3 b 6389 (BitVec.ofInt 64 (-8956)) 4150 (by decide +kernel))
          ((status_setPC _ _).trans hrun3) cert_echkCEndT_04
      · intro hhiF
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhiF
        have hs0lt : sampled 0 < 256 := by have := of_decide_eq_false hhiF; omega
        have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
          Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 0 (by decide)) (by omega)
        exact finish_clamp_branch04 hraw (matches_setPC hm3 _) rfl rfl (by simp [env, mkSegEnv04])
          (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          hv0 hv1 hv2 hb0 hb1 hb2 false hdone
          (setPC_fall_w_eq s3 b 6389 6390 (by decide +kernel))
          ((status_setPC _ _).trans hrun3) cert_echkCEndF_04
    · intro hcsF
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcsF
      have hs1lt : sampled 1 < 256 := by have := of_decide_eq_false hcsF; omega
      have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
        Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 1 (by decide)) (by omega)
      refine step_b_seg5 (w := 7235) (disp := BitVec.ofInt 64 (-3380))
        (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
        (setPC_fall_w_eq s2 b 7234 7235 (by decide +kernel)) ((status_setPC _ _).trans hrun2) ?_
      exact finish_clamp_branch04 hraw (matches_setPC (matches_setPC hm2 _) _) rfl rfl
        (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
        (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
        (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
        hv0 hv1 hv2 hb0 hb1 hb2 false hdone
        (setPC_disp_w_eq (s2.setPC _) b 7235 (BitVec.ofInt 64 (-3380)) 6390 (by decide +kernel))
        ((status_setPC _ _).trans ((status_setPC _ _).trans hrun2)) cert_echkCHi_04

/-! ## 3. Loop Body Halves (`seg5_row_bodyA_wp`, `seg5_row_bodyB_wp`) & Row Theorems -/

attribute [local irreducible] validSpecVar progBases specEnvSteps extendLoopVars
  TreeMem MultiLaneSlots MultiLaneSampled

private def Seg5MidState [MlKemPlacement] (b sp fpVal : BitVec 64) (rho : List (BitVec 8))
    (row extra : Nat) (F : SepProp) (s : State) (P : SepProp) : Prop :=
  s.pc = b + offMidExtra04 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  Seg5RegInv sp fpVal s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x19 = BitVec.ofNat 64 row ∧
  s.readReg64 .x11 = 0#64 ∧ s.readReg64 .x9 = sp + 20715#64 ∧
  ∃ (tA tB : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    Seg5ConstWordsInv sp rho tA ∧
    (∀ idx, idx < 25 →
      slotHolds cfgClamp04 s tA (postExtra01Slots.getD idx (.vreg 0))
        ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
        ((rowPermState rho row 1 (extra + 3)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHoldsLo cfgClamp04 s tA (postExtra2Slots.getD idx (.vreg 0))
        ((rowPermState rho row 2 (extra + 3)).getD idx 0#64)) ∧
    (∀ col, col < 3 →
      wordsToBytes (btreeWords (21 * col) 21 tB) = shake128BlockAt (rowSeeds rho row col) (extra + 3)) ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (P ⊢ TreeMem (sp + 20704#64) 63 tB ∗
      (MultiLaneSampled (sp + 19168#64) 3 sampled ∗
        (MultiLaneSlots (sp + 5680#64) 544 3 hws ∗
          (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗ F))))

private theorem slotHolds_clamp_to_extra04 {s : State} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {lo hi : BitVec 64} (h : slotHolds cfgClamp04 s tA sl lo hi) :
    slotHolds cfgExtra04 s tA sl lo hi := by cases sl <;> exact h

private theorem seg5_row_bodyA_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row extra : Nat} {F : SepProp}
    {s0 : State} {P0 : SepProp} (hInv : Seg5LoopState b sp fpVal rho row F extra s0 P0) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offMidExtra04) s0 P0
      (Seg5MidState b sp fpVal rho row extra F) := by
  rcases hInv with ⟨hpc0, hrun0, hcl0, hro0, hreg0, hx8_0, hx19_0,
    tA0, sampled, hws, htA0, hs01_0, hs2_0, hinv0, hP0⟩
  apply with_frozen_env04 hcl0 hro0
  refine sepWP_mono_pre (Entails.trans hP0 (Entails.trans (by sep_frame :
      TreeMem (sp + 144#64) 264 tA0 ∗ memRegion (sp + 22400#64) 1512 ∗
        MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗
        MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F ⊢
      memRegion (sp + 20704#64) 504 ∗
        (TreeMem (sp + 144#64) 264 tA0 ∗ memRegion (sp + 22400#64) 1512 ∗
          MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F))
    (sepConj_mono_left (memRegion_entails_exists_treeMem (ptr := sp + 20704#64) (len := 63) (by decide))))) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tB0
  let k2Hi : Nat → BitVec 64 := fun idx =>
    if h : idx < 25 then Classical.choose (hs2_0 idx h) else 0#64
  let env0 := mkSegEnv04 sp fpVal row rho (rowPermState rho row 0 (extra + 2))
    (rowPermState rho row 1 (extra + 2)) (rowPermState rho row 2 (extra + 2)) k2Hi s0 tA0 tB0
  rcases mkSegState04_matches (cfg := cfgExtra04) (hasConsts := true)
    (slots01 := inv01Slots) (slots2 := inv2Slots)
    (k0 := rowPermState rho row 0 (extra + 2)) (k1 := rowPermState rho row 1 (extra + 2))
    (k2 := rowPermState rho row 2 (extra + 2)) (k2Hi := k2Hi) (tA := tA0) (tB := tB0)
    (by decide) (by decide) hreg0 hx19_0 (fun _ => htA0)
    (fun i hi => slotHolds_clamp_to_extra04 (hs01_0 i (by simpa [inv01Slots] using hi)))
    (fun i hi => by
      have hi25 : i < 25 := by simpa [inv2Slots] using hi
      have hch := slotHolds_clamp_to_extra04 (Classical.choose_spec (hs2_0 i hi25))
      simpa [k2Hi, hi25] using hch) with ⟨hm0, htA_eq, htB_eq⟩
  apply keccakRc_intro hro0
  let FF := memRegion (sp + 22400#64) 1512 ∗
    MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgExtra04 env0 stExtra0_04 FF) ?_ ?_
  · unfold stExtra0_04; dsimp only [KSpatial, FF]
    rw [htA_eq, htB_eq]
    dsimp only [cfgExtra04]
    rw [show env0.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show env0.sp = sp from rfl,
      show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
      show sp + BitVec.ofNat 64 20704 = sp + 20704#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hr0 : env0.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runAndCheckKProg04 cfgExtra04_wf hr0 cert_stepsExtra04 hm0 hpc0 hrun0 ?_
  intro s1 envF stEnd hpc1 hrun1 hspF hrcF _hrlF heval hm1 hchk
  have hspec := specEnv_stepsExtra04_vars hrho (row := row) (extra := extra) (env0 := env0)
    (fun idx h => by simp [env0, mkSegEnv04, h])
    (fun idx h => by simp [env0, mkSegEnv04, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega])
    (fun idx h => by simp [env0, mkSegEnv04, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega])
  rcases hspec with ⟨hvLow, hv2000, hv2025, hv3000⟩
  simp only [checkExtraEnd04, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hchkG, hchkC⟩, hx11B⟩, hx9B⟩, hmemB⟩, hslots⟩
  have hevLow : ∀ id, id < 1500 → envF.vars id = env0.vars id := fun id hid => by
    have h := heval (.var id) (okExtra04_low hid)
    dsimp only [evalKExpr] at h
    exact h.trans (hvLow id (by omega))
  have hreg1 := extract_segRegInv04 (row := row) (eX8 := .var 101) hm1 hspF hrcF
    ((hevLow 100 (by decide)).trans rfl)
    ((hevLow 102 (by decide)).trans rfl) hchkG
  have hx8_1 : s1.readReg64 .x8 = BitVec.ofNat 64 (row + 1) := by
    rw [hreg1.2.1]; exact (hevLow 101 (by decide)).trans hx8_0
  have htA1 : Seg5ConstWordsInv sp rho (stEnd.memA.map (evalKExpr envF)) :=
    extract_constWords04 hspF
      ((hevLow 103 (by decide)).trans rfl)
      ((hevLow 104 (by decide)).trans rfl)
      ((hevLow 105 (by decide)).trans rfl)
      ((hevLow 106 (by decide)).trans rfl) hchkC
  have hx11_1 : s1.readReg64 (.gpr 11#5) = 0#64 :=
    eval_checked_gpr hm1 heval 11#5 (by decide) (.const64 0#64) hx11B rfl
  have hx9_1 : s1.readReg64 .x9 = sp + 20715#64 := by
    simpa [evalKExpr, specEnvSteps_sp, env0, mkSegEnv04] using
      eval_checked_gpr hm1 heval 9#5 (by decide) (.spAdd 20715#64) hx9B rfl
  let tA1 := stEnd.memA.map (evalKExpr envF)
  let tB1 := stEnd.memB.map (evalKExpr envF)
  have hs01_1 : ∀ idx, idx < 25 → slotHolds cfgClamp04 s1 tA1 (postExtra01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
      ((rowPermState rho row 1 (extra + 3)).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    have h := eval_checked_slot hm1 heval _ hs.1.1.1.1 (.var (2000 + idx)) (.var (2025 + idx))
      hs.1.1.1.2 hs.1.1.2 (okExtra04_lo 2000 (by decide) hidx) (okExtra04_hi 2000 (by decide) hidx)
    rwa [evalKExpr, evalKExpr, hv2000 idx hidx, hv2025 idx hidx] at h
  have hs2_1 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp04 s1 tA1 (postExtra2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 (extra + 3)).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    have h := eval_checked_slotLo hm1 heval _ hs.1.2 (.var (3000 + idx)) hs.2 (okExtra04_lo 3000 (by decide) hidx)
    rwa [evalKExpr, hv3000 idx hidx] at h
  have hbufs : ∀ col, col < 3 →
      wordsToBytes (btreeWords (21 * col) 21 tB1) = shake128BlockAt (rowSeeds rho row col) (extra + 3) := by
    intro col hcol; rw [← shake128BlockAt_rowSeeds_eq]
    rcases (show col = 0 ∨ col = 1 ∨ col = 2 by omega) with rfl | rfl | rfl
    · refine wordsToBytes_btreeWords_eq_extractRate_21 fun j hj => ?_
      have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB1, Nat.mul_zero, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval j (.var (2000 + j)) hm.1.1 (okExtra04_lo 2000 (by decide) (by omega))).trans (hv2000 j (by omega))
    · refine wordsToBytes_btreeWords_eq_extractRate_21 fun j hj => ?_
      have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact (eval_checked_memB heval (21 + j) (.var (2025 + j)) hm.1.2 (okExtra04_hi 2000 (by decide) (by omega))).trans (hv2025 j (by omega))
    · refine wordsToBytes_btreeWords_eq_extractRate_21 fun j hj => ?_
      have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact (eval_checked_memB heval (42 + j) (.var (3000 + j)) hm.2 (okExtra04_lo 3000 (by decide) (by omega))).trans (hv3000 j (by omega))
  dsimp only [KSpatial, cfgExtra04]
  apply sepWP_drop_left
  refine step_b_seg5 (w := 6979) (disp := 20#64) (Or.inr ⟨by decide, by decide⟩) (by decide +kernel) hpc1 hrun1 ?_
  have hpcM : (s1.setPC (b + BitVec.ofNat 64 (4 * 6979) + 20#64)).pc = b + offMidExtra04 :=
    setPC_disp_w_eq s1 b 6979 20#64 6984 (by decide +kernel)
  refine SepWP.done hpcM ((status_setPC _ _).trans hrun1) fun hc1 hr1 =>
    ⟨hpcM, (status_setPC _ _).trans hrun1, hc1, hr1, segRegInv04_setPC hreg1.1,
     readReg64_setPC hx8_1, readReg64_setPC hreg1.2.2, readReg64_setPC hx11_1, readReg64_setPC hx9_1,
     tA1, tB1, sampled, hws, htA1,
     fun idx h => slotHolds_setPC (hs01_1 idx h),
     fun idx h => by rcases hs2_1 idx h with ⟨vh, hh⟩; exact ⟨vh, slotHolds_setPC hh⟩,
     hbufs, hinv0, ?_⟩
  rw [show envF.sp = sp from hspF,
      show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
      show sp + BitVec.ofNat 64 20704 = sp + 20704#64 from rfl]
  dsimp only [FF]; sep_frame

private theorem seg5_row_bodyB_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row extra : Nat} {F : SepProp}
    {sm : State} {Pm : SepProp} (_hpc : sm.pc = b + offMidExtra04) (_hrun : sm.status = .Running)
    (hMid : Seg5MidState b sp fpVal rho row extra F sm Pm) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) (extra + 1) then b + offRowDone04 else b + offLoopHead04) sm Pm
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) (extra + 1) then Seg5RowDone b sp fpVal rho row F sf Pf
        else Seg5LoopState b sp fpVal rho row F (extra + 1) sf Pf) := by
  rcases hMid with ⟨hpcM, hrunM, hclM, hroM, hregM, hx8M, hx19M, hx11M, hx9M,
    tA, tB, sampled, hws, htA, hs01, hs2, hbufs, hinv, hPm⟩
  refine sepWP_mono_pre hPm ?_
  let pcBaseE := b + BitVec.ofNat 64 (4 * 6980)
  let bufsE : Nat → List (BitVec 8) := fun i => wordsToBytes (btreeWords (21 * i) 21 tB)
  have ⟨_, _, _, _, hr21, _, hr23, _, _, _, hr27, _⟩ := hregM
  refine sepWP_seq_env hclM hroM
    (mid := b + offClampExtra04)
    (post1 := fun sC PC =>
      Seg5RegInv sp fpVal sC ∧ sC.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
      sC.readReg64 .x19 = BitVec.ofNat 64 row ∧
      ∃ sampled' hws', MultiLaneRawXofInv 3 (rowSeeds rho row) (extra + 1) sampled' hws' ∧
        (∀ idx, idx < 25 → slotHolds cfgClamp04 sC tA (postExtra01Slots.getD idx (.vreg 0))
          ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
          ((rowPermState rho row 1 (extra + 3)).getD idx 0#64)) ∧
        (∀ idx, idx < 25 → slotHoldsLo cfgClamp04 sC tA (postExtra2Slots.getD idx (.vreg 0))
          ((rowPermState rho row 2 (extra + 3)).getD idx 0#64)) ∧
        (PC ⊢ TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
          MultiLaneSlots (sp + 5680#64) 544 3 hws' ∗ memRegion (sp + 20704#64) 504 ∗
          MultiLaneSampled (sp + 19168#64) 3 sampled' ∗ F)) ?_
    (fun sC PC hpcC hrunC hclC hroC ⟨hrC, hx8C, hx19C, sampled', hws', hraw, hs01C, hs2C, hPC⟩ =>
      sepWP_mono_pre hPC (seg5_row_clamp_extra1 hpcC hrunC hclC hroC hrC hx8C hx19C htA hraw hs01C hs2C))
  refine step_rej_site_extra1 (pcBase := pcBaseE) (sqBase := sp + 20704#64)
    (sampBase := sp + 19168#64) (slotsBase := sp + 5680#64) (cfg := cfgRejExtra1_04)
    (seeds := rowSeeds rho row) (bufs := bufsE) (extra := extra)
    (hpc := by
      dsimp only [pcAt, pcBaseE, cfgRejExtra1_04]; rw [hpcM]; dsimp only [offMidExtra04]
      rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
    hrunM cfgRejExtra1_04_valid rfl
    (fetchesInstrsAt_blk04_seg5 (by omega)
      (by rw [show (rejOuterInstrs cfgRejExtra1_04).length = 11 from rfl]; omega)
      (by dsimp only [pcBaseE]; rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
      cert_rejExtraO04)
    (fetchesInstrsAt_blk04_seg5 (by omega)
      (by rw [show (rejInnerInstrs cfgRejExtra1_04.v).length = 193 from rfl]; omega)
      (by dsimp only [pcBaseE]; rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
      cert_rejExtraI04)
    (fun i hi => by
      dsimp only [cfgRejExtra1_04] at hi ⊢
      exact rejBufReadable_of_treeMem (offWords := 21 * i)
        (by
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
          · simp
          · rw [BitVec.add_assoc]
          · rw [BitVec.add_assoc])
        (by omega) rfl)
    (fun i _ => by dsimp only [bufsE, cfgRejExtra1_04]; rw [wordsToBytes_length, btreeWords_length])
    (fun i hi => by
      dsimp only [cfgRejExtra1_04] at hi
      rw [List.take_of_length_le (by dsimp only [bufsE]; rw [wordsToBytes_length, btreeWords_length])]
      exact hbufs i hi)
    hinv.toRaw hx11M (by dsimp only [cfgRejExtra1_04]; rw [hx9M, BitVec.add_assoc]; rfl)
    hr23 hr21 hr27 ?_
  intro sF sampled' hws' hp hraw
  rcases segRegInv04_of_sitePreserved (pc := pcAt pcBaseE 204) hp
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    hregM hx8M hx19M with ⟨hregF, hx8F, hx19F⟩
  refine SepWP.done
    (by
      dsimp only [pcAt, pcBaseE, offClampExtra04]
      rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
    ((status_setPC _ _).trans hp.1)
    ⟨hregF, hx8F, hx19F, sampled', hws', hraw,
     fun idx h => slotHolds_of_sitePreserved hp (hs01 idx h),
     fun idx h => slotHoldsLo_of_sitePreserved hp (hs2 idx h),
     Entails.trans (sepConj_mono_left
       (by simpa using treeMem_entails_memRegion (ptr := sp + 20704#64) (len := 63) tB (by decide))) (by sep_frame)⟩

theorem seg5_row_safe_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} (htA : Seg5ConstWordsInv sp rho tA)
    {F : SepProp} {s0 : State}
    (hpc0 : s0.pc = b + offRowEntry04) (hrun0 : s0.status = .Running)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hreg0 : Seg5RegInv sp fpVal s0) (hx8_0 : s0.readReg64 .x8 = BitVec.ofNat 64 row) :
    SafeSepWP (blkPC04.rebase b (fun _ => none)) s0
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F)
      (Seg5RowDone b sp fpVal rho row F) :=
  sampleNttRow_safeSepWP (N := 3) (seeds := rowSeeds rho row)
    (loopHead := b + offLoopHead04) (midPC := b + offMidExtra04) (exitPC := b + offRowDone04)
    (Inv := Seg5LoopState b sp fpVal rho row F)
    (Mid := fun extra => Seg5MidState b sp fpVal rho row extra F)
    (by unfold offLoopHead04 offMidExtra04; bv_omega)
    (fun _ _ _ hInv => hInv.1)
    (seg5_row_init_wp hb hbase hrho hrow htA hpc0 hrun0 hcl0 hro0 hreg0 hx8_0)
    (fun _ _ _ hInv => seg5_row_bodyA_wp hrho hInv)
    (fun _ _ _ hpc hrun hMid => seg5_row_bodyB_wp hpc hrun hMid)

theorem seg5_row_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    (hTerm : ∀ col, col < 3 → Shake128SeedTerminates (rowSeeds rho row col))
    {tA : BTree (BitVec 64) 9} (htA : Seg5ConstWordsInv sp rho tA)
    {F : SepProp} {s0 : State}
    (hpc0 : s0.pc = b + offRowEntry04) (hrun0 : s0.status = .Running)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hreg0 : Seg5RegInv sp fpVal s0) (hx8_0 : s0.readReg64 .x8 = BitVec.ofNat 64 row) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offRowDone04) s0
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F)
      (Seg5RowDone b sp fpVal rho row F) :=
  sampleNttRow_sepWP hTerm
    (seg5_row_init_wp hb hbase hrho hrow htA hpc0 hrun0 hcl0 hro0 hreg0 hx8_0)
    (fun _ _ _ hInv => seg5_row_bodyA_wp hrho hInv)
    (fun _ _ _ hpc hrun hMid => seg5_row_bodyB_wp hpc hrun hMid)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop
