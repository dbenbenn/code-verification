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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp

/-!
# `decapsulate_compressed_key` (`B04`) — `Seg5` Initial 3-Block `SampleNTT` (`Seg5RowInit`)

Proves `seg5_row_clamp_init3` (`+0x6370 → +0x40d8 / +0x63d8`), `SitePreserved` transfers,
`specEnv_stepsInit04_vars`, and `seg5_row_init_wp` (`+0x436c → +0x40d8 / +0x63d8`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowInit

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakF1600 shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneClampedInv MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone step_rej_site_init3)
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
  btreeWords_split rejBufReadable_of_treeMem wordsToBytes_append
  wordsToBytes_btreeWords_eq_extractRate_21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memB eval_checked_pstate
  eval_checked_slot exprVarsOk extendLoopVars progBases rhoW rowPermState
  rowPermState_succ rowSeeds shake128FirstBlocks_rowSeeds_three specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  condCC_256_of_le271 condCS_256_of_le271 condHI_255_of_le271 keccakRc_intro
  raw_sampled_le271 rowPermState_size slotHoldsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  eq_some_getD sepWP_drop_left)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit (
  checkPStateEq checkPreAbsorb evalExprList25_varRange expVarRange pc_add_eq pc_of_eq
  preAbsorb_eq_of_check setPC_disp_w_eq setPC_fall_w_eq slotHoldsLo_of_sitePreserved
  slotHolds_of_sitePreserved status_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row (
  eval_checked_slotLo not_mem_of_dec readReg64_setPC sepWP_mono_pre slotHolds_setPC
  specEnvSteps_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  buildPostLoopState04 checkInstrsAt04 fetchesInstrsAt_blk04_seg5 mkLoopInitState04
  preClamp01Slots preClamp2Slots runKRange04 sepWP_of_runKRange04
  slotsA1 slotsA2 slotsA3 slotsB1 slotsB2 slotsB3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init (
  Seg5ConstWordsInv Seg5LoopState Seg5RegInv Seg5RowDone cfgClamp04 cfgClamp04_wf cfgInit04
  cfgInit04_wf cfgRejInit3_04 cfgRejInit3_04_valid multiLaneSampled3_eq_treeMem04
  seg5_row_memset step_bCond_seg5 step_b_seg5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp (
  checkClampEnd04 checkConstWordsMemA04 checkSegRegGprs04 extract_constWords04
  extract_segRegInv04 finish_clamp_branch04 mkSegEnv04 mkSegState04 mkSegState04_matches
  runAndCheckKProg04 sepWP_of_runAndCheckKProg04 with_frozen_env04)

attribute [local irreducible] keccakF1600 blkPC04

/-! ## 1. `+0x6370 → +0x40d8 / +0x63d8` Clamp Dispatch & `SitePreserved` Transfers -/

private def stInitClamp0_04 : KState := mkSegState04 cfgClamp04 true preClamp01Slots preClamp2Slots
private def stInitC1_04 : KState := (runKRange04 cfgClamp04 6364 17 stInitClamp0_04).getD stInitClamp0_04
private def stInitCLo_04 : KState := (runKRange04 cfgClamp04 6386 1 stInitC1_04).getD stInitC1_04
private def stInitCHi_04 : KState := (runKRange04 cfgClamp04 6382 2 stInitC1_04).getD stInitC1_04
private def stInitCEnd_04 : KState := (runKRange04 cfgClamp04 6388 1 stInitCHi_04).getD stInitCHi_04

private theorem cert_initC1_04 : runKRange04 cfgClamp04 6364 17 stInitClamp0_04 = some stInitC1_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 6364 17 stInitClamp0_04) stInitClamp0_04 (by decide +kernel)
private theorem cert_initCLo_04 : runKRange04 cfgClamp04 6386 1 stInitC1_04 = some stInitCLo_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 6386 1 stInitC1_04) stInitC1_04 (by decide +kernel)
private theorem cert_initCHi_04 : runKRange04 cfgClamp04 6382 2 stInitC1_04 = some stInitCHi_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 6382 2 stInitC1_04) stInitC1_04 (by decide +kernel)
private theorem cert_initCEnd_04 : runKRange04 cfgClamp04 6388 1 stInitCHi_04 = some stInitCEnd_04 :=
  eq_some_getD (o := runKRange04 cfgClamp04 6388 1 stInitCHi_04) stInitCHi_04 (by decide +kernel)

private theorem cert_pstateC1_04 : checkPStateEq stInitC1_04 (.var 902) (.const64 256#64) = true := by decide +kernel
private theorem cert_pstateCHi_04 : checkPStateEq stInitCHi_04 (.var 901) (.const64 256#64) = true := by decide +kernel
private theorem cert_pstateCEnd_04 : checkPStateEq stInitCEnd_04 (.var 900) (.const64 255#64) = true := by decide +kernel
private theorem cert_chkCLo_04 : checkClampEnd04 stInitCLo_04 (!false) = true := by decide +kernel
private theorem cert_chkCHi_04 : checkClampEnd04 stInitCHi_04 (!false) = true := by decide +kernel
private theorem cert_chkCEndT_04 : checkClampEnd04 stInitCEnd_04 (!true) = true := by decide +kernel
private theorem cert_chkCEndF_04 : checkClampEnd04 stInitCEnd_04 (!false) = true := by decide +kernel

attribute [local irreducible] stInitC1_04 stInitCLo_04 stInitCHi_04 stInitCEnd_04

theorem seg5_row_clamp_init3 [MlKemPlacement] {b sp fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row : Nat} {F : SepProp} {tA : BTree (BitVec 64) 9}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {s : State}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 6364)) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg5RegInv sp fpVal s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row)
    (htA : Seg5ConstWordsInv sp rho tA)
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) 0 sampled hws)
    (hs01 : ∀ idx, idx < 25 → slotHolds cfgClamp04 s tA (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64))
    (hs2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp04 s tA (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0
       then b + BitVec.ofNat 64 (4 * 4150) else b + BitVec.ofNat 64 (4 * 6390)) s
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗
        MultiLaneSampled (sp + 19168#64) 3 sampled ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg5RowDone b sp fpVal rho row F sf Pf
        else Seg5LoopState b sp fpVal rho row F 0 sf Pf) := by
  let tB : BTree (BitVec 64) 9 := BTree.ofFn 9 fun i =>
    if i < 3 then BitVec.ofNat 64 (sampled i) else 0#64
  have htB : ∀ i, i < 3 → tB.get i = BitVec.ofNat 64 (sampled i) := fun i hi => by
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi]
  let k2Hi : Nat → BitVec 64 := fun idx =>
    if h : idx < 25 then Classical.choose (hs2 idx h) else 0#64
  let env := mkSegEnv04 sp fpVal row rho (rowPermState rho row 0 2) (rowPermState rho row 1 2)
    (rowPermState rho row 2 2) k2Hi s tA tB
  rcases mkSegState04_matches (cfg := cfgClamp04) (hasConsts := true)
    (slots01 := preClamp01Slots) (slots2 := preClamp2Slots)
    (k0 := rowPermState rho row 0 2) (k1 := rowPermState rho row 1 2)
    (k2 := rowPermState rho row 2 2) (k2Hi := k2Hi) (tA := tA) (tB := tB)
    (by decide) (by decide) hreg hx19 (fun _ => htA)
    (fun i hi => hs01 i (by simpa [preClamp01Slots] using hi))
    (fun i hi => by
      have hi25 : i < 25 := by simpa [preClamp2Slots] using hi
      simpa [k2Hi, hi25] using Classical.choose_spec (hs2 i hi25)) with ⟨hm0, htA_eq, htB_eq⟩
  apply with_frozen_env04 hcl hro
  apply keccakRc_intro hro
  let FF := memRegion (sp + 22400#64) 1512 ∗
    MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgClamp04 env stInitClamp0_04 FF) ?_ ?_
  · dsimp only [KSpatial, stInitClamp0_04, FF]
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
  have hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, h]
  have hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv04, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  have hr0 : env.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 6364) (count := 17)
    (st := stInitClamp0_04) (st' := stInitC1_04) (s := s)
    (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_initC1_04 hpc hrun hm0 ?_
  intro s1 hpc1 hrun1 hm1
  have hp1 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm1
    (fun _ _ => rfl) (.var 902) (.const64 256#64) cert_pstateC1_04 rfl rfl
  refine step_bCond_seg5 (w := 6381) (cond := .CC) (disp := 20#64)
    (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
    (pc_add_eq hpc1 (by decide +kernel)) hrun1 ?_ ?_
  · intro hcc
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcc
    have hs2lt : sampled 2 < 256 := of_decide_eq_true hcc
    have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
      Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 2 (by decide)) (by omega)
    refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 6386) (count := 1)
      (st := stInitC1_04) (st' := stInitCLo_04) (s := s1.setPC (b + BitVec.ofNat 64 (4 * 6381) + 20#64))
      (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_initCLo_04
      (setPC_disp_w_eq s1 b 6381 20#64 6386 (by decide +kernel)) ((status_setPC _ _).trans hrun1) (matches_setPC hm1 _) ?_
    intro s2 hpc2 hrun2 hm2
    refine step_b_seg5 (w := 6387) (disp := 12#64) (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_
    exact finish_clamp_branch04 hraw (matches_setPC hm2 _) rfl rfl
      (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
      (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
      (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
      hv0 hv1 hv2 hb0 hb1 hb2 false hdone
      (setPC_disp_w_eq s2 b 6387 12#64 6390 (by decide +kernel)) ((status_setPC _ _).trans hrun2) cert_chkCLo_04
  · intro hccF
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hccF
    have hs2ge : 256 ≤ sampled 2 := by have := of_decide_eq_false hccF; omega
    refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 6382) (count := 2)
      (st := stInitC1_04) (st' := stInitCHi_04) (s := s1.setPC (b + BitVec.ofNat 64 (4 * (6381 + 1))))
      (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_initCHi_04
      (setPC_fall_w_eq s1 b 6381 6382 (by decide +kernel)) ((status_setPC _ _).trans hrun1) (matches_setPC hm1 _) ?_
    intro s2 hpc2 hrun2 hm2
    have hp2 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm2
      (fun _ _ => rfl) (.var 901) (.const64 256#64) cert_pstateCHi_04 rfl rfl
    refine step_bCond_seg5 (w := 6384) (cond := .CS) (disp := 16#64)
      (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_ ?_
    · intro hcs
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcs
      have hs1ge : 256 ≤ sampled 1 := of_decide_eq_true hcs
      refine sepWP_of_runKRange04 cfgClamp04_wf hr0 (w := 6388) (count := 1)
        (st := stInitCHi_04) (st' := stInitCEnd_04) (s := s2.setPC (b + BitVec.ofNat 64 (4 * 6384) + 16#64))
        (fun k hk => Or.inr ⟨by omega, by omega⟩) cert_initCEnd_04
        (setPC_disp_w_eq s2 b 6384 16#64 6388 (by decide +kernel)) ((status_setPC _ _).trans hrun2) (matches_setPC hm2 _) ?_
      intro s3 hpc3 hrun3 hm3
      have hp3 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm3
        (fun _ _ => rfl) (.var 900) (.const64 255#64) cert_pstateCEnd_04 rfl rfl
      refine step_bCond_seg5 (w := 6389) (cond := .HI) (disp := BitVec.ofInt 64 (-8956))
        (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
        (pc_add_eq hpc3 (by decide +kernel)) hrun3 ?_ ?_
      · intro hhi
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhi
        have hs0ge : 256 ≤ sampled 0 := of_decide_eq_true hhi
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = true :=
          hraw.allLanesDone_iff_ge256.mpr fun i hi => by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption
        exact finish_clamp_branch04 hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          hv0 hv1 hv2 hb0 hb1 hb2 true hdone
          (setPC_disp_w_eq s3 b 6389 (BitVec.ofInt 64 (-8956)) 4150 (by decide +kernel))
          ((status_setPC _ _).trans hrun3) cert_chkCEndT_04
      · intro hhiF
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhiF
        have hs0lt : sampled 0 < 256 := by have := of_decide_eq_false hhiF; omega
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
          Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 0 (by decide)) (by omega)
        exact finish_clamp_branch04 hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
          hv0 hv1 hv2 hb0 hb1 hb2 false hdone
          (setPC_fall_w_eq s3 b 6389 6390 (by decide +kernel)) ((status_setPC _ _).trans hrun3) cert_chkCEndF_04
    · intro hcsF
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcsF
      have hs1lt : sampled 1 < 256 := by have := of_decide_eq_false hcsF; omega
      have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
        Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 1 (by decide)) (by omega)
      refine step_b_seg5 (w := 6385) (disp := 20#64) (Or.inr ⟨by decide, by decide⟩) (by decide +kernel)
        (setPC_fall_w_eq s2 b 6384 6385 (by decide +kernel)) ((status_setPC _ _).trans hrun2) ?_
      exact finish_clamp_branch04 hraw (matches_setPC (matches_setPC hm2 _) _) rfl rfl
        (by simp [env, mkSegEnv04]) (by simpa [env, mkSegEnv04] using hx8) (by simp [env, mkSegEnv04])
        (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
        (by simp [env, mkSegEnv04]) (by simp [env, mkSegEnv04])
        hv0 hv1 hv2 hb0 hb1 hb2 false hdone
        (setPC_disp_w_eq (s2.setPC _) b 6385 20#64 6390 (by decide +kernel))
        ((status_setPC _ _).trans ((status_setPC _ _).trans hrun2)) cert_chkCHi_04

theorem segRegInv04_setPC [MlKemPlacement] {sp fpVal pc : BitVec 64} {s : State}
    (h : Seg5RegInv sp fpVal s) : Seg5RegInv sp fpVal (s.setPC pc) := by
  rcases h with ⟨hsp, hal, r29, r20, r21, r22, r23, r24, r25, r26, r27, r28⟩
  exact ⟨hsp, hal, readReg64_setPC r29, readReg64_setPC r20, readReg64_setPC r21,
    readReg64_setPC r22, readReg64_setPC r23, readReg64_setPC r24, readReg64_setPC r25,
    readReg64_setPC r26, readReg64_setPC r27, readReg64_setPC r28⟩

theorem segRegInv04_of_sitePreserved [MlKemPlacement] {cfgS : RejSiteConfig}
    {sp fpVal pc : BitVec 64} {row : Nat} {s0 sF : State}
    (hp : SitePreserved cfgS s0 sF)
    (hn8 : Reg.x8 ∉ cfgS.siteClobberedRegs) (hn29 : Reg.fp ∉ cfgS.siteClobberedRegs)
    (hn19 : Reg.x19 ∉ cfgS.siteClobberedRegs) (hn20 : Reg.x20 ∉ cfgS.siteClobberedRegs)
    (hn21 : Reg.x21 ∉ cfgS.siteClobberedRegs) (hn22 : Reg.x22 ∉ cfgS.siteClobberedRegs)
    (hn23 : Reg.x23 ∉ cfgS.siteClobberedRegs) (hn24 : Reg.x24 ∉ cfgS.siteClobberedRegs)
    (hn25 : Reg.x25 ∉ cfgS.siteClobberedRegs) (hn26 : Reg.x26 ∉ cfgS.siteClobberedRegs)
    (hn27 : Reg.x27 ∉ cfgS.siteClobberedRegs) (hn28 : Reg.x28 ∉ cfgS.siteClobberedRegs)
    (hreg : Seg5RegInv sp fpVal s0) (hx8 : s0.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx19 : s0.readReg64 .x19 = BitVec.ofNat 64 row) :
    Seg5RegInv sp fpVal (sF.setPC pc) ∧
      (sF.setPC pc).readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
      (sF.setPC pc).readReg64 .x19 = BitVec.ofNat 64 row := by
  rcases hreg with ⟨hsp, hspA, r29, r20, r21, r22, r23, r24, r25, r26, r27, r28⟩
  have hspF : (sF.setPC pc).sp = sp := hp.2.1.trans hsp
  have hspAF : (sF.setPC pc).spAligned = true := by
    unfold State.spAligned at hspA ⊢; rwa [hspF, ← hsp]
  exact ⟨⟨hspF, hspAF, (hp.2.2.2 _ hn29).trans r29, (hp.2.2.2 _ hn20).trans r20,
    (hp.2.2.2 _ hn21).trans r21, (hp.2.2.2 _ hn22).trans r22, (hp.2.2.2 _ hn23).trans r23,
    (hp.2.2.2 _ hn24).trans r24, (hp.2.2.2 _ hn25).trans r25, (hp.2.2.2 _ hn26).trans r26,
    (hp.2.2.2 _ hn27).trans r27, (hp.2.2.2 _ hn28).trans r28⟩,
    (hp.2.2.2 _ hn8).trans hx8, (hp.2.2.2 _ hn19).trans hx19⟩

/-! ## 2. 6-Permutation `A1..A3, B1..B3` Symbolic Program (`+0x4390 → +0x603c`) -/

private def stInit0_04 : KState := mkSegState04 cfgInit04 true [] []
private def stAt4359_04 : KState := (runKRange04 cfgInit04 4324 35 stInit0_04).getD stInit0_04
private def expA1Lo04 : List KExpr := slotsA1.map fun sl => (readSlot cfgInit04 stAt4359_04 sl).1
private def expA1Hi04 : List KExpr := slotsA1.map fun sl => (readSlot cfgInit04 stAt4359_04 sl).2
private def stBodyA1_04 : KState :=
  (runKRange04 cfgInit04 4359 197 (mkLoopInitState04 cfgInit04 8#5 slotsA1)).getD stAt4359_04
private def stPostA1_04 : KState := buildPostLoopState04 2000 8#5 stAt4359_04 stBodyA1_04
private def stAt4604_04 : KState := (runKRange04 cfgInit04 4557 47 stPostA1_04).getD stPostA1_04
private def expA2Lo04 : List KExpr := slotsA2.map fun sl => (readSlot cfgInit04 stAt4604_04 sl).1
private def expA2Hi04 : List KExpr := slotsA2.map fun sl => (readSlot cfgInit04 stAt4604_04 sl).2

private theorem cert_preA1Lo04 : checkPreAbsorb expA1Lo04 0 = true := by decide +kernel
private theorem cert_preA1Hi04 : checkPreAbsorb expA1Hi04 1 = true := by decide +kernel
private theorem cert_preA2Lo04 : checkPreAbsorb expA2Lo04 2 = true := by decide +kernel
private theorem cert_preA2Hi04 : checkPreAbsorb expA2Hi04 2 = true := by decide +kernel

private def stepsInit04 : List KProgStep :=
  [.range 4324 35,
   .loop 4359 197 8#5 slotsA1 expA1Lo04 expA1Hi04 2000,
   .range 4557 47,
   .loop 4604 197 8#5 slotsA2 expA2Lo04 expA2Hi04 3000,
   .range 4802 49,
   .loop 4851 201 8#5 slotsA3 (expVarRange 2000) (expVarRange 2025) 4000,
   .range 5053 30,
   .loop 5083 200 8#5 slotsB1 (expVarRange 4000) (expVarRange 4025) 5000,
   .range 5284 44,
   .loop 5328 201 8#5 slotsB2 (expVarRange 3000) (expVarRange 3025) 6000,
   .range 5530 40,
   .loop 5570 207 8#5 slotsB3 (expVarRange 6000) (expVarRange 6025) 7000,
   .range 5778 381]

private def checkCol2Var (base j : Nat) (e : KExpr) : Bool :=
  e.beq (.var (base + j)) || e.beq (.var (base + 25 + j))

private def checkInitEnd04 (st : KState) : Bool :=
  checkSegRegGprs04 st (.add64 (.var 100) (.const64 1#64)) &&
  checkConstWordsMemA04 st &&
  (st.gprs.get 9).beq (.const64 0#64) &&
  (st.gprs.get 10).beq (.spAdd 22411#64) &&
  ((List.range 21).all fun j =>
    (st.memB.get j).beq (.var (2000 + j)) &&
    (st.memB.get (21 + j)).beq (.var (4000 + j)) &&
    (st.memB.get (42 + j)).beq (.var (5000 + j)) &&
    (st.memB.get (63 + j)).beq (.var (2025 + j)) &&
    (st.memB.get (84 + j)).beq (.var (4025 + j)) &&
    (st.memB.get (105 + j)).beq (.var (5025 + j)) &&
    checkCol2Var 3000 j (st.memB.get (126 + j)) &&
    checkCol2Var 6000 j (st.memB.get (147 + j)) &&
    checkCol2Var 7000 j (st.memB.get (168 + j))) &&
  ((List.range 25).all fun idx =>
    let sl01 := preClamp01Slots.getD idx (.vreg 0)
    let sl2 := preClamp2Slots.getD idx (.vreg 0)
    slotValid cfgClamp04 sl01 &&
      (readSlot cfgClamp04 st sl01).1.beq (.var (5000 + idx)) &&
      (readSlot cfgClamp04 st sl01).2.beq (.var (5025 + idx)) &&
      slotValid cfgClamp04 sl2 &&
      checkCol2Var 7000 idx (readSlot cfgClamp04 st sl2).1)

private theorem cert_stepsInit04 :
    runAndCheckKProg04 cfgInit04 4324 6160 4324 6159 1500 stepsInit04 stInit0_04
      (fun _ st => checkInitEnd04 st) = true := by decide +kernel

attribute [local irreducible] expA1Lo04 expA1Hi04 expA2Lo04 expA2Hi04

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

private theorem specEnv_stepsInit04_vars {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row : Nat} (hrow : row < 3) {env0 : KEnv}
    (hv100 : env0.vars 100 = BitVec.ofNat 64 row)
    (hvRho : ∀ k, k < 4 → env0.vars (103 + k) = rhoW rho k) :
    let envS := specEnvSteps env0 stepsInit04
    envS.vars 100 = BitVec.ofNat 64 row ∧
    envS.vars 102 = env0.vars 102 ∧
    (∀ k, k < 4 → envS.vars (103 + k) = rhoW rho k) ∧
    (∀ idx, idx < 25 → envS.vars (2000 + idx) = (rowPermState rho row 0 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (2025 + idx) = (rowPermState rho row 1 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3000 + idx) = (rowPermState rho row 2 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3025 + idx) = (rowPermState rho row 2 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4000 + idx) = (rowPermState rho row 0 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4025 + idx) = (rowPermState rho row 1 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5000 + idx) = (rowPermState rho row 0 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5025 + idx) = (rowPermState rho row 1 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (6000 + idx) = (rowPermState rho row 2 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (6025 + idx) = (rowPermState rho row 2 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (7000 + idx) = (rowPermState rho row 2 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (7025 + idx) = (rowPermState rho row 2 2).getD idx 0#64) := by
  dsimp only [stepsInit04, specEnvSteps]
  set e1 := extendLoopVars env0 2000 (evalExprList25 env0 expA1Lo04) (evalExprList25 env0 expA1Hi04) with he1
  set e2 := extendLoopVars e1 3000 (evalExprList25 e1 expA2Lo04) (evalExprList25 e1 expA2Hi04) with he2
  set e3 := extendLoopVars e2 4000 (evalExprList25 e2 (expVarRange 2000)) (evalExprList25 e2 (expVarRange 2025)) with he3
  set e4 := extendLoopVars e3 5000 (evalExprList25 e3 (expVarRange 4000)) (evalExprList25 e3 (expVarRange 4025)) with he4
  set e5 := extendLoopVars e4 6000 (evalExprList25 e4 (expVarRange 3000)) (evalExprList25 e4 (expVarRange 3025)) with he5
  set e6 := extendLoopVars e5 7000 (evalExprList25 e5 (expVarRange 6000)) (evalExprList25 e5 (expVarRange 6025)) with he6
  have hp10 : keccakF1600 (evalExprList25 env0 expA1Lo04) = rowPermState rho row 0 0 :=
    preAbsorb_eq_of_check hrho hrow hv100 hvRho cert_preA1Lo04
  have hp11 : keccakF1600 (evalExprList25 env0 expA1Hi04) = rowPermState rho row 1 0 :=
    preAbsorb_eq_of_check hrho hrow hv100 hvRho cert_preA1Hi04
  have hp20 : keccakF1600 (evalExprList25 e1 expA2Lo04) = rowPermState rho row 2 0 :=
    preAbsorb_eq_of_check hrho hrow (by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hv100])
      (fun k hk => by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hvRho k hk]) cert_preA2Lo04
  have hp21 : keccakF1600 (evalExprList25 e1 expA2Hi04) = rowPermState rho row 2 0 :=
    preAbsorb_eq_of_check hrho hrow (by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hv100])
      (fun k hk => by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hvRho k hk]) cert_preA2Hi04
  have hp30 : keccakF1600 (evalExprList25 e2 (expVarRange 2000)) = rowPermState rho row 0 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 0) fun idx h => by
      rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lo _ _ _ _ h, hp10], rowPermState_succ]
  have hp31 : keccakF1600 (evalExprList25 e2 (expVarRange 2025)) = rowPermState rho row 1 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 0) fun idx h => by
      rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_hi _ _ _ _ h, hp11], rowPermState_succ]
  have hp40 : keccakF1600 (evalExprList25 e3 (expVarRange 4000)) = rowPermState rho row 0 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 1) fun idx h => by
      rw [he3, extendLoopVars_lo _ _ _ _ h, hp30], rowPermState_succ]
  have hp41 : keccakF1600 (evalExprList25 e3 (expVarRange 4025)) = rowPermState rho row 1 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 1) fun idx h => by
      rw [he3, extendLoopVars_hi _ _ _ _ h, hp31], rowPermState_succ]
  have hp50 : keccakF1600 (evalExprList25 e4 (expVarRange 3000)) = rowPermState rho row 2 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 0) fun idx h => by
      rw [he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
        he2, extendLoopVars_lo _ _ _ _ h, hp20], rowPermState_succ]
  have hp51 : keccakF1600 (evalExprList25 e4 (expVarRange 3025)) = rowPermState rho row 2 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 0) fun idx h => by
      rw [he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
        he2, extendLoopVars_hi _ _ _ _ h, hp21], rowPermState_succ]
  have hp60 : keccakF1600 (evalExprList25 e5 (expVarRange 6000)) = rowPermState rho row 2 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 1) fun idx h => by
      rw [he5, extendLoopVars_lo _ _ _ _ h, hp50], rowPermState_succ]
  have hp61 : keccakF1600 (evalExprList25 e5 (expVarRange 6025)) = rowPermState rho row 2 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 1) fun idx h => by
      rw [he5, extendLoopVars_hi _ _ _ _ h, hp51], rowPermState_succ]
  have hlt : ∀ id, id < 2000 → e6.vars id = env0.vars id := fun id h => by
    rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lt _ _ _ _ h]
  refine ⟨by rw [hlt 100 (by omega), hv100], hlt 102 (by omega),
    fun k hk => by rw [hlt _ (by omega), hvRho k hk],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lo _ _ _ _ h, hp10],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_hi _ _ _ _ h, hp11],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lo _ _ _ _ h, hp20],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_hi _ _ _ _ h, hp21],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lo _ _ _ _ h, hp30],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_hi _ _ _ _ h, hp31],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lo _ _ _ _ h, hp40],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_hi _ _ _ _ h, hp41],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lo _ _ _ _ h, hp50],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_hi _ _ _ _ h, hp51],
    fun idx h => by rw [he6, extendLoopVars_lo _ _ _ _ h, hp60],
    fun idx h => by rw [he6, extendLoopVars_hi _ _ _ _ h, hp61]⟩

/-! ## 3. `+0x436c → +0x40d8 / +0x63d8` Initial 3-Block Absorb, Squeeze & `rej_sample` (`seg5_row_init_wp`) -/

private theorem cert_rejInitO04 : checkInstrsAt04 6160 (rejOuterInstrs cfgRejInit3_04) = true := by decide +kernel
private theorem cert_rejInitI04 : checkInstrsAt04 6171 (rejInnerInstrs .varA) = true := by decide +kernel

private theorem eval_col2_memB {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    {base j off : Nat} {v : BitVec 64}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hchk : checkCol2Var base j (stEnd.memB.get off) = true)
    (hokLo : ok (base + j) = true) (hokHi : ok (base + 25 + j) = true)
    (hvLo : envSpec.vars (base + j) = v) (hvHi : envSpec.vars (base + 25 + j) = v) :
    (stEnd.memB.map (evalKExpr envFinal)).get off = v := by
  simp only [checkCol2Var, Bool.or_eq_true] at hchk
  rcases hchk with h | h
  · simpa [evalKExpr, hvLo] using eval_checked_memB heval off (.var (base + j)) h hokLo
  · simpa [evalKExpr, hvHi] using eval_checked_memB heval off (.var (base + 25 + j)) h hokHi

private theorem eval_col2_slotLo {cfg : KCfg} {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State} {base idx : Nat} {sl : KSlot} {v : BitVec 64}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hsl : slotValid cfg sl = true)
    (hchk : checkCol2Var base idx (readSlot cfg stEnd sl).1 = true)
    (hokLo : ok (base + idx) = true) (hokHi : ok (base + 25 + idx) = true)
    (hvLo : envSpec.vars (base + idx) = v) (hvHi : envSpec.vars (base + 25 + idx) = v) :
    slotHoldsLo cfg sf (stEnd.memA.map (evalKExpr envFinal)) sl v := by
  simp only [checkCol2Var, Bool.or_eq_true] at hchk
  rcases hchk with h | h
  · simpa [evalKExpr, hvLo] using eval_checked_slotLo hm heval sl hsl (.var (base + idx)) h hokLo
  · simpa [evalKExpr, hvHi] using eval_checked_slotLo hm heval sl hsl (.var (base + 25 + idx)) h hokHi

private theorem btreeWords63_bytes_eq_firstBlocks3 {rho : List (BitVec 8)} {row col start : Nat}
    {tB : BTree (BitVec 64) 9}
    (h0 : ∀ j, j < 21 → tB.get (start + j) = (rowPermState rho row col 0).getD j 0#64)
    (h1 : ∀ j, j < 21 → tB.get (start + 21 + j) = (rowPermState rho row col 1).getD j 0#64)
    (h2 : ∀ j, j < 21 → tB.get (start + 42 + j) = (rowPermState rho row col 2).getD j 0#64) :
    wordsToBytes (btreeWords start 63 tB) = shake128FirstBlocks (rowSeeds rho row col) 3 := by
  rw [show (63 : Nat) = 21 + (21 + 21) from rfl,
    btreeWords_split start 21 (21 + 21) tB, btreeWords_split (start + 21) 21 21 tB,
    wordsToBytes_append, wordsToBytes_append,
    wordsToBytes_btreeWords_eq_extractRate_21 h0,
    wordsToBytes_btreeWords_eq_extractRate_21 (fun j hj => by simpa [Nat.add_assoc] using h1 j hj),
    wordsToBytes_btreeWords_eq_extractRate_21 (fun j hj => by
      simpa [show start + 21 + 21 + j = start + 42 + j by omega] using h2 j hj),
    shake128FirstBlocks_rowSeeds_three]

private theorem okInit04_all :
    ([2000, 3000, 4000, 5000, 6000, 7000].all fun b =>
      (List.range 25).all fun i =>
        validSpecVar 1500 (progBases stepsInit04) (b + i) &&
        validSpecVar 1500 (progBases stepsInit04) (b + 25 + i)) = true := by decide +kernel

private theorem okInit04_lo (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000, 4000, 5000, 6000, 7000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsInit04) (b + i) = true := by
  have h1 := (List.all_eq_true.mp okInit04_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).1

private theorem okInit04_hi (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000, 4000, 5000, 6000, 7000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsInit04) (b + 25 + i) = true := by
  have h1 := (List.all_eq_true.mp okInit04_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).2

private theorem okInit04_low {id : Nat} (h : id < 1500) :
    validSpecVar 1500 (progBases stepsInit04) id = true := by
  simp [validSpecVar, Nat.blt_eq, h]

attribute [local irreducible] validSpecVar progBases specEnvSteps extendLoopVars
  TreeMem MultiLaneSlots MultiLaneSampled

private def Seg5InitPreClampPost [MlKemPlacement] (sp fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (F : SepProp) (sF : State) (PF : SepProp) : Prop :=
  Seg5RegInv sp fpVal sF ∧ sF.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
  sF.readReg64 .x19 = BitVec.ofNat 64 row ∧
  ∃ tA2 sampled' hws', Seg5ConstWordsInv sp rho tA2 ∧
    MultiLaneRawXofInv 3 (rowSeeds rho row) 0 sampled' hws' ∧
    (∀ idx, idx < 25 → slotHolds cfgClamp04 sF tA2 (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHoldsLo cfgClamp04 sF tA2 (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64)) ∧
    (PF ⊢ TreeMem (sp + 144#64) 264 tA2 ∗ memRegion (sp + 22400#64) 1512 ∗
      MultiLaneSlots (sp + 5680#64) 544 3 hws' ∗ memRegion (sp + 20704#64) 504 ∗
      MultiLaneSampled (sp + 19168#64) 3 sampled' ∗ F)

private theorem step_init_rej04 [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} {F : SepProp}
    {s2 : State} {envF : KEnv} {stEnd : KState}
    (hpc2 : s2.pc = b + BitVec.ofNat 64 (4 * 6159)) (hrun2 : s2.status = .Running)
    (hspEq : envF.sp = sp)
    (hreg2 : Seg5RegInv sp fpVal s2 ∧
      (s2.readReg64 .x8 = evalKExpr envF (.add64 (.var 100) (.const64 1#64)) ∧
       s2.readReg64 .x19 = BitVec.ofNat 64 row))
    (hx8_2 : s2.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (htA2 : Seg5ConstWordsInv sp rho (stEnd.memA.map (evalKExpr envF)))
    (hx9_2 : s2.readReg64 (.gpr 9#5) = 0#64)
    (hx10_2 : s2.readReg64 .x10 = sp + 22411#64)
    (hs01_2 : ∀ idx, idx < 25 → slotHolds cfgClamp04 s2 (stEnd.memA.map (evalKExpr envF))
      (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64))
    (hs2_2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp04 s2 (stEnd.memA.map (evalKExpr envF))
      (preClamp2Slots.getD idx (.vreg 0)) ((rowPermState rho row 2 2).getD idx 0#64))
    (hbuf0 : wordsToBytes (btreeWords 0 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 0) 3)
    (hbuf1 : wordsToBytes (btreeWords 63 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 1) 3)
    (hbuf2 : wordsToBytes (btreeWords 126 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 2) 3) :
    let FF := MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 20704#64) 504 ∗ MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗ F
    SepWP (blkPC04.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 6364)) s2
      (KSpatial cfgInit04 envF stEnd FF)
      (Seg5InitPreClampPost sp fpVal rho row F) := by
  intro FF
  let tA2 := stEnd.memA.map (evalKExpr envF)
  let tB2 := stEnd.memB.map (evalKExpr envF)
  dsimp only [KSpatial, cfgInit04]
  apply sepWP_drop_left
  refine sepWP_mono_pre (Q := TreeMem (sp + 22400#64) 189 tB2 ∗
      (MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗
        (MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          (TreeMem (sp + 144#64) 264 tA2 ∗ memRegion (sp + 20704#64) 504 ∗ F)))) ?_ ?_
  · rw [hspEq, show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
        show sp + BitVec.ofNat 64 22400 = sp + 22400#64 from rfl]
    dsimp only [FF]; sep_frame
  refine step_b_seg5 (w := 6159) (disp := 20#64) (Or.inr ⟨by decide, by decide⟩) (by decide +kernel) hpc2 hrun2 ?_
  rcases hreg2.1 with ⟨_, _, _, _, hx21, _, hx23, _, _, _, hx27, _⟩
  let pcBaseI := b + BitVec.ofNat 64 (4 * 6160)
  let bufsI : Nat → List (BitVec 8) := fun i => wordsToBytes (btreeWords (63 * i) 63 tB2)
  refine step_rej_site_init3 (pcBase := pcBaseI) (sqBase := sp + 22400#64)
    (sampBase := sp + 19168#64) (slotsBase := sp + 5680#64) (cfg := cfgRejInit3_04)
    (seeds := rowSeeds rho row) (bufs := bufsI)
    (hpc := by
      change b + BitVec.ofNat 64 (4 * 6159) + 20#64 = (b + BitVec.ofNat 64 (4 * 6160)) + 16#64
      rw [BitVec.add_assoc b, BitVec.add_assoc b]
      exact congrArg (b + ·) (by decide))
    (hrun := (status_setPC _ _).trans hrun2) cfgRejInit3_04_valid rfl
    (fetchesInstrsAt_blk04_seg5 (by omega)
      (by rw [show (rejOuterInstrs cfgRejInit3_04).length = 11 from rfl]; omega)
      (by dsimp only [pcBaseI]; rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
      cert_rejInitO04)
    (fetchesInstrsAt_blk04_seg5 (by omega)
      (by rw [show (rejInnerInstrs cfgRejInit3_04.v).length = 193 from rfl]; omega)
      (by dsimp only [pcBaseI]; rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
      cert_rejInitI04)
    (fun i hi => by
      dsimp only [cfgRejInit3_04] at hi ⊢
      exact rejBufReadable_of_treeMem (offWords := 63 * i)
        (by rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> [simp; rw [BitVec.add_assoc]; rw [BitVec.add_assoc]])
        (by omega) rfl)
    (fun i _ => by dsimp only [bufsI, cfgRejInit3_04]; rw [wordsToBytes_length, btreeWords_length])
    (fun i hi => by
      dsimp only [cfgRejInit3_04] at hi
      rw [List.take_of_length_le (by dsimp only [bufsI]; rw [wordsToBytes_length, btreeWords_length])]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> [exact hbuf0; exact hbuf1; exact hbuf2])
    (MultiLaneClampedInv.init_zero 3).toRaw
    (readReg64_setPC hx9_2)
    (by dsimp only [cfgRejInit3_04]; rw [readReg64_setPC hx10_2, BitVec.add_assoc]; rfl)
    (readReg64_setPC hx23) (readReg64_setPC hx21) (readReg64_setPC hx27) ?_
  intro sF sampled' hws' hp hraw
  rcases segRegInv04_of_sitePreserved (pc := pcAt pcBaseI 204) hp
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (segRegInv04_setPC hreg2.1) (readReg64_setPC hx8_2) (readReg64_setPC hreg2.2.2)
    with ⟨hregF, hx8F, hx19F⟩
  refine SepWP.done
    (by
      change (b + BitVec.ofNat 64 (4 * 6160)) + BitVec.ofNat 64 (4 * 204) = b + BitVec.ofNat 64 (4 * 6364)
      rw [BitVec.add_assoc]; exact congrArg (b + ·) (by decide))
    ((status_setPC _ _).trans hp.1)
    ⟨hregF, hx8F, hx19F, tA2, sampled', hws', htA2, hraw,
     fun idx hidx => slotHolds_of_sitePreserved hp (slotHolds_setPC (hs01_2 idx hidx)),
     fun idx hidx => by rcases hs2_2 idx hidx with ⟨vh, hh⟩; exact slotHoldsLo_of_sitePreserved hp ⟨vh, slotHolds_setPC hh⟩,
     Entails.trans (sepConj_mono_left
       (by simpa using treeMem_entails_memRegion (ptr := sp + 22400#64) (len := 189) tB2 (by decide))) (by sep_frame)⟩

private theorem seg5_row_init_rej [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {F : SepProp} {s2 : State} {env0 envF : KEnv} {stEnd : KState}
    (hev0_100 : env0.vars 100 = BitVec.ofNat 64 row)
    (hev0_102 : env0.vars 102 = fpVal)
    (hev0_rho : ∀ k, k < 4 → env0.vars (103 + k) = rhoW rho k)
    (hev0_sp : env0.sp = sp)
    (hpc2 : s2.pc = b + BitVec.ofNat 64 (4 * 6159)) (hrun2 : s2.status = .Running)
    (hspF : envF.sp = env0.sp)
    (hrcF : envF.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (heval : ∀ e, exprVarsOk (validSpecVar 1500 (progBases stepsInit04)) e = true →
      evalKExpr envF e = evalKExpr (specEnvSteps env0 stepsInit04) e)
    (hm2 : KStateMatches envF stEnd s2)
    (hchk : checkInitEnd04 stEnd = true) :
    let FF := MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 20704#64) 504 ∗ MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗ F
    SepWP (blkPC04.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 6364)) s2
      (KSpatial cfgInit04 envF stEnd FF)
      (Seg5InitPreClampPost sp fpVal rho row F) := by
  intro FF
  have hspEq : envF.sp = sp := hspF.trans hev0_sp
  rcases specEnv_stepsInit04_vars hrho hrow hev0_100 hev0_rho with
    ⟨hv100S, hv102S, hvRhoS, hv2000, hv2025, hv3000, hv3025,
      hv4000, hv4025, hv5000, hv5025, hv6000, hv6025, hv7000, hv7025⟩
  simp only [checkInitEnd04, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hchkG, hchkC⟩, hx9B⟩, hx10B⟩, hmemB⟩, hslots⟩
  have hreg2 := extract_segRegInv04 (eX8 := .add64 (.var 100) (.const64 1#64)) hm2 hspEq hrcF
    (by simpa [evalKExpr, hv100S] using (heval (.var 100) (okInit04_low (by decide))))
    (by simpa [evalKExpr, hv102S, hev0_102] using (heval (.var 102) (okInit04_low (by decide)))) hchkG
  have hx8_2 : s2.readReg64 .x8 = BitVec.ofNat 64 (row + 1) := by
    have hokAdd : exprVarsOk (validSpecVar 1500 (progBases stepsInit04)) (.add64 (.var 100) (.const64 1#64)) = true :=
      by simp [exprVarsOk, okInit04_low (show 100 < 1500 by decide)]
    rw [hreg2.2.1, heval _ hokAdd]
    simp [evalKExpr, hv100S, BitVec.ofNat_add]
  have htA2 : Seg5ConstWordsInv sp rho (stEnd.memA.map (evalKExpr envF)) :=
    extract_constWords04 hspEq
      (by simpa [evalKExpr, hvRhoS 0 (by decide)] using heval (.var 103) (okInit04_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 1 (by decide)] using heval (.var 104) (okInit04_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 2 (by decide)] using heval (.var 105) (okInit04_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 3 (by decide)] using heval (.var 106) (okInit04_low (by decide))) hchkC
  have hx9_2 : s2.readReg64 (.gpr 9#5) = 0#64 :=
    eval_checked_gpr hm2 heval 9#5 (by decide) (.const64 0#64) hx9B rfl
  have hx10_2 : s2.readReg64 .x10 = sp + 22411#64 := by
    simpa [evalKExpr, specEnvSteps_sp, hev0_sp] using
      eval_checked_gpr hm2 heval 10#5 (by decide) (.spAdd 22411#64) hx10B rfl
  let tA2 := stEnd.memA.map (evalKExpr envF)
  let tB2 := stEnd.memB.map (evalKExpr envF)
  have hs01_2 : ∀ idx, idx < 25 → slotHolds cfgClamp04 s2 tA2 (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    have h := eval_checked_slot hm2 heval _ hs.1.1.1.1 (.var (5000 + idx)) (.var (5025 + idx))
      hs.1.1.1.2 hs.1.1.2 (okInit04_lo 5000 (by decide) hidx) (okInit04_hi 5000 (by decide) hidx)
    rwa [evalKExpr, evalKExpr, hv5000 idx hidx, hv5025 idx hidx] at h
  have hs2_2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp04 s2 tA2 (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    exact eval_col2_slotLo hm2 heval hs.1.2 hs.2
      (okInit04_lo 7000 (by decide) hidx) (okInit04_hi 7000 (by decide) hidx) (hv7000 idx hidx) (hv7025 idx hidx)
  have hbuf0 : wordsToBytes (btreeWords 0 63 tB2) = shake128FirstBlocks (rowSeeds rho row 0) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval j (.var (2000 + j)) hm.1.1.1.1.1.1.1.1 (okInit04_lo 2000 (by decide) (by omega))).trans (hv2000 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval (21 + j) (.var (4000 + j)) hm.1.1.1.1.1.1.1.2 (okInit04_lo 4000 (by decide) (by omega))).trans (hv4000 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval (42 + j) (.var (5000 + j)) hm.1.1.1.1.1.1.2 (okInit04_lo 5000 (by decide) (by omega))).trans (hv5000 j (by omega))
  have hbuf1 : wordsToBytes (btreeWords 63 63 tB2) = shake128FirstBlocks (rowSeeds rho row 1) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact (eval_checked_memB heval (63 + j) (.var (2025 + j)) hm.1.1.1.1.1.2 (okInit04_hi 2000 (by decide) (by omega))).trans (hv2025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 63 + 21 + j = 84 + j by omega]
      exact (eval_checked_memB heval (84 + j) (.var (4025 + j)) hm.1.1.1.1.2 (okInit04_hi 4000 (by decide) (by omega))).trans (hv4025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 63 + 42 + j = 105 + j by omega]
      exact (eval_checked_memB heval (105 + j) (.var (5025 + j)) hm.1.1.1.2 (okInit04_hi 5000 (by decide) (by omega))).trans (hv5025 j (by omega))
  have hbuf2 : wordsToBytes (btreeWords 126 63 tB2) = shake128FirstBlocks (rowSeeds rho row 2) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact eval_col2_memB heval hm.1.1.2 (okInit04_lo 3000 (by decide) (by omega)) (okInit04_hi 3000 (by decide) (by omega)) (hv3000 j (by omega)) (hv3025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 126 + 21 + j = 147 + j by omega]
      exact eval_col2_memB heval hm.1.2 (okInit04_lo 6000 (by decide) (by omega)) (okInit04_hi 6000 (by decide) (by omega)) (hv6000 j (by omega)) (hv6025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 126 + 42 + j = 168 + j by omega]
      exact eval_col2_memB heval hm.2 (okInit04_lo 7000 (by decide) (by omega)) (okInit04_hi 7000 (by decide) (by omega)) (hv7000 j (by omega)) (hv7025 j (by omega))
  exact step_init_rej04 hpc2 hrun2 hspEq hreg2 hx8_2 htA2 hx9_2 hx10_2 hs01_2 hs2_2 hbuf0 hbuf1 hbuf2

private theorem seg5_row_init_pre_clamp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} (htA : Seg5ConstWordsInv sp rho tA)
    {F : SepProp} {s1 : State} {P1 : SepProp}
    (hpc1 : s1.pc = b + BitVec.ofNat 64 (4 * 4324)) (hrun1 : s1.status = .Running)
    (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hreg1 : Seg5RegInv sp fpVal s1) (hx19_1 : s1.readReg64 .x19 = BitVec.ofNat 64 row)
    (hP1 : P1 ⊢ MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗ F)) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 6364)) s1 P1
      (Seg5InitPreClampPost sp fpVal rho row F) := by
  refine sepWP_mono_pre (Entails.trans hP1 (Entails.trans (by sep_frame :
      MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
        MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗
        (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗ F) ⊢
      memRegion (sp + 22400#64) 1512 ∗
        (TreeMem (sp + 144#64) 264 tA ∗ MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          memRegion (sp + 20704#64) 504 ∗ MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗ F))
    (sepConj_mono_left (memRegion_entails_exists_treeMem (ptr := sp + 22400#64) (len := 189) (by decide))))) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tB0
  let env0 := mkSegEnv04 sp fpVal row rho #[] #[] #[] (fun _ => 0#64) s1 tA tB0
  rcases mkSegState04_matches (cfg := cfgInit04) (hasConsts := true) (slots01 := []) (slots2 := [])
    (k0 := #[]) (k1 := #[]) (k2 := #[]) (k2Hi := fun _ => 0#64) (tA := tA) (tB := tB0)
    (by decide) (by decide) hreg1 hx19_1 (fun _ => htA) (fun _ h => nomatch h) (fun _ h => nomatch h)
    with ⟨hm0, htA_eq, htB_eq⟩
  apply keccakRc_intro hro1
  let FF := MultiLaneSlots (sp + 5680#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
    memRegion (sp + 20704#64) 504 ∗ MultiLaneSampled (sp + 19168#64) 3 (fun _ => 0) ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgInit04 env0 stInit0_04 FF) ?_ ?_
  · unfold stInit0_04; dsimp only [KSpatial, FF]
    rw [htA_eq, htB_eq]
    dsimp only [cfgInit04]
    rw [show env0.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show env0.sp = sp from rfl,
      show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
      show sp + BitVec.ofNat 64 22400 = sp + 22400#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hr0 : env0.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runAndCheckKProg04 cfgInit04_wf hr0 cert_stepsInit04 hm0 hpc1 hrun1 ?_
  intro s2 envF stEnd hpc2 hrun2 hspF hrcF _hrlF heval hm2 hchk
  exact seg5_row_init_rej (fpVal := fpVal) hrho hrow (by simp [env0, mkSegEnv04]) (by simp [env0, mkSegEnv04])
    (fun k hk => by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [env0, mkSegEnv04]) rfl hpc2 hrun2 hspF hrcF heval hm2 hchk

theorem seg5_row_init_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} (htA : Seg5ConstWordsInv sp rho tA)
    {F : SepProp} {s0 : State}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * 4315)) (hrun0 : s0.status = .Running)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hreg0 : Seg5RegInv sp fpVal s0) (hx8_0 : s0.readReg64 .x8 = BitVec.ofNat 64 row) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0
       then b + BitVec.ofNat 64 (4 * 4150) else b + BitVec.ofNat 64 (4 * 6390)) s0
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg5RowDone b sp fpVal rho row F sf Pf
        else Seg5LoopState b sp fpVal rho row F 0 sf Pf) := by
  refine SepWP.congr_pre (P1 := memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 19168#64) 24 ∗
      (TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗ F))
      (by apply sepProp_ext <;> sep_frame) ?_
  refine sepWP_seq_env hcl0 hro0
    (seg5_row_memset hb hbase s0 sp fpVal row _ hpc0 hrun0 hreg0 hx8_0 hcl0) ?_
  intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hreg1, hx19_1, hP1⟩
  exact sepWP_seq_env hcl1 hro1
    (seg5_row_init_pre_clamp hrho hrow htA hpc1 hrun1 hro1 hreg1 hx19_1 hP1)
    (fun sF PF hpcF hrunF hclF hroF ⟨hrF, hx8F, hx19F, tA2, sampled', hws', htA2, hraw, hs01F, hs2F, hPF⟩ =>
      sepWP_mono_pre hPF (seg5_row_clamp_init3 hpcF hrunF hclF hroF hrF hx8F hx19F htA2 hraw hs01F hs2F))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowInit
