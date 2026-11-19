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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowStep

/-!
# `encapsulate1_serialized` (`B03`) — `Seg2` `extra1` Loop & Full Row WP (`Seg2Row`)

Proves `seg2_row_clamp_extra1`, `seg2_row_bodyA_wp` (`+0x2580 → +0x2e84`), `seg2_row_bodyB_wp`
(`+0x2e84 → +0x026c / +0x2580`), `seg2_row_safeSepWP`, and `seg2_row_sepWP`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakF1600 Shake128SeedTerminates shake128BlockAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  decMemReg rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone sampleNttRow_safeSepWP sampleNttRow_sepWP step_rej_site_extra1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blkPC03 blkPl03 sepWP_with_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KExpr KState evalKExpr runKRange runKRange_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeOfWords btreeOfWords_get btreeWords checkInstrsAt03 fetchesInstrsAt_blk03_seg2b
  seedConstsWords sepWP_elim_treeMem treeMem_entails_memRegion wordsToBytes
  wordsToBytes_length zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KConstsLoOpt KSpatial KStateMatches evalMemTree matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  inv01Slots inv2Slots rejBufReadable_of_treeMem slotsL7 slotsL8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  KProgStep Seg2LoopState Seg2RowExit cfgClamp cfgClamp_wf cfgExtra cfgExtra_wf
  cfgRejExtra1 cfgRejExtra1_valid condCC_256_of_le271 condCS_256_of_le271
  condHI_255_of_le271 evalExprList25 exprVarsOk extendLoopVars keccakRc_intro raw_sampled_le271
  rowPermState rowPermState_size rowPermState_succ rowSeeds runAndCheckKProg
  shake128BlockAt_rowSeeds_eq specEnvSteps step_bCond_seg2b step_b_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner (
  eval_checked_gpr eval_checked_pstate sepWP_of_runAndCheckKProg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp (
  checkSeedConstsMemA checkSegRegGprs eq_some_getD extract_seedConsts extract_segRegInv
  finish_clamp_branch mkSegEnv mkSegState mkSegState_matches preExtra01Slots preExtra2Slots
  sepWP_drop_left with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit (
  evalExprList25_varRange expVarRange expZero25 extendLoopVars_hi extendLoopVars_lo
  extendLoopVars_lt pc_add_eq pc_of_eq runKRange_cselHi segRegInv_of_sitePreserved
  setPC_disp_eq setPC_disp_w_eq setPC_fall_eq setPC_fall_w_eq slotHolds_of_sitePreserved
  stepCselHi)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowStep (
  chkSlotsPair25 chkSlotsSingle25 chkSq21 extract_slotsPair25 extract_slotsSingle25
  extract_sq21 not_mem_of_dec readReg64_setPC seg2_row_init_wp segRegInv_setPC
  sepWP_congr_pre_entails slotHolds_setPC status_setPC)

attribute [local irreducible] keccakF1600 blkPC03

private def stExtClamp0 : KState := mkSegState cfgClamp true preExtra01Slots preExtra2Slots
private def stExtA : KState := (runKRange cfgClamp 3182 9 stExtClamp0).getD stExtClamp0
private def stExtB : KState := stepCselHi 12#5 (.var 900) stExtA
private def stExtC : KState := (runKRange cfgClamp 3192 3 stExtB).getD stExtB
private def stExtD : KState := stepCselHi 13#5 (.var 901) stExtC
private def stExtE : KState := (runKRange cfgClamp 3196 26 stExtD).getD stExtD
private def stExtF : KState := stepCselHi 12#5 (.var 902) stExtE
private def stExtC1 : KState := (runKRange cfgClamp 3223 5 stExtF).getD stExtF
private def stExtCHi : KState := (runKRange cfgClamp 3229 1 stExtC1).getD stExtC1
private def stExtCEnd : KState := (runKRange cfgClamp 2398 1 stExtCHi).getD stExtCHi

private theorem runKRange_stExtC1 : runKRange cfgClamp 3182 46 stExtClamp0 = some stExtC1 := by
  have h0 : runKRange cfgClamp 3182 9 stExtClamp0 = some stExtA :=
    eq_some_getD stExtClamp0 (by decide +kernel)
  have h1 : runKRange cfgClamp 3182 10 stExtClamp0 = some stExtB :=
    runKRange_append (m := 9) (n := 1) h0
      (runKRange_cselHi 3191 12#5 27#5 9#5 (.var 900) stExtA
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h2 : runKRange cfgClamp 3182 13 stExtClamp0 = some stExtC :=
    runKRange_append (m := 10) (n := 3) h1 (eq_some_getD stExtB (by decide +kernel))
  have h3 : runKRange cfgClamp 3182 14 stExtClamp0 = some stExtD :=
    runKRange_append (m := 13) (n := 1) h2
      (runKRange_cselHi 3195 13#5 27#5 10#5 (.var 901) stExtC
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h4 : runKRange cfgClamp 3182 40 stExtClamp0 = some stExtE :=
    runKRange_append (m := 14) (n := 26) h3 (eq_some_getD stExtD (by decide +kernel))
  have h5 : runKRange cfgClamp 3182 41 stExtClamp0 = some stExtF :=
    runKRange_append (m := 40) (n := 1) h4
      (runKRange_cselHi 3222 12#5 27#5 11#5 (.var 902) stExtE
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  exact runKRange_append (m := 41) (n := 5) h5 (eq_some_getD stExtF (by decide +kernel))

private theorem seg2_row_clamp_extra1 [MlKemPlacement] {b sp : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {F : SepProp} {tA : BTree (BitVec 64) 9}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {s : State}
    (hpc : s.pc = b + 0x31b8#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64)
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) (extra + 1) sampled hws)
    (hs01 : ∀ idx, idx < 25 → slotHolds cfgClamp s tA (preExtra01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
      ((rowPermState rho row 1 (extra + 3)).getD idx 0#64))
    (hs2 : ∀ idx, idx < 25 → slotHolds cfgClamp s tA (preExtra2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 (extra + 3)).getD idx 0#64) 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) (extra + 1) then b + 0x026c#64 else b + 0x2580#64) s
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ MultiLaneSampled (sp + 12448#64) 3 sampled ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) (extra + 1) then Seg2RowExit b sp rho row F sf Pf
        else Seg2LoopState b sp rho row F (extra + 1) sf Pf) := by
  have status_setPC : ∀ {st : State} {pc : BitVec 64},
      st.status = .Running → (st.setPC pc).status = .Running := fun h => h
  let wsB : List (BitVec 64) :=
    [BitVec.ofNat 64 (sampled 0), BitVec.ofNat 64 (sampled 1), BitVec.ofNat 64 (sampled 2)]
  let tB := btreeOfWords 0 wsB zeroTree9
  have htB : ∀ i, i < 3 → tB.get i = BitVec.ofNat 64 (sampled i) := fun i hi => by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact (btreeOfWords_get 0 wsB zeroTree9 0 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
    · exact (btreeOfWords_get 0 wsB zeroTree9 1 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
    · exact (btreeOfWords_get 0 wsB zeroTree9 2 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
  apply with_frozen_env hcl hro
  apply keccakRc_intro hro
  let env := mkSegEnv sp row rho (rowPermState rho row 0 (extra + 3))
    (rowPermState rho row 1 (extra + 3)) (rowPermState rho row 2 (extra + 3)) s tA tB
  rcases mkSegState_matches (cfg := cfgClamp) (hasSeedConsts := true)
    (slots01 := preExtra01Slots) (slots2 := preExtra2Slots) (row := row)
    (k0 := rowPermState rho row 0 (extra + 3)) (k1 := rowPermState rho row 1 (extra + 3))
    (k2 := rowPermState rho row 2 (extra + 3)) (tA := tA) (tB := tB)
    (by decide +kernel) (by decide +kernel) hreg hx22 (fun _ => htA) hs01 hs2
    with ⟨hm0, htA_eq, htB_eq⟩
  let FF := Seg2ConstsLo sp ∗ memRegion (sp + 2192#64) 1512 ∗
    MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgClamp env stExtClamp0 FF) ?_ ?_
  · dsimp only [stExtClamp0, KSpatial]
    rw [htA_eq, htB_eq]
    dsimp only [KConstsLoOpt, cfgClamp, FF]
    rw [emp_sepConj, Seg2Init.multiLaneSampled3_eq_treeMem sp sampled tB
          (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide)),
        show env.sp = sp from rfl,
        show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
        show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
        show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0) := by simpa [env, mkSegEnv] using htB 0 (by decide)
  have hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1) := by simpa [env, mkSegEnv] using htB 1 (by decide)
  have hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2) := by simpa [env, mkSegEnv] using htB 2 (by decide)
  have hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, h]
  have hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 (extra + 3)).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  have hr0 : env.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 3182) (n := 46) (st' := stExtC1)
    (by omega) (by omega)
    (by rw [BitVec.ofNat_mul 4 3182]; exact pc_of_eq hpc (by decide +kernel)) hrun hm0 runKRange_stExtC1 ?_
  intro s1 hpc1 hrun1 hm1
  have hp1 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm1
    (fun _ _ => rfl) (.var 902) 256#64 (by decide +kernel) rfl
  refine step_bCond_seg2b (w := 3228) (cond := .CC) (disp := BitVec.ofInt 64 (-3312))
    (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc1 (by decide +kernel)) hrun1 ?_ ?_
  · intro hcc
    rw [hp1, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcc
    have hs2lt : sampled 2 < 256 := of_decide_eq_true hcc
    have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
      Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 2 (by decide)) (by omega)
    exact finish_clamp_branch (extra := extra + 1) hraw (matches_setPC hm1 _) rfl rfl
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
      hv0 hv1 hv2 hb0 hb1 hb2 false hdone
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_disp_eq s1 b 3228 (BitVec.ofInt 64 (-3312)) 0x2580#64 (by decide +kernel))
      (status_setPC hrun1) (by decide +kernel)
  · intro hccF
    rw [hp1, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hccF
    have hs2ge : 256 ≤ sampled 2 := by have := of_decide_eq_false hccF; omega
    refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 3229) (n := 1) (st' := stExtCHi)
      (by omega) (by omega) (setPC_fall_w_eq s1 b 3228 3229 (by decide +kernel)) (status_setPC hrun1)
      (matches_setPC hm1 _) (eq_some_getD _ (by decide +kernel)) ?_
    intro s2 hpc2 hrun2 hm2
    have hp2 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm2
      (fun _ _ => rfl) (.var 901) 256#64 (by decide +kernel) rfl
    refine step_bCond_seg2b (w := 3230) (cond := .CS) (disp := BitVec.ofInt 64 (-3328))
      (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_ ?_
    · intro hcs
      rw [hp2, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcs
      have hs1ge : 256 ≤ sampled 1 := of_decide_eq_true hcs
      refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 2398) (n := 1) (st' := stExtCEnd)
        (by omega) (by omega) (setPC_disp_w_eq s2 b 3230 (BitVec.ofInt 64 (-3328)) 2398 (by decide +kernel))
        (status_setPC hrun2) (matches_setPC hm2 _) (eq_some_getD _ (by decide +kernel)) ?_
      intro s3 hpc3 hrun3 hm3
      have hp3 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm3
        (fun _ _ => rfl) (.var 900) 255#64 (by decide +kernel) rfl
      refine step_bCond_seg2b (w := 2399) (cond := .HI) (disp := BitVec.ofInt 64 (-8976))
        (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc3 (by decide +kernel)) hrun3 ?_ ?_
      · intro hhi
        rw [hp3, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhi
        have hs0ge : 256 ≤ sampled 0 := of_decide_eq_true hhi
        have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = true :=
          hraw.allLanesDone_iff_ge256.mpr fun i hi => by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption
        exact finish_clamp_branch (extra := extra + 1) hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
          hv0 hv1 hv2 hb0 hb1 hb2 true hdone
          (by simp only [↓reduceIte]; exact setPC_disp_eq s3 b 2399 (BitVec.ofInt 64 (-8976)) 0x026c#64 (by decide +kernel))
          (status_setPC hrun3) (by decide +kernel)
      · intro hhiF
        rw [hp3, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhiF
        have hs0lt : sampled 0 < 256 := by have := of_decide_eq_false hhiF; omega
        have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
          Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 0 (by decide)) (by omega)
        exact finish_clamp_branch (extra := extra + 1) hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
          hv0 hv1 hv2 hb0 hb1 hb2 false hdone
          (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_fall_eq s3 b 2399 0x2580#64 (by decide +kernel))
          (status_setPC hrun3) (by decide +kernel)
    · intro hcsF
      rw [hp2, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcsF
      have hs1lt : sampled 1 < 256 := by have := of_decide_eq_false hcsF; omega
      have hdone : allLanesDone 3 (rowSeeds rho row) (extra + 1) = false :=
        Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 1 (by decide)) (by omega)
      refine step_b_seg2b (w := 3231) (disp := BitVec.ofInt 64 (-3324)) (by omega) (by omega) (by decide +kernel)
        (setPC_fall_w_eq s2 b 3230 3231 (by decide +kernel)) (status_setPC hrun2) ?_
      exact finish_clamp_branch (extra := extra + 1) hraw (matches_setPC (matches_setPC hm2 _) _) rfl rfl
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
        hv0 hv1 hv2 hb0 hb1 hb2 false hdone
        (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_disp_eq _ b 3231 (BitVec.ofInt 64 (-3324)) 0x2580#64 (by decide +kernel))
        (status_setPC (status_setPC hrun2)) (by decide +kernel)


/-! ## 2. `+0x2580 → +0x2e84` (`extra1` `L7 + L8` Keccak Permutations) -/

private def stExtra0 : KState := mkSegState cfgExtra true inv01Slots inv2Slots

private def stepsExtra : List KProgStep :=
  [.range 2400 24,
   .loop true 2424 200 9#5 slotsL7 (expVarRange 0) (expVarRange 25) 2000,
   .range 2625 92,
   .loop false 2717 192 11#5 slotsL8 (expVarRange 50) expZero25 3000,
   .range 2910 67]

private theorem specEnv_stepsExtra_vars {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row extra : Nat} {env0 : Seg2SymDefs.KEnv}
    (hv0 : ∀ idx, idx < 25 → env0.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64)
    (hv1 : ∀ idx, idx < 25 → env0.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64)
    (hv2 : ∀ idx, idx < 25 → env0.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64) :
    let envS := specEnvSteps env0 stepsExtra
    (∀ id, id < 2000 → envS.vars id = env0.vars id) ∧
    (∀ idx, idx < 25 → envS.vars (2000 + idx) = (rowPermState rho row 0 (extra + 3)).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (2025 + idx) = (rowPermState rho row 1 (extra + 3)).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3000 + idx) = (rowPermState rho row 2 (extra + 3)).getD idx 0#64) := by
  dsimp only [stepsExtra, specEnvSteps]
  let e1 := extendLoopVars env0 2000 (evalExprList25 env0 (expVarRange 0)) (evalExprList25 env0 (expVarRange 25))
  have hp0 : keccakF1600 (evalExprList25 env0 (expVarRange 0)) = rowPermState rho row 0 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 (extra + 2))
      (fun idx h => by simpa using hv0 idx h), rowPermState_succ]
  have hp1 : keccakF1600 (evalExprList25 env0 (expVarRange 25)) = rowPermState rho row 1 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 (extra + 2)) hv1, rowPermState_succ]
  let e2 := extendLoopVars e1 3000 (evalExprList25 e1 (expVarRange 50)) (evalExprList25 e1 expZero25)
  have hp2 : keccakF1600 (evalExprList25 e1 (expVarRange 50)) = rowPermState rho row 2 (extra + 3) := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 (extra + 2))
      (fun idx h => by rw [extendLoopVars_lt (by omega), hv2 idx h]), rowPermState_succ]
  refine ⟨fun id h => by rw [extendLoopVars_lt (by omega), extendLoopVars_lt h],
    fun idx h => by rw [extendLoopVars_lt (by omega), extendLoopVars_lo h, hp0],
    fun idx h => by
      rw [extendLoopVars_lt (by omega), show 2025 + idx = 2000 + 25 + idx from rfl,
          extendLoopVars_hi h, hp1],
    fun idx h => by rw [extendLoopVars_lo h, hp2]⟩

private def chkExtraHdr (ok : Nat → Bool) (st : KState) : Bool :=
  (checkSegRegGprs st (.var 101) && (ok 96 && ok 101)) &&
  (checkSeedConstsMemA st && (ok 97 && ok 98 && ok 99 && ok 100)) &&
  ((st.gprs.get 11).beq (.const64 0#64) && (st.gprs.get 9).beq (.spAdd 13995#64))

private def chkExtraSq (ok : Nat → Bool) (st : KState) : Bool :=
  chkSq21 ok st 0 2000 && chkSq21 ok st 21 2025 && chkSq21 ok st 42 3000

private def chkExtraPost (ok : Nat → Bool) (st : KState) : Bool :=
  chkExtraHdr ok st && chkExtraSq ok st &&
  (chkSlotsPair25 ok st preExtra01Slots 2000 2025 && chkSlotsSingle25 ok st preExtra2Slots 3000)

private theorem cert_stepsExtra :
    runAndCheckKProg cfgExtra 2400 2977 2400 2977 1000 stepsExtra stExtra0 chkExtraPost = true := by
  decide +kernel

private theorem cert_rejExtraO : checkInstrsAt03 2978 (rejOuterInstrs cfgRejExtra1) = true := by
  decide +kernel

private theorem cert_rejExtraI : checkInstrsAt03 2989 (rejInnerInstrs cfgRejExtra1.v) = true := by
  decide +kernel

private def Seg2MidState [MlKemPlacement] (b sp : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (extra : Nat) (s : State) (P : SepProp) : Prop :=
  s.pc = b + 0x2e84#64 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧ Seg2RegInv sp s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x22 = BitVec.ofNat 64 row ∧
  s.readReg64 .x11 = 0#64 ∧ s.readReg64 .x9 = (sp + 13984#64) + 11#64 ∧
  ∃ (tA tSq : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
    (∀ i, i < 3 → wordsToBytes (btreeWords (21 * i) 21 tSq) =
      shake128BlockAt (rowSeeds rho row i) (extra + 3)) ∧
    (∀ idx, idx < 25 → slotHolds cfgClamp s tA (preExtra01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 (extra + 3)).getD idx 0#64)
      ((rowPermState rho row 1 (extra + 3)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHolds cfgClamp s tA (preExtra2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 (extra + 3)).getD idx 0#64) 0#64) ∧
    MultiLaneRawXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (P ⊢ TreeMem (sp + 13984#64) 63 tSq ∗
      (MultiLaneSampled (sp + 12448#64) 3 sampled ∗
        (MultiLaneSlots (sp + 4272#64) 544 3 hws ∗
          (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
            memRegion (sp + 2192#64) 1512 ∗ F))))

private theorem seg2_row_bodyA_wp [MlKemPlacement] {b sp : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row extra : Nat} {F : SepProp}
    {s : State} {P : SepProp} (hInv : Seg2LoopState b sp rho row F extra s P) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x2e84#64) s P
      (Seg2MidState b sp rho row F extra) := by
  rcases hInv with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22, tA, sampled, hws,
    htA, hs01, hs2, hxof, hP⟩
  refine sepWP_congr_pre_entails
    (P1 := memRegion (sp + 13984#64) (8 * 63) ∗
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ MultiLaneSampled (sp + 12448#64) 3 sampled ∗ F))
    (Entails.trans hP (by sep_frame)) ?_
  refine sepWP_elim_treeMem (len := 63) (by decide) fun tB0 => ?_
  apply with_frozen_env hcl hro
  apply keccakRc_intro hro
  let env0 := mkSegEnv sp row rho (rowPermState rho row 0 (extra + 2))
    (rowPermState rho row 1 (extra + 2)) (rowPermState rho row 2 (extra + 2)) s tA tB0
  rcases mkSegState_matches (cfg := cfgExtra) (hasSeedConsts := true)
    (slots01 := inv01Slots) (slots2 := inv2Slots) (row := row)
    (k0 := rowPermState rho row 0 (extra + 2)) (k1 := rowPermState rho row 1 (extra + 2))
    (k2 := rowPermState rho row 2 (extra + 2)) (tA := tA) (tB := tB0)
    (by decide +kernel) (by decide +kernel) hreg hx22 (fun _ => htA) hs01 hs2
    with ⟨hm0, htA0, htB0⟩
  let FF1 := Seg2ConstsLo sp ∗ memRegion (sp + 2192#64) 1512 ∗
    MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ MultiLaneSampled (sp + 12448#64) 3 sampled ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgExtra env0 stExtra0 FF1) ?_ ?_
  · dsimp only [stExtra0, KSpatial]
    rw [htA0, htB0]
    dsimp only [KConstsLoOpt, cfgExtra, FF1]
    rw [emp_sepConj, show env0.sp = sp from rfl,
      show env0.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
      show sp + BitVec.ofNat 64 13984 = sp + 13984#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hr0 : env0.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runAndCheckKProg cfgExtra_wf hr0 cert_stepsExtra hm0
    (by rw [BitVec.ofNat_mul 4 2400]; exact pc_of_eq hpc (by decide +kernel)) hrun ?_
  intro s2 envFinal stEnd hpc2 hrun2 hspF hrcF _ heval hm2 hchk
  have hv0_0 : ∀ idx, idx < 25 → env0.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64 :=
    fun idx h => by simp [env0, mkSegEnv, h]
  have hv1_0 : ∀ idx, idx < 25 → env0.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64 :=
    fun idx h => by simp [env0, mkSegEnv, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2_0 : ∀ idx, idx < 25 → env0.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64 :=
    fun idx h => by simp [env0, mkSegEnv, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  rcases specEnv_stepsExtra_vars hrho hv0_0 hv1_0 hv2_0 with ⟨hlt, hp0, hp1, hp2⟩
  simp only [chkExtraPost, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hHdr, hSq⟩, hsl01, hsl2⟩
  simp only [chkExtraHdr, Bool.and_eq_true] at hHdr
  rcases hHdr with ⟨⟨⟨hregC, ho96, ho101⟩, hseedC, ⟨⟨ho97, ho98⟩, ho99⟩, ho100⟩, hg11, hg9⟩
  simp only [chkExtraSq, Bool.and_eq_true] at hSq
  rcases hSq with ⟨⟨hsq0, hsq1⟩, hsq2⟩
  have hvF : ∀ id, id < 2000 → (ok : (Seg2Init.validSpecVar 1000 (Seg2Init.progBases stepsExtra)) id = true) →
      envFinal.vars id = env0.vars id :=
    fun id hid hok => (heval (.var id) hok).trans (hlt id hid)
  have hv96F : envFinal.vars 96 = BitVec.ofNat 64 row := hvF 96 (by omega) ho96
  have hv101F : envFinal.vars 101 = BitVec.ofNat 64 (row + 1) :=
    (hvF 101 (by omega) ho101).trans hx8
  rcases extract_segRegInv hm2 hspF hrcF hv96F hregC with ⟨hreg2, hx8_2, hx22_2⟩
  have htA2 := extract_seedConsts
    (hvF 97 (by omega) ho97) (hvF 98 (by omega) ho98)
    (hvF 99 (by omega) ho99) (hvF 100 (by omega) ho100) hseedC
  have hx11_2 : s2.readReg64 .x11 = 0#64 :=
    eval_checked_gpr hm2 heval 11#5 (by decide) (.const64 0#64) hg11 rfl
  have hx9_2 : s2.readReg64 .x9 = (sp + 13984#64) + 11#64 := by
    have r := eval_checked_gpr hm2 heval 9#5 (by decide) (.spAdd 13995#64) hg9 rfl
    dsimp only [evalKExpr] at r; rw [r, show (specEnvSteps env0 stepsExtra).sp = sp from rfl]
    rw [BitVec.add_assoc]; rfl
  have hs01_2 := extract_slotsPair25 hm2 heval hp0 hp1 hsl01
  have hs2_2 := extract_slotsSingle25 hm2 heval hp2 hsl2
  have hpcEnd : s2.pc = b + 0x2e84#64 := by
    rw [hpc2, BitVec.ofNat_mul 4 2977]
  apply sepWP_drop_left
  refine SepWP.done hpcEnd hrun2 fun hcl2 hro2 => ?_
  refine ⟨hpcEnd, hrun2, hcl2, hro2, hreg2, hx8_2.trans hv101F, hx22_2, hx11_2, hx9_2,
    evalMemTree envFinal stEnd.memA, evalMemTree envFinal stEnd.memB, sampled, hws,
    htA2, ?_, hs01_2, hs2_2, hxof.toRaw, ?_⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact (extract_sq21 heval hp0 hsq0).trans (shake128BlockAt_rowSeeds_eq _ _ _ _)
    · exact (extract_sq21 heval hp1 hsq1).trans (shake128BlockAt_rowSeeds_eq _ _ _ _)
    · exact (extract_sq21 heval hp2 hsq2).trans (shake128BlockAt_rowSeeds_eq _ _ _ _)
  · dsimp only [KConstsLoOpt, cfgExtra, FF1]
    rw [emp_sepConj, hspF, show env0.sp = sp from rfl,
      show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
      show sp + BitVec.ofNat 64 13984 = sp + 13984#64 from rfl]
    sep_frame

private theorem seg2_row_bodyB_wp [MlKemPlacement] {b sp : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {F : SepProp} {sm : State} {Pm : SepProp}
    (_hpc : sm.pc = b + 0x2e84#64) (_hrun : sm.status = .Running)
    (hMid : Seg2MidState b sp rho row F extra sm Pm) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) (extra + 1) then b + 0x026c#64 else b + 0x2580#64)
      sm Pm
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) (extra + 1) then Seg2RowExit b sp rho row F sf Pf
        else Seg2LoopState b sp rho row F (extra + 1) sf Pf) := by
  rcases hMid with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22, hx11, hx9,
    tA, tSq, sampled, hws, htA, hsq, hs01, hs2, hraw, hP⟩
  refine sepWP_congr_pre_entails hP ?_
  refine SepWP.seq (sepWP_with_env hcl hro (target := b + 0x31b8#64)
    (post := fun sC PC => mlkemMultiLib.CodeLoaded mlkemMpl sC.mem → MlKemRoOk mlkemMpl sC.mem →
      SepWP (blkPC03.rebase b (fun _ => none))
        (if allLanesDone 3 (rowSeeds rho row) (extra + 1) then b + 0x026c#64 else b + 0x2580#64) sC PC
        (fun sf Pf =>
          if allLanesDone 3 (rowSeeds rho row) (extra + 1) then Seg2RowExit b sp rho row F sf Pf
          else Seg2LoopState b sp rho row F (extra + 1) sf Pf)) ?_)
    (fun _ _ _ _ ⟨_, _, hclC, hroC, hk⟩ => hk hclC hroC)
  refine step_b_seg2b (w := 2977) (disp := 20#64) (by omega) (by omega) (by decide +kernel)
    (by rw [BitVec.ofNat_mul 4 2977]; exact pc_of_eq hpc (by decide +kernel)) hrun ?_
  let bufs : Nat → List (BitVec 8) := fun i => wordsToBytes (btreeWords (21 * i) 21 tSq)
  rcases hreg with ⟨hsp, hspA, r19, hx20, hx21, r23, hx24, r25, r26, r27, r28⟩
  have hreg' : Seg2RegInv sp sm := ⟨hsp, hspA, r19, hx20, hx21, r23, hx24, r25, r26, r27, r28⟩
  refine step_rej_site_extra1 (pcBase := b + 0x2e88#64) (sqBase := sp + 13984#64)
    (sampBase := sp + 12448#64) (slotsBase := sp + 4272#64) (cfg := cfgRejExtra1)
    (seeds := rowSeeds rho row) (bufs := bufs) (extra := extra)
    ((setPC_disp_eq sm b 2977 20#64 0x2e98#64 (by decide +kernel)).trans
      (by change b + 0x2e98#64 = (b + 0x2e88#64) + 16#64; rw [BitVec.add_assoc]; rfl))
    (status_setPC hrun) cfgRejExtra1_valid rfl
    (fetchesInstrsAt_blk03_seg2b (w0 := 2978) (by omega)
      (by rw [show (rejOuterInstrs cfgRejExtra1).length = 11 from rfl]; omega)
      (by
        change (b + 0x2e88#64) + 0#64 = b + BitVec.ofNat 64 (4 * 2978)
        rw [BitVec.add_zero, BitVec.ofNat_mul 4 2978])
      cert_rejExtraO)
    (fetchesInstrsAt_blk03_seg2b (w0 := 2989) (by omega)
      (by rw [show (rejInnerInstrs cfgRejExtra1.v).length = 193 from rfl]; omega)
      (by
        rw [BitVec.add_assoc, BitVec.ofNat_mul 4 11, BitVec.ofNat_mul 4 2989]
        exact congrArg (b + ·) (by decide))
      cert_rejExtraI)
    (fun i hi => by
      dsimp only [cfgRejExtra1] at hi ⊢
      exact rejBufReadable_of_treeMem (offWords := 21 * i)
        (by congr 1; exact eq_of_beq (by
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> decide))
        (by omega) rfl)
    (fun i hi => by
      dsimp only [cfgRejExtra1, bufs] at hi ⊢
      rw [wordsToBytes_length, Seg2Mem.btreeWords_length])
    (fun i hi => by
      dsimp only [cfgRejExtra1] at hi
      rw [List.take_of_length_le (by dsimp only [bufs]; rw [wordsToBytes_length, Seg2Mem.btreeWords_length])]
      exact hsq i hi)
    hraw
    (readReg64_setPC hx11) (readReg64_setPC hx9)
    (readReg64_setPC hx21) (readReg64_setPC hx24) (readReg64_setPC hx20) ?_
  intro sF sampled' hws' hpSite hraw'
  rcases segRegInv_of_sitePreserved (pc := pcAt (b + 0x2e88#64) 204) hpSite
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (segRegInv_setPC hreg') (readReg64_setPC hx8) (readReg64_setPC hx22)
    with ⟨hregF, hx8F, hx22F⟩
  have hs01F := fun idx h =>
    slotHolds_of_sitePreserved (pc := pcAt (b + 0x2e88#64) 204) hpSite (slotHolds_setPC (hs01 idx h))
  have hs2F := fun idx h =>
    slotHolds_of_sitePreserved (pc := pcAt (b + 0x2e88#64) 204) hpSite (slotHolds_setPC (hs2 idx h))
  have hpcF : (sF.setPC (pcAt (b + 0x2e88#64) 204)).pc = b + 0x31b8#64 := by
    change (b + 0x2e88#64) + BitVec.ofNat 64 (4 * 204) = b + 0x31b8#64
    rw [BitVec.add_assoc, BitVec.ofNat_mul 4 204]
    exact congrArg (b + ·) (by decide)
  refine SepWP.done hpcF (status_setPC hpSite.1) fun hclF hroF => ?_
  refine sepWP_congr_pre_entails
    (show TreeMem (sp + 13984#64) 63 tSq ∗
        (MultiLaneSampled (sp + 12448#64) 3 sampled' ∗
          (MultiLaneSlots (sp + 4272#64) 544 3 hws' ∗
            (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗ F))) ⊢
        Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
          MultiLaneSlots (sp + 4272#64) 544 3 hws' ∗ MultiLaneSampled (sp + 12448#64) 3 sampled' ∗
          memRegion (sp + 13984#64) 504 ∗ F by
      have htm := treeMem_entails_memRegion (ptr := sp + 13984#64) tSq (len := 63) (by decide)
      rw [show 8 * 63 = 504 from rfl] at htm
      exact Entails.trans (sepConj_mono_left htm) (by sep_frame)) ?_
  exact seg2_row_clamp_extra1 hpcF (status_setPC hpSite.1) hclF hroF hregF hx8F hx22F htA hraw' hs01F hs2F

/-! ## 3. Full Single-Row `SafeSepWP` (Unconditional) & `SepWP` (Conditional) -/

theorem seg2_row_safeSepWP [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) :
    SafeSepWP (blkPC03.rebase b (fun _ => none)) s
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (Seg2RowExit b sp rho row F) :=
  sampleNttRow_safeSepWP
    (loopHead := b + 0x2580#64) (midPC := b + 0x2e84#64) (exitPC := b + 0x026c#64)
    (by intro heq; clear *- heq; bv_omega)
    (fun _ _ _ h => h.1)
    (seg2_row_init_wp hb hbase hrho hrow hpc hrun hcl hro hreg hx8 htA)
    (fun _ _ _ h => seg2_row_bodyA_wp hrho h)
    (fun _ _ _ h1 h2 h3 => seg2_row_bodyB_wp h1 h2 h3)

theorem seg2_row_sepWP [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    (hTerm : ∀ c, c < 3 → Shake128SeedTerminates (rowSeeds rho row c))
    {tA : BTree (BitVec 64) 9} {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x026c#64) s
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (Seg2RowExit b sp rho row F) :=
  sampleNttRow_sepWP hTerm
    (seg2_row_init_wp hb hbase hrho hrow hpc hrun hcl hro hreg hx8 htA)
    (fun _ _ _ h => seg2_row_bodyA_wp hrho h)
    (fun _ _ _ h1 h2 h3 => seg2_row_bodyB_wp h1 h2 h3)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row
