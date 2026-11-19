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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner

/-!
# `encapsulate1_serialized` (`B03`) — `Seg2` Row Init Helpers (`Seg2RowInit`)

Row counter + `B29` `memset`, 6-permutation `L1..L6` spec, and `init3` clamp.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakF1600 keccakZeroState packLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (keccakLastBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism (
  keccakXorRate21 keccakXorRate21_getD_ge keccakXorRate21_getD_lt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03 blkPl03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr fetchWordTree03 runKRange runKRange_append stepKInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeOfWords btreeOfWords_get seedConstsWords sepWP_elim_treeMem zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KConstsLoOpt KSpatial evalMemTree matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2a sepWP_runKRange_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  btreeKExprBeq_eq_true readSlot slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  kpflagOptBeq kpflagOptBeq_eq_true slotsL1 slotsL2 slotsL3 slotsL4 slotsL5 slotsL6 stepKLoopSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  KProgStep Seg2LoopState Seg2RowExit cfgClamp cfgClamp_wf cfgInit condCC_256_of_le271
  condCS_256_of_le271 condHI_255_of_le271 envRow evalExprList25 evalKExpr_eq_envRow
  exprOnlyVar96 extendLoopVars keccakRc_intro lastBlock_rowSeeds_pack_ge4
  lastBlock_rowSeeds_pack_lt4 multiLaneSampled3_eq_treeMem raw_sampled_le271
  replicate1632_eq_multiLaneSlots0 rowPermState rowPermState_succ rowPermState_zero
  rowSeeds seg2_bl_memset specEnvSteps step_bCond_seg2b step_b_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner (
  eval_checked_gpr eval_checked_memB eval_checked_pstate)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp (
  eq_some_getD finish_clamp_branch mkSegEnv mkSegState mkSegState_matches
  preClamp01Slots preClamp2Slots sepWP_drop_left with_frozen_env)

attribute [local irreducible] keccakF1600 blkPC03

@[expose] def stepCselHi (rd : BitVec 5) (lhs : KExpr) (st : KState) : KState :=
  { st with gprs := st.gprs.set rd.toNat (.clamp64 lhs) }

theorem runKRange_cselHi {cfg : KCfg} (w : Nat) (rd rn rm : BitVec 5) (lhs : KExpr) (st : KState)
    (hfw : fetchWordTree03 w = some (.condSelect .W64 .CSEL (.gpr rd) (.gpr rn) (.gpr rm) .HI))
    (hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false)
    (hp : kpflagOptBeq st.pstateFlag (some (.subs64 lhs 255#64)) = true)
    (hrn : (st.gprs.get rn.toNat).beq (.const64 256#64) = true)
    (hrm : (st.gprs.get rm.toNat).beq lhs = true) :
    runKRange cfg w 1 st = some (stepCselHi rd lhs st) := by
  simp [runKRange, hfw, stepKInst, hrr, kpflagOptBeq_eq_true hp, KExpr.beq_eq_true hrn, hrm, stepCselHi]

@[expose] def stInitClamp0 : KState := mkSegState cfgClamp true preClamp01Slots preClamp2Slots
@[expose] def stInitCA : KState :=
  stepCselHi 12#5 (.var 900) ((runKRange cfgClamp 2368 8 stInitClamp0).getD stInitClamp0)
@[expose] def stInitCB : KState :=
  stepCselHi 13#5 (.var 901) ((runKRange cfgClamp 2377 1 stInitCA).getD stInitCA)
@[expose] def stInitCC : KState :=
  stepCselHi 12#5 (.var 902) ((runKRange cfgClamp 2379 2 stInitCB).getD stInitCB)
@[expose] def stInitC1 : KState := (runKRange cfgClamp 2382 3 stInitCC).getD stInitCC
@[expose] def stInitCLo : KState := (runKRange cfgClamp 2393 4 stInitC1).getD stInitC1
@[expose] def stInitCHi : KState := (runKRange cfgClamp 2386 5 stInitC1).getD stInitC1
@[expose] def stInitCEnd : KState := (runKRange cfgClamp 2398 1 stInitCHi).getD stInitCHi

private theorem runKRange_stInitC1 : runKRange cfgClamp 2368 17 stInitClamp0 = some stInitC1 := by
  have h1 : runKRange cfgClamp 2368 9 stInitClamp0 = some stInitCA :=
    runKRange_append (m := 8) (n := 1) (eq_some_getD _ (by decide +kernel))
      (runKRange_cselHi 2376 12#5 27#5 9#5 (.var 900) _
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h2 : runKRange cfgClamp 2368 10 stInitClamp0 = some ((runKRange cfgClamp 2377 1 stInitCA).getD stInitCA) :=
    runKRange_append (m := 9) (n := 1) h1 (eq_some_getD _ (by decide +kernel))
  have h3 : runKRange cfgClamp 2368 11 stInitClamp0 = some stInitCB :=
    runKRange_append (m := 10) (n := 1) h2
      (runKRange_cselHi 2378 13#5 27#5 10#5 (.var 901) _
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h4 : runKRange cfgClamp 2368 13 stInitClamp0 = some ((runKRange cfgClamp 2379 2 stInitCB).getD stInitCB) :=
    runKRange_append (m := 11) (n := 2) h3 (eq_some_getD _ (by decide +kernel))
  have h5 : runKRange cfgClamp 2368 14 stInitClamp0 = some stInitCC :=
    runKRange_append (m := 13) (n := 1) h4
      (runKRange_cselHi 2381 12#5 27#5 11#5 (.var 902) _
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  exact runKRange_append (m := 14) (n := 3) h5 (eq_some_getD _ (by decide +kernel))

theorem pc_of_eq {b x y : BitVec 64} {s : State} (hpc : s.pc = b + x) (h : (x == y) = true) :
    s.pc = b + y := by rw [hpc, eq_of_beq h]

theorem pc_add_eq {b : BitVec 64} {w1 w2 : Nat} {s : State}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w1))
    (h : (4#64 * BitVec.ofNat 64 w1 == 4#64 * BitVec.ofNat 64 w2) = true) :
    s.pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [hpc, BitVec.ofNat_mul 4 w1, BitVec.ofNat_mul 4 w2, eq_of_beq h]

theorem setPC_disp_eq (s : State) (b : BitVec 64) (w1 : Nat) (disp y : BitVec 64)
    (h : (4#64 * BitVec.ofNat 64 w1 + disp == y) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * w1) + disp)).pc = b + y := by
  change b + BitVec.ofNat 64 (4 * w1) + disp = b + y; rw [BitVec.add_assoc, BitVec.ofNat_mul 4 w1, eq_of_beq h]

theorem setPC_disp_w_eq (s : State) (b : BitVec 64) (w1 : Nat) (disp : BitVec 64) (w2 : Nat)
    (h : (4#64 * BitVec.ofNat 64 w1 + disp == 4#64 * BitVec.ofNat 64 w2) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * w1) + disp)).pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [BitVec.ofNat_mul 4 w2]; exact setPC_disp_eq s b w1 disp _ h

theorem setPC_fall_eq (s : State) (b : BitVec 64) (w1 : Nat) (y : BitVec 64)
    (h : (4#64 * (BitVec.ofNat 64 w1 + 1#64) == y) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * (w1 + 1)))).pc = b + y := by
  change b + BitVec.ofNat 64 (4 * (w1 + 1)) = b + y; rw [BitVec.ofNat_mul 4 (w1 + 1), BitVec.ofNat_add w1 1, eq_of_beq h]

theorem setPC_fall_w_eq (s : State) (b : BitVec 64) (w1 w2 : Nat)
    (h : (4#64 * (BitVec.ofNat 64 w1 + 1#64) == 4#64 * BitVec.ofNat 64 w2) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * (w1 + 1)))).pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [BitVec.ofNat_mul 4 w2]; exact setPC_fall_eq s b w1 _ h

theorem seg2_row_clamp_init3 [MlKemPlacement] {b sp : BitVec 64} {rho : List (BitVec 8)}
    {row : Nat} {F : SepProp} {tA : BTree (BitVec 64) 9}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {s : State}
    (hpc : s.pc = b + 0x2500#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64)
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) 0 sampled hws)
    (hs01 : ∀ idx, idx < 25 → slotHolds cfgClamp s tA (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64))
    (hs2 : ∀ idx, idx < 25 → slotHolds cfgClamp s tA (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64) 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0 then b + 0x026c#64 else b + 0x2580#64) s
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ MultiLaneSampled (sp + 12448#64) 3 sampled ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg2RowExit b sp rho row F sf Pf
        else Seg2LoopState b sp rho row F 0 sf Pf) := by
  let wsB : List (BitVec 64) :=
    [BitVec.ofNat 64 (sampled 0), BitVec.ofNat 64 (sampled 1), BitVec.ofNat 64 (sampled 2)]
  let tB := btreeOfWords 0 wsB zeroTree9
  have htB : ∀ i, i < 3 → tB.get i = BitVec.ofNat 64 (sampled i) := fun i hi => by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact (btreeOfWords_get 0 wsB zeroTree9 0 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
    · exact (btreeOfWords_get 0 wsB zeroTree9 1 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
    · exact (btreeOfWords_get 0 wsB zeroTree9 2 (by simp [wsB]) (by simp [wsB])).trans (by simp [wsB])
  let env := mkSegEnv sp row rho (rowPermState rho row 0 2) (rowPermState rho row 1 2)
    (rowPermState rho row 2 2) s tA tB
  rcases mkSegState_matches (cfg := cfgClamp) (hasSeedConsts := true)
    (slots01 := preClamp01Slots) (slots2 := preClamp2Slots)
    (k0 := rowPermState rho row 0 2) (k1 := rowPermState rho row 1 2)
    (k2 := rowPermState rho row 2 2) (tA := tA) (tB := tB)
    (by decide) (by decide) hreg hx22 (fun _ => htA)
    (fun i hi => hs01 i (by simpa [preClamp01Slots] using hi))
    (fun i hi => hs2 i (by simpa [preClamp2Slots] using hi)) with ⟨hm0, htA_eq, htB_eq⟩
  apply with_frozen_env hcl hro
  apply keccakRc_intro hro
  let FF := Seg2ConstsLo sp ∗ memRegion (sp + 2192#64) 1512 ∗
    MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgClamp env stInitClamp0 FF) ?_ ?_
  · dsimp only [stInitClamp0, KSpatial]
    rw [htA_eq, htB_eq]
    dsimp only [KConstsLoOpt, cfgClamp, FF]
    rw [emp_sepConj, multiLaneSampled3_eq_treeMem sp sampled tB
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide)),
      show env.sp = sp from rfl,
      show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
      show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0) := by
    simpa [env, mkSegEnv] using htB 0 (by decide)
  have hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1) := by
    simpa [env, mkSegEnv] using htB 1 (by decide)
  have hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2) := by
    simpa [env, mkSegEnv] using htB 2 (by decide)
  have hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, h]
  have hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  have hr0 : env.rLoop < 24 := show (0 : Nat) < 24 by decide
  have status_setPC : ∀ {st : State} {pc : BitVec 64}, st.status = .Running → (st.setPC pc).status = .Running :=
    fun h => h
  refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 2368) (n := 17) (st' := stInitC1)
    (by omega) (by omega)
    (by rw [BitVec.ofNat_mul 4 2368]; exact pc_of_eq hpc (by decide +kernel)) hrun hm0 runKRange_stInitC1 ?_
  intro s1 hpc1 hrun1 hm1
  have hp1 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm1
    (fun _ _ => rfl) (.var 902) 256#64 (by decide +kernel) rfl
  refine step_bCond_seg2b (w := 2385) (cond := .CC) (disp := 32#64)
    (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc1 (by decide +kernel)) hrun1 ?_ ?_
  · intro hcc
    rw [hp1, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcc
    have hs2lt : sampled 2 < 256 := of_decide_eq_true hcc
    have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
      Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 2 (by decide)) (by omega)
    refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 2393) (n := 4) (st' := stInitCLo)
      (by omega) (by omega) (setPC_disp_w_eq s1 b 2385 32#64 2393 (by decide +kernel)) (status_setPC hrun1)
      (matches_setPC hm1 _) (eq_some_getD _ (by decide +kernel)) ?_
    intro s2 hpc2 hrun2 hm2
    refine step_b_seg2b (w := 2397) (disp := 12#64) (by omega) (by omega) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_
    exact finish_clamp_branch hraw (matches_setPC hm2 _) rfl rfl
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
      hv0 hv1 hv2 hb0 hb1 hb2 false hdone
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_disp_eq s2 b 2397 12#64 0x2580#64 (by decide +kernel))
      (status_setPC hrun2) (by decide +kernel)
  · intro hccF
    rw [hp1, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hccF
    have hs2ge : 256 ≤ sampled 2 := by have := of_decide_eq_false hccF; omega
    refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 2386) (n := 5) (st' := stInitCHi)
      (by omega) (by omega) (setPC_fall_w_eq s1 b 2385 2386 (by decide +kernel)) (status_setPC hrun1)
      (matches_setPC hm1 _) (eq_some_getD _ (by decide +kernel)) ?_
    intro s2 hpc2 hrun2 hm2
    have hp2 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm2
      (fun _ _ => rfl) (.var 901) 256#64 (by decide +kernel) rfl
    refine step_bCond_seg2b (w := 2391) (cond := .CS) (disp := 28#64)
      (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_ ?_
    · intro hcs
      rw [hp2, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcs
      have hs1ge : 256 ≤ sampled 1 := of_decide_eq_true hcs
      refine sepWP_runKRange_seg2b cfgClamp_wf hr0 (w := 2398) (n := 1) (st' := stInitCEnd)
        (by omega) (by omega) (setPC_disp_w_eq s2 b 2391 28#64 2398 (by decide +kernel)) (status_setPC hrun2)
        (matches_setPC hm2 _) (eq_some_getD _ (by decide +kernel)) ?_
      intro s3 hpc3 hrun3 hm3
      have hp3 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm3
        (fun _ _ => rfl) (.var 900) 255#64 (by decide +kernel) rfl
      refine step_bCond_seg2b (w := 2399) (cond := .HI) (disp := BitVec.ofInt 64 (-8976))
        (by omega) (by omega) (by decide +kernel) (pc_add_eq hpc3 (by decide +kernel)) hrun3 ?_ ?_
      · intro hhi
        rw [hp3, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhi
        have hs0ge : 256 ≤ sampled 0 := of_decide_eq_true hhi
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = true :=
          hraw.allLanesDone_iff_ge256.mpr fun i hi => by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption
        exact finish_clamp_branch hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
          hv0 hv1 hv2 hb0 hb1 hb2 true hdone
          (by simp only [↓reduceIte]; exact setPC_disp_eq s3 b 2399 (BitVec.ofInt 64 (-8976)) 0x026c#64 (by decide +kernel))
          (status_setPC hrun3) (by decide +kernel)
      · intro hhiF
        rw [hp3, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhiF
        have hs0lt : sampled 0 < 256 := by have := of_decide_eq_false hhiF; omega
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
          Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 0 (by decide)) (by omega)
        exact finish_clamp_branch hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
          hv0 hv1 hv2 hb0 hb1 hb2 false hdone
          (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_fall_eq s3 b 2399 0x2580#64 (by decide +kernel))
          (status_setPC hrun3) (by decide +kernel)
    · intro hcsF
      rw [hp2, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcsF
      have hs1lt : sampled 1 < 256 := by have := of_decide_eq_false hcsF; omega
      have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
        Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 1 (by decide)) (by omega)
      refine step_b_seg2b (w := 2392) (disp := 32#64) (by omega) (by omega) (by decide +kernel)
        (setPC_fall_w_eq s2 b 2391 2392 (by decide +kernel)) (status_setPC hrun2) ?_
      exact finish_clamp_branch hraw (matches_setPC (matches_setPC hm2 _) _) rfl rfl
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx8)
        hv0 hv1 hv2 hb0 hb1 hb2 false hdone
        (by simp only [Bool.false_eq_true, ↓reduceIte]; exact setPC_disp_eq _ b 2392 32#64 0x2580#64 (by decide +kernel))
        (status_setPC (status_setPC hrun2)) (by decide +kernel)

theorem slotHolds_of_sitePreserved {cfgK : KCfg} {cfgS : RejSiteConfig} {s0 sF : State}
    {pc : BitVec 64} {tA : BTree (BitVec 64) 9} {sl : KSlot} {vLo vHi : BitVec 64}
    (hp : SitePreserved cfgS s0 sF) (hsl : slotHolds cfgK s0 tA sl vLo vHi) :
    slotHolds cfgK (sF.setPC pc) tA sl vLo vHi := by
  have hv : (sF.setPC pc).vregs = s0.vregs := hp.2.2.1
  cases sl with
  | vreg r => exact ⟨hsl.1, by simp [State.readVReg128, VRegFile.read, hv, ← hsl.2]⟩
  | spillQ _ => exact hsl
  | vregLo r => exact ⟨hsl.1, by simp [State.readVReg128, VRegFile.read, hv, ← hsl.2]⟩
  | spillD _ => exact hsl

theorem segRegInv_of_sitePreserved [MlKemPlacement] {cfgS : RejSiteConfig} {sp pc : BitVec 64}
    {row : Nat} {s0 sF : State}
    (hp : SitePreserved cfgS s0 sF)
    (hn8 : Reg.x8 ∉ cfgS.siteClobberedRegs) (hn19 : Reg.x19 ∉ cfgS.siteClobberedRegs)
    (hn20 : Reg.x20 ∉ cfgS.siteClobberedRegs) (hn21 : Reg.x21 ∉ cfgS.siteClobberedRegs)
    (hn22 : Reg.x22 ∉ cfgS.siteClobberedRegs) (hn23 : Reg.x23 ∉ cfgS.siteClobberedRegs)
    (hn24 : Reg.gpr 24#5 ∉ cfgS.siteClobberedRegs) (hn25 : Reg.gpr 25#5 ∉ cfgS.siteClobberedRegs)
    (hn26 : Reg.gpr 26#5 ∉ cfgS.siteClobberedRegs) (hn27 : Reg.gpr 27#5 ∉ cfgS.siteClobberedRegs)
    (hn28 : Reg.x28 ∉ cfgS.siteClobberedRegs)
    (hreg : Seg2RegInv sp s0) (hx8 : s0.readReg64 .x8 = BitVec.ofNat 64 (row + 1))
    (hx22 : s0.readReg64 .x22 = BitVec.ofNat 64 row) :
    Seg2RegInv sp (sF.setPC pc) ∧
      (sF.setPC pc).readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
      (sF.setPC pc).readReg64 .x22 = BitVec.ofNat 64 row := by
  rcases hreg with ⟨hsp, hspA, r19, r20, r21, r23, r24, r25, r26, r27, r28⟩
  have hspF : (sF.setPC pc).sp = sp := hp.2.1.trans hsp
  have hspAF : (sF.setPC pc).spAligned := by
    unfold State.spAligned at hspA ⊢; rwa [hspF, ← hsp]
  refine ⟨⟨hspF, hspAF, (hp.2.2.2 _ hn19).trans r19, (hp.2.2.2 _ hn20).trans r20,
    (hp.2.2.2 _ hn21).trans r21, (hp.2.2.2 _ hn23).trans r23, (hp.2.2.2 _ hn24).trans r24,
    (hp.2.2.2 _ hn25).trans r25, (hp.2.2.2 _ hn26).trans r26, (hp.2.2.2 _ hn27).trans r27,
    (hp.2.2.2 _ hn28).trans r28⟩, (hp.2.2.2 _ hn8).trans hx8, (hp.2.2.2 _ hn22).trans hx22⟩

/-! ## 2. `+0x0504 → +0x0528` Row Header & `B29` `memset` -/

@[expose] def stHdr0 : KState := mkSegState cfgClamp true [] []
@[expose] def stHdr1 : KState := (runKRange cfgClamp 321 8 stHdr0).getD stHdr0

theorem seg2_row_header_memset [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} {row : Nat} {tA : BTree (BitVec 64) 9}
    {Rest : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0528#64) s
      (TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 12448#64) 24 ∗ Rest)
      (fun sf Pf =>
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp sf ∧ sf.readReg64 .x22 = BitVec.ofNat 64 row ∧
        (Pf ⊢ TreeMem (sp + 96#64) 262 tA ∗
          MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗ Rest)) := by
  refine SepWP.seq (mid := b + 0x0524#64)
    (Mid := fun s1 P1 =>
      mlkemMultiLib.CodeLoaded mlkemMpl s1.mem ∧ MlKemRoOk mlkemMpl s1.mem ∧
      Seg2RegInv sp s1 ∧ s1.readReg64 .x22 = BitVec.ofNat 64 row ∧
      s1.readReg64 .x0 = sp + 4272#64 ∧ s1.readReg32 .x1 = 0#32 ∧ s1.readReg64 .x2 = 1632#64 ∧
      P1 = memRegion (sp + 4272#64) 1632 ∗
        (TreeMem (sp + 96#64) 262 tA ∗ MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗ Rest)) ?_ ?_
  · apply with_frozen_env hcl hro
    refine SepWP.congr_pre
      (P1 := memRegion (sp + 12448#64) (8 * 3) ∗
        (TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 4272#64) 1632 ∗ Rest))
      (by apply sepProp_ext <;> sep_frame) ?_
    refine sepWP_elim_treeMem (len := 3) (by decide) fun tB => ?_
    apply keccakRc_intro hro
    let env := mkSegEnv sp (s.readReg64 .x22).toNat rho keccakZeroState keccakZeroState
      keccakZeroState s tA tB
    rcases mkSegState_matches (cfg := cfgClamp) (hasSeedConsts := true) (slots01 := []) (slots2 := [])
      (row := (s.readReg64 .x22).toNat)
      (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState) (tA := tA) (tB := tB)
      (by decide) (by decide) hreg (by simp)
      (fun _ => htA) (by intro _ h; simp at h) (by intro _ h; simp at h) with ⟨hm0, htA0, htB0⟩
    let FF := memRegion (sp + 4272#64) 1632 ∗ Rest
    refine SepWP.congr_pre (P1 := KSpatial cfgClamp env stHdr0 FF) ?_ ?_
    · dsimp only [stHdr0, KSpatial]
      rw [htA0, htB0]
      dsimp only [KConstsLoOpt, cfgClamp, FF]
      rw [emp_sepConj, show env.sp = sp from rfl,
        show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
        show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
        show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl]
      apply sepProp_ext <;> sep_frame
    refine sepWP_runKRange_seg2a cfgClamp_wf (show (0 : Nat) < 24 by decide) (w := 321) (n := 8)
      (st' := stHdr1) (by decide) (by decide) (pc_of_eq hpc (by decide)) hrun hm0
      (eq_some_getD _ (by decide +kernel)) ?_
    intro s1 hpc1 hrun1 hm1
    apply sepWP_drop_left
    have gp := fun (r : BitVec 5) (hr : r ≠ 31#5) (e : KExpr)
        (h : (stHdr1.gprs.get r.toNat).beq e = true)
        (hok : Seg2Init.exprVarsOk (fun _ => true) e = true) =>
      eval_checked_gpr (ok := fun _ => true) (envSpec := env) hm1 (fun _ _ => rfl) r hr e h hok
    have hx1_64 : s1.readReg64 .x1 = 0#64 := by
      simpa [evalKExpr] using gp 1#5 (by decide) (.const64 0#64) (by decide +kernel) rfl
    have hx26_1 : s1.readReg64 (.gpr 26#5) = (sp + 13984#64) + 11#64 := by
      have r := gp 26#5 (by decide) (.spAdd 13995#64) (by decide +kernel) rfl
      dsimp only [evalKExpr, env, mkSegEnv] at r; rw [r]; rw [BitVec.add_assoc]; rfl
    have hmA_eq : evalMemTree env stHdr1.memA = tA := by
      rw [btreeKExprBeq_eq_true (t1 := stHdr1.memA) (t2 := stHdr0.memA) (by decide +kernel)]; exact htA0
    have hmB0 := eval_checked_memB (ok := fun _ => true) (envSpec := env)
      (stEnd := stHdr1) (fun _ _ => rfl) 0 (.const64 0#64) (by decide +kernel) rfl
    have hmB1 := eval_checked_memB (ok := fun _ => true) (envSpec := env)
      (stEnd := stHdr1) (fun _ _ => rfl) 1 (.const64 0#64) (by decide +kernel) rfl
    have hmB2 := eval_checked_memB (ok := fun _ => true) (envSpec := env)
      (stEnd := stHdr1) (fun _ _ => rfl) 2 (.const64 0#64) (by decide +kernel) rfl
    refine SepWP.done (pc_of_eq hpc1 (by decide)) hrun1 fun hcl1 hro1 =>
      ⟨hcl1, hro1, ⟨hm1.hsp, hm1.hsp_al,
        by simpa [evalKExpr, env, mkSegEnv] using gp 19#5 (by decide) (.rcAdd 0#64) (by decide +kernel) rfl,
        by simpa [evalKExpr, env, mkSegEnv] using gp 20#5 (by decide) (.spAdd 4272#64) (by decide +kernel) rfl,
        by simpa [evalKExpr, env, mkSegEnv] using gp 21#5 (by decide) (.spAdd 12448#64) (by decide +kernel) rfl,
        by simpa [evalKExpr, env, mkSegEnv] using gp 23#5 (by decide) (.spAdd 2456#64) (by decide +kernel) rfl,
        by simpa [evalKExpr] using gp 24#5 (by decide) (.const64 544#64) (by decide +kernel) rfl,
        by simpa [evalKExpr, env, mkSegEnv] using gp 25#5 (by decide) (.spAdd 14248#64) (by decide +kernel) rfl,
        hx26_1,
        by simpa [evalKExpr] using gp 27#5 (by decide) (.const64 256#64) (by decide +kernel) rfl,
        by simpa [evalKExpr, env, mkSegEnv] using gp 28#5 (by decide) (.spAdd 13984#64) (by decide +kernel) rfl⟩,
      by simpa [evalKExpr, env, mkSegEnv, hx8] using gp 22#5 (by decide) (.var 101) (by decide +kernel) rfl,
      by simpa [evalKExpr, env, mkSegEnv] using gp 0#5 (by decide) (.spAdd 4272#64) (by decide +kernel) rfl,
      by simp [State.readReg32, hx1_64],
      by simpa [evalKExpr] using gp 2#5 (by decide) (.const64 1632#64) (by decide +kernel) rfl, ?_⟩
    dsimp only [KConstsLoOpt, cfgClamp, FF]
    rw [emp_sepConj, hmA_eq, show env.sp = sp from rfl,
      show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
      show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl,
      ← multiLaneSampled3_eq_treeMem sp (fun _ => 0) _ hmB0 hmB1 hmB2]
    apply sepProp_ext <;> sep_frame
  · rintro s1 P1 hpc1 hrun1 ⟨hcl1, hro1, hreg1, hx22_1, hx0_1, hx1_1, hx2_1, rfl⟩
    apply with_frozen_env hcl1 hro1
    refine (seg2_bl_memset hb hbase s1 sp _ hpc1 hrun1 hreg1 hx0_1 hx1_1 hx2_1 hcl1).mono
      fun sf Pf _ _ ⟨hregF, hx22F, hPf⟩ hclF hroF =>
        ⟨hclF, hroF, hregF, hx22F.trans hx22_1, Entails.trans hPf ?_⟩
    rw [replicate1632_eq_multiLaneSlots0]
    sep_frame

/-! ## 3. 6-Permutation `L1..L6` Symbolic Program & `rowPermState` Identification -/

@[expose] def stInit0 : KState := mkSegState cfgInit true [] []
@[expose] def stAt365 : KState := (runKRange cfgInit 330 35 stInit0).getD stInit0
@[expose] def expL1Lo : List KExpr := slotsL1.map fun sl => (readSlot cfgInit stAt365 sl).1
@[expose] def expL1Hi : List KExpr := slotsL1.map fun sl => (readSlot cfgInit stAt365 sl).2
@[expose] def stPostL1 : KState := (stepKLoopSym cfgInit true 365 196 8#5 slotsL1 2000 stAt365).getD stAt365
@[expose] def stAt605 : KState := (runKRange cfgInit 562 43 stPostL1).getD stPostL1
@[expose] def expL2Lo : List KExpr := slotsL2.map fun sl => (readSlot cfgInit stAt605 sl).1
@[expose] def expVarRange (base : Nat) : List KExpr := (List.range 25).map fun idx => .var (base + idx)
@[expose] def expZero25 : List KExpr := List.replicate 25 (.const64 0#64)

@[expose] def stepsInit : List KProgStep :=
  [.range 330 35,
   .loop true 365 196 8#5 slotsL1 expL1Lo expL1Hi 2000,
   .range 562 43,
   .loop false 605 199 8#5 slotsL2 expL2Lo expZero25 3000,
   .range 805 46,
   .loop true 851 204 8#5 slotsL3 (expVarRange 2000) (expVarRange 2025) 4000,
   .range 1056 31,
   .loop true 1087 202 8#5 slotsL4 (expVarRange 4000) (expVarRange 4025) 5000,
   .range 1290 43,
   .loop false 1333 205 8#5 slotsL5 (expVarRange 3000) expZero25 6000,
   .range 1539 39,
   .loop false 1578 207 8#5 slotsL6 (expVarRange 6000) expZero25 7000,
   .range 1786 377]

private theorem keccakZeroState_getD_eq (k : Nat) : keccakZeroState.getD k 0#64 = 0#64 := by
  unfold keccakZeroState
  by_cases hk : k < 25 <;> simp [Array.getD, hk]

private def preAbsorb_check_ge4 (es : List KExpr) (c : Nat) : Bool :=
  (List.range 3).all fun row =>
    (List.range 25).all fun idx =>
      Nat.blt idx 4 ||
        (exprOnlyVar96 (es.getD idx (.const64 0#64)) &&
          (evalKExpr (envRow row) (es.getD idx (.const64 0#64)) ==
            if Nat.blt idx 21 then
              packLane64 (keccakLastBlock 168 0x1f#8 (rowSeeds (List.replicate 32 0#8) row c)) (8 * idx)
            else 0#64))

private theorem array_getElem_eq_getD64 (a : Array (BitVec 64)) (idx : Nat) (h : idx < a.size) :
    a[idx]'h = a.getD idx 0#64 := by
  simp only [Array.getD, h, ↓reduceDIte]; rfl

private theorem evalExprList25_getD (env : KEnv) (es : List KExpr) (idx : Nat) (hidx : idx < 25) :
    (evalExprList25 env es).getD idx 0#64 = evalKExpr env (es.getD idx (.const64 0#64)) := by
  simp [evalExprList25, Array.getD, hidx]

private theorem preAbsorb_eq_of_checks {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row c : Nat} (hrow : row < 3) {env : KEnv} {es : List KExpr}
    (hv96 : env.vars 96 = BitVec.ofNat 64 row)
    (hvRho : ∀ k, k < 4 → env.vars (100 - k) = ByteSlice.readLE rho (8 * k) 8)
    (hLt4 : (List.range 4).all (fun k => (es.getD k (.const64 0#64)).beq (.var (100 - k))) = true)
    (hGe4 : preAbsorb_check_ge4 es c = true) :
    keccakF1600 (evalExprList25 env es) = rowPermState rho row c 0 := by
  rw [rowPermState_zero rho hrho row c]
  apply congrArg keccakF1600
  apply Array.ext
  · simp [evalExprList25, keccakXorRate21]
  · intro idx hi1 hi2
    have hidx : idx < 25 := by simpa [evalExprList25] using hi1
    rw [array_getElem_eq_getD64 _ idx hi1, evalExprList25_getD env es idx hidx,
        array_getElem_eq_getD64 _ idx hi2]
    by_cases hk4 : idx < 4
    · have hbeq := (List.all_eq_true.mp hLt4) idx (List.mem_range.mpr hk4)
      rw [KExpr.beq_eq_true hbeq, evalKExpr, hvRho idx hk4,
        keccakXorRate21_getD_lt _ _ (by omega), keccakZeroState_getD_eq idx, BitVec.zero_xor,
        lastBlock_rowSeeds_pack_lt4 hrho row c hk4]
    · have hrowChk := (List.all_eq_true.mp hGe4) row (List.mem_range.mpr hrow)
      have hidxChk := (List.all_eq_true.mp hrowChk) idx (List.mem_range.mpr hidx)
      have hbltF : Nat.blt idx 4 = false := Bool.eq_false_iff.mpr (by simp [Nat.blt_eq, hk4])
      rw [hbltF, Bool.false_or, Bool.and_eq_true] at hidxChk
      rw [evalKExpr_eq_envRow hv96 hidxChk.1, beq_iff_eq.mp hidxChk.2]
      by_cases hk21 : idx < 21
      · have hblt21 : Nat.blt idx 21 = true := Nat.blt_eq.mpr hk21
        simp only [hblt21, ↓reduceIte]
        rw [keccakXorRate21_getD_lt _ _ hk21, keccakZeroState_getD_eq idx,
          BitVec.zero_xor, lastBlock_rowSeeds_pack_ge4 hrho row c (by omega)]
      · have hblt21 : Nat.blt idx 21 = false := Bool.eq_false_iff.mpr (by simp [Nat.blt_eq, hk21])
        simp only [hblt21, Bool.false_eq_true, ↓reduceIte]
        rw [keccakXorRate21_getD_ge _ _ (by omega) (by decide), keccakZeroState_getD_eq idx]

theorem evalExprList25_varRange {env : KEnv} {base : Nat} {st : KeccakState}
    (hst : st.size = 25) (hvars : ∀ idx, idx < 25 → env.vars (base + idx) = st.getD idx 0#64) :
    evalExprList25 env (expVarRange base) = st := by
  apply Array.ext
  · simp [evalExprList25, hst]
  · intro idx hi1 hi2
    have hidx : idx < 25 := by simpa [evalExprList25] using hi1
    have hget : (expVarRange base).getD idx (.const64 0#64) = .var (base + idx) := by
      simp [expVarRange, List.getD_eq_getElem?_getD, hidx]
    rw [array_getElem_eq_getD64 _ idx hi1, evalExprList25_getD env _ idx hidx, hget, evalKExpr,
      hvars idx hidx, array_getElem_eq_getD64 st idx hi2]

theorem extendLoopVars_lt {env : KEnv} {b id : Nat} {sLo sHi : KeccakState} (h : id < b) :
    (extendLoopVars env b sLo sHi).vars id = env.vars id := by
  simp only [extendLoopVars, h, ↓reduceIte]

theorem extendLoopVars_lo {env : KEnv} {b idx : Nat} {sLo sHi : KeccakState} (h : idx < 25) :
    (extendLoopVars env b sLo sHi).vars (b + idx) = (keccakF1600 sLo).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + idx < b) by omega, show b + idx < b + 25 by omega,
    show b + idx - b = idx by omega, ↓reduceIte]

theorem extendLoopVars_hi {env : KEnv} {b idx : Nat} {sLo sHi : KeccakState} (h : idx < 25) :
    (extendLoopVars env b sLo sHi).vars (b + 25 + idx) = (keccakF1600 sHi).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + 25 + idx < b) by omega,
    show ¬(b + 25 + idx < b + 25) by omega, show b + 25 + idx < b + 50 by omega,
    show b + 25 + idx - (b + 25) = idx by omega, ↓reduceIte]

theorem specEnv_stepsInit_vars {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row : Nat} (hrow : row < 3) {env0 : KEnv}
    (hv96 : env0.vars 96 = BitVec.ofNat 64 row)
    (hvRho : ∀ k, k < 4 → env0.vars (100 - k) = ByteSlice.readLE rho (8 * k) 8) :
    let envS := specEnvSteps env0 stepsInit
    envS.vars 96 = BitVec.ofNat 64 row ∧
    envS.vars 97 = ByteSlice.readLE rho 24 8 ∧
    envS.vars 98 = ByteSlice.readLE rho 16 8 ∧
    envS.vars 99 = ByteSlice.readLE rho 8 8 ∧
    envS.vars 100 = ByteSlice.readLE rho 0 8 ∧
    (∀ idx, idx < 25 → envS.vars (2000 + idx) = (rowPermState rho row 0 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (2025 + idx) = (rowPermState rho row 1 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3000 + idx) = (rowPermState rho row 2 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4000 + idx) = (rowPermState rho row 0 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4025 + idx) = (rowPermState rho row 1 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5000 + idx) = (rowPermState rho row 0 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5025 + idx) = (rowPermState rho row 1 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (6000 + idx) = (rowPermState rho row 2 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (7000 + idx) = (rowPermState rho row 2 2).getD idx 0#64) := by
  dsimp only [stepsInit, specEnvSteps]
  let e1 := extendLoopVars env0 2000 (evalExprList25 env0 expL1Lo) (evalExprList25 env0 expL1Hi)
  have hp10 : keccakF1600 (evalExprList25 env0 expL1Lo) = rowPermState rho row 0 0 :=
    preAbsorb_eq_of_checks hrho hrow hv96 hvRho (by decide +kernel) (by decide +kernel)
  have hp11 : keccakF1600 (evalExprList25 env0 expL1Hi) = rowPermState rho row 1 0 :=
    preAbsorb_eq_of_checks hrho hrow hv96 hvRho (by decide +kernel) (by decide +kernel)
  have he1_lt : ∀ id, id < 2000 → e1.vars id = env0.vars id :=
    fun id h => by simp [e1, extendLoopVars, h]
  let e2 := extendLoopVars e1 3000 (evalExprList25 e1 expL2Lo) (evalExprList25 e1 expZero25)
  have hp20 : keccakF1600 (evalExprList25 e1 expL2Lo) = rowPermState rho row 2 0 :=
    preAbsorb_eq_of_checks hrho hrow (by rw [he1_lt 96 (by decide), hv96])
      (fun k hk => by rw [he1_lt _ (by omega), hvRho k hk]) (by decide +kernel) (by decide +kernel)
  let e3 := extendLoopVars e2 4000 (evalExprList25 e2 (expVarRange 2000)) (evalExprList25 e2 (expVarRange 2025))
  have hp30 : keccakF1600 (evalExprList25 e2 (expVarRange 2000)) = rowPermState rho row 0 1 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 0 0) fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lo h, hp10], rowPermState_succ]
  have hp31 : keccakF1600 (evalExprList25 e2 (expVarRange 2025)) = rowPermState rho row 1 1 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 1 0) fun idx h => by
      rw [extendLoopVars_lt (by omega), show 2025 + idx = 2000 + 25 + idx from rfl,
        extendLoopVars_hi h, hp11], rowPermState_succ]
  let e4 := extendLoopVars e3 5000 (evalExprList25 e3 (expVarRange 4000)) (evalExprList25 e3 (expVarRange 4025))
  have hp40 : keccakF1600 (evalExprList25 e3 (expVarRange 4000)) = rowPermState rho row 0 2 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 0 1) fun idx h => by
      rw [extendLoopVars_lo h, hp30], rowPermState_succ]
  have hp41 : keccakF1600 (evalExprList25 e3 (expVarRange 4025)) = rowPermState rho row 1 2 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 1 1) fun idx h => by
      rw [show 4025 + idx = 4000 + 25 + idx from rfl, extendLoopVars_hi h, hp31], rowPermState_succ]
  let e5 := extendLoopVars e4 6000 (evalExprList25 e4 (expVarRange 3000)) (evalExprList25 e4 expZero25)
  have hp50 : keccakF1600 (evalExprList25 e4 (expVarRange 3000)) = rowPermState rho row 2 1 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 2 0) fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lo h, hp20],
      rowPermState_succ]
  let e6 := extendLoopVars e5 7000 (evalExprList25 e5 (expVarRange 6000)) (evalExprList25 e5 expZero25)
  have hp60 : keccakF1600 (evalExprList25 e5 (expVarRange 6000)) = rowPermState rho row 2 2 := by
    rw [evalExprList25_varRange (Seg2Init.rowPermState_size hrho row 2 1) fun idx h => by
      rw [extendLoopVars_lo h, hp50], rowPermState_succ]
  change e6.vars 96 = _ ∧ _
  have hlt3000 : ∀ id, id < 3000 → e6.vars id = e1.vars id := fun id h => by
    rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lt (by omega),
      extendLoopVars_lt (by omega), extendLoopVars_lt h]
  have hlt2000 : ∀ id, id < 2000 → e6.vars id = env0.vars id := fun id h => by
    rw [hlt3000 id (by omega), extendLoopVars_lt h]
  refine ⟨by rw [hlt2000 96 (by decide), hv96],
    by simpa using (hlt2000 97 (by decide)).trans (hvRho 3 (by decide)),
    by simpa using (hlt2000 98 (by decide)).trans (hvRho 2 (by decide)),
    by simpa using (hlt2000 99 (by decide)).trans (hvRho 1 (by decide)),
    by simpa using (hlt2000 100 (by decide)).trans (hvRho 0 (by decide)),
    fun idx h => by rw [hlt3000 _ (by omega), extendLoopVars_lo h, hp10],
    fun idx h => by rw [hlt3000 _ (by omega), show 2025 + idx = 2000 + 25 + idx from rfl, extendLoopVars_hi h, hp11],
    fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lt (by omega),
        extendLoopVars_lt (by omega), extendLoopVars_lo h, hp20],
    fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lo h, hp30],
    fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lt (by omega),
        show 4025 + idx = 4000 + 25 + idx from rfl, extendLoopVars_hi h, hp31],
    fun idx h => by rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega), extendLoopVars_lo h, hp40],
    fun idx h => by
      rw [extendLoopVars_lt (by omega), extendLoopVars_lt (by omega),
        show 5025 + idx = 5000 + 25 + idx from rfl, extendLoopVars_hi h, hp41],
    fun idx h => by rw [extendLoopVars_lt (by omega), extendLoopVars_lo h, hp50],
    fun idx h => by rw [extendLoopVars_lo h, hp60]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit
