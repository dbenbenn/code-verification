/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Extra-Block While Body (`Seg2Extra`)

Proves `seg2_extra_bodyA_ok` (`+0x29ac → +0x3374`, 1-block 4-lane `L7`/`L8` squeeze) and
`seg2_extra_bodyB_ok` (`+0x3374 → +0x3770 / +0x29ac`, `step_rej_site_extra1` + post-site clamp).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Extra

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakAbsorb keccakF1600 keccakPermuteN shake128BlockAt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  SitePreserved decBallNotMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone step_rej_site_extra1
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  condCC_256_of_le271 raw_sampled_le271
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blkPC07 blkPl07 fetchWordTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KEnv KExpr KSlot KState evalKExpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMem_entails_memRegion KSpatial KStateMatches SepWP.of_memRegion_btreeMem
  blk07NoRelocInRange btreeBytesFrom btreeBytesFrom_length evalMemTree
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  btreeBytesFrom_eq_extractRate_21 rejBufReadable_of_btreeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast (
  runAndCheckKProg_of_fast
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memB extendLoopVars exprVarsOk
  rowSeed runAndCheckKProg sepWP_of_runAndCheckKProg specEnvSteps
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowCalleeGprs RowExitState RowExtraState RowMidState cfgC cfgC_valid
  fetches_rejExtra1_inner fetches_rejExtra1_outer rejCfgExtra1 rejCfgExtra1_valid
  slotsInv01 slotsInv23 slotsL7 slotsL8 slotsMidExtra01 slotsMidExtra23
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  checkCalleeGprsPreserved checkHeaderPreserved checkOutSlots
  checked_calleeGprs checked_headerOk checked_outSlots
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB (
  envInitB evalExprList25_slotExprs keccakAbsorb_rowSeed_size keccakPermuteN_size
  keccakPermuteN_succ_right slotExprsHi slotExprsLo stRawB stRawB_matches
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp (
  ClampState cfgClamp cfgClamp_valid checkClampCommon condLS_255_of_le271 csInitClamp
  envClamp envClamp_valid runClampRange sepWP_of_runClampRange sitePreserved_row stRawClamp_matches
  step_bCond_seg2 step_b_seg2
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init (
  allLanesDone4_false_of_lt256 allLanesDone4_true_of_ge256 checkClampFull clampMatches_setPC
  eval_envClamp_800 finish_clamp_exit finish_clamp_loop with_frozen_env
)

attribute [local irreducible] blkPC07 mlkemMultiLib keccakF1600 keccakAbsorb BTreeMem allLanesDone

private theorem status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
private theorem mem_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
private theorem sp_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := rfl
private theorem vregs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).vregs = s.vregs := rfl
private theorem spAligned_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := rfl
private theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl
private theorem rowCalleeGprs_setPC [MlKemPlacement] {sp rcBase : BitVec 64} {row : Nat}
    {s : State} (pc : BitVec 64) (hg : RowCalleeGprs sp rcBase row s) :
    RowCalleeGprs sp rcBase row (s.setPC pc) := hg
private theorem slotHolds_setPC {cfg : KeccakSymDefs.KCfg} {s : State} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {vLo vHi : BitVec 64} (pc : BitVec 64)
    (h : slotHolds cfg s tA sl vLo vHi) : slotHolds cfg (s.setPC pc) tA sl vLo vHi := h

/-! ## 1. Extra-Block Body A (`+0x29ac → +0x3374`, `L7`–`L8` 1-Block Squeeze) -/

private def stepsExtraA : List KProgStep :=
  [.range 2667 19,
   .loop 2686 205 8#5 slotsL7 (slotExprsLo cfgC stRawB slotsInv01) (slotExprsHi cfgC stRawB slotsInv01) 2000,
   .range 2892 83,
   .loop 2975 206 10#5 slotsL8 (slotExprsLo cfgC stRawB slotsInv23) (slotExprsHi cfgC stRawB slotsInv23) 3000,
   .range 3182 106]

private def expMemBExtra1 (c j : Nat) : KExpr :=
  match c with
  | 0 => .var (2000 + j)
  | 1 => .var (2025 + j)
  | 2 => .var (3000 + j)
  | _ => .var (3025 + j)

private def chkMemBExtra1 (ok : Nat → Bool) (st : KState) : Bool :=
  (List.range 4).all fun c => (List.range 21).all fun j =>
    let e := expMemBExtra1 c j
    (st.memB.get (21 * c + j)).beq e && exprVarsOk ok e

private def chkExtraA (ok : Nat → Bool) (st : KState) : Bool :=
  (st.gprs.get 1).beq (.var 66) && exprVarsOk ok (.var 66) &&
  (st.gprs.get 10).beq (.const64 0#64) && exprVarsOk ok (.const64 0#64) &&
  (st.gprs.get 8).beq (.spAdd 26779#64) && exprVarsOk ok (.spAdd 26779#64) &&
  checkHeaderPreserved ok st && checkCalleeGprsPreserved ok st && chkMemBExtra1 ok st &&
  checkOutSlots cfgC ok st slotsMidExtra01 2000 && checkOutSlots cfgC ok st slotsMidExtra23 3000

private theorem cert_extraA :
    runAndCheckKProg cfgC 2667 3288 2667 3288 1600 stepsExtraA stRawB chkExtraA = true :=
  runAndCheckKProg_of_fast (by decide +kernel)

private theorem nr_extra_clamp : blk07NoRelocInRange 3288 3549 = true := by rfl_kernel
private theorem fw_3288 : fetchWordTree07 3288 = some (.b 20#64) := by rfl_kernel

theorem seg2_extra_bodyA_ok [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) {rho : List (BitVec 8)} {row extra : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) {st : State} {P : SepProp}
    (hpre : RowExtraState b sp rcBase rho row Rest extra st P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (pcAt (b + BitVec.ofNat 64 (4 * 3289)) 4) st P
      (RowMidState sp rcBase rho row Rest extra) := by
  rcases hpre with ⟨hpc, hrun, hsp, hspA, hsp16, hcl, hro, hgprs, hx1,
    tA0, sampled, hws, hhdr0, hsl01, hsl23, hinv, hP⟩
  refine with_frozen_env hcl hro ?_
  refine SepWP.weaken_pre hP ?_
  refine SepWP.of_memRegion_btreeMem 84 (sp + 26768#64) (by decide) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun tB0 => ?_
  rcases stRawB_matches hsp hspA hgprs hhdr0 (tB := tB0) with ⟨hm0, htA0, htB0⟩
  let env0 := envInitB sp rcBase rho row st tA0 tB0
  change KStateMatches env0 stRawB st at hm0
  change evalMemTree env0 stRawB.memA = tA0 at htA0
  change evalMemTree env0 stRawB.memB = tB0 at htB0
  have henvSp : env0.sp = sp := rfl
  have henvRc : env0.rcBase = rcBase := rfl
  have hspEnt :
      (BTreeMem (sp + 26768#64) 84 tB0 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
        MultiLaneSampled (sp + 24720#64) 4 sampled ∗
        MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
        memRegion (sp + 28848#64) 2016 ∗ Rest)) ⊢
      KSpatial cfgC env0 stRawB (MultiLaneSampled (sp + 24720#64) 4 sampled ∗
        MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
        memRegion (sp + 28848#64) 2016 ∗ Rest) := by
    simp only [KSpatial, cfgC, henvSp, henvRc, htA0, htB0]; sep_frame
  refine SepWP.weaken_pre hspEnt ?_
  have hpc' : st.pc = b + BitVec.ofNat 64 (4 * 2667) := by simpa using hpc
  refine sepWP_of_runAndCheckKProg cfgC_valid (env0 := env0) (show 0 < 24 by decide) cert_extraA hm0 hpc' hrun ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _ heval hmF hchk
  simp only [chkExtraA, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx1_eq, hx1_ok⟩, hx10_eq⟩, hx10_ok⟩, hx8_eq⟩, hx8_ok⟩,
    hhdr_chk⟩, hgpr_chk⟩, hmemB_chk⟩, hout01⟩, hout23⟩
  let sk (col : Nat) := keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row col))
  have hkSz (col : Nat) : (sk col).size = 25 :=
    keccakPermuteN_size (extra + 2) (keccakAbsorb_rowSeed_size hrho row col)
  have hlt800_01 : evalExprList25 env0 (slotExprsLo cfgC stRawB slotsInv01) = sk 0 ∧
      evalExprList25 env0 (slotExprsHi cfgC stRawB slotsInv01) = sk 1 :=
    evalExprList25_slotExprs hm0 htA0 (fun _ _ => rfl) (by decide) (by decide) rfl
      (hkSz 0) (hkSz 1) hsl01
  let env1 := extendLoopVars env0 2000 (sk 0) (sk 1)
  have hsub1 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true → evalKExpr env1 e = evalKExpr env0 e :=
    Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid; simp [env1, extendLoopVars, show id < 2000 by omega]
  have hlt800_23 : evalExprList25 env1 (slotExprsLo cfgC stRawB slotsInv23) = sk 2 ∧
      evalExprList25 env1 (slotExprsHi cfgC stRawB slotsInv23) = sk 3 :=
    evalExprList25_slotExprs hm0 htA0 hsub1 (by decide) (by decide) rfl
      (hkSz 2) (hkSz 3) hsl23
  let env2 := extendLoopVars env1 3000 (sk 2) (sk 3)
  have hspecEq : specEnvSteps env0 stepsExtraA = env2 := by
    simp only [stepsExtraA, specEnvSteps, hlt800_01.1, hlt800_01.2]
    change specEnvSteps env1 [.range 2892 83,
      .loop 2975 206 10#5 slotsL8 (slotExprsLo cfgC stRawB slotsInv23) (slotExprsHi cfgC stRawB slotsInv23) 3000,
      .range 3182 106] = env2
    simp only [specEnvSteps, hlt800_23.1, hlt800_23.2]; rfl
  have hsub2 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (specEnvSteps env0 stepsExtraA) e = evalKExpr env0 e := by
    rw [hspecEq]
    exact Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid
      simp [env2, env1, extendLoopVars, show id < 3000 by omega, show id < 2000 by omega]
  have hspecSp : (specEnvSteps env0 stepsExtraA).sp = sp := by rw [hspecEq]; rfl
  have hspecRc : (specEnvSteps env0 stepsExtraA).rcBase = rcBase := by rw [hspecEq]; rfl
  have hspec64 : (specEnvSteps env0 stepsExtraA).vars 64 = BitVec.ofNat 64 row :=
    (hsub2 (.var 64) (by decide)).trans rfl
  have hspec66 : (specEnvSteps env0 stepsExtraA).vars 66 = BitVec.ofNat 64 (row + 1) :=
    (hsub2 (.var 66) (by decide)).trans hx1
  have hx1F := eval_checked_gpr hmF heval 1#5 (by decide) (.var 66) hx1_eq hx1_ok
  have hx10F := eval_checked_gpr hmF heval 10#5 (by decide) (.const64 0#64) hx10_eq hx10_ok
  have hx8F := eval_checked_gpr hmF heval 8#5 (by decide) (.spAdd 26779#64) hx8_eq hx8_ok
  have hhdrF := checked_headerOk heval hspecSp
    ((hsub2 (.var 100) (by decide)).trans rfl)
    ((hsub2 (.var 101) (by decide)).trans rfl)
    ((hsub2 (.var 102) (by decide)).trans rfl)
    ((hsub2 (.var 103) (by decide)).trans rfl) hhdr_chk
  have hgprsF := checked_calleeGprs hmF heval hspecSp hspecRc hspec64 hgpr_chk
  have hslOut01 := checked_outSlots hmF heval (by decide) (by decide) hout01
  have hslOut23 := checked_outSlots hmF heval (by decide) (by decide) hout23
  refine step_b_seg2 (disp := 20#64) nr_extra_clamp (by decide) (by decide) (by decide)
    fw_3288 hpcF hrunF ?_
  have hpcMid : (sf.setPC (b + BitVec.ofNat 64 (4 * 3288) + 20#64)).pc =
      pcAt (b + BitVec.ofNat 64 (4 * 3289)) 4 := by dsimp only [State.setPC, pcAt]; bv_omega
  refine SepWP.done hpcMid ((status_setPC sf _).trans hrunF) fun hclM hroM => ?_
  have hstep3 (col : Nat) : keccakF1600 (sk col) =
      keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row col)) := by
    simpa [sk, Nat.add_assoc] using keccakPermuteN_succ_right (extra + 2)
      (keccakAbsorb 21 0x1f#8 (rowSeed rho row col))
  refine ⟨(sp_setPC sf _).trans (hmF.hsp.trans hspF), (spAligned_setPC sf _).trans hmF.hsp_al,
    hsp16, hclM, hroM, rowCalleeGprs_setPC _ hgprsF,
    (readReg64_setPC sf _ .x1).trans (by simpa [Reg.x1, evalKExpr, hspec66] using hx1F),
    (readReg64_setPC sf _ .x10).trans (by simpa [Reg.x10, evalKExpr] using hx10F),
    (readReg64_setPC sf _ .x8).trans (by simpa [Reg.x8, evalKExpr, hspecSp] using hx8F),
    evalMemTree envFinal stEnd.memA, evalMemTree envFinal stEnd.memB, sampled, hws, hhdrF,
    ?_, ?_, ?_, hinv.toRaw, ?_⟩
  · intro c hc
    refine btreeBytesFrom_eq_extractRate_21 fun j hj => ?_
    have h1 := List.all_eq_true.mp hmemB_chk c (List.mem_range.mpr hc)
    have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
    rcases Bool.and_eq_true _ _ |>.mp h2 with ⟨heq, hok⟩
    have hmB := eval_checked_memB heval _ _ heq hok
    rw [hmB, hspecEq]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · simp [expMemBExtra1, evalKExpr, env2, env1, extendLoopVars, hstep3 0,
        show 2000 + j < 3000 by omega, show ¬(2000 + j < 2000) by omega, show 2000 + j < 2000 + 25 by omega]
    · simp [expMemBExtra1, evalKExpr, env2, env1, extendLoopVars, hstep3 1,
        show 2025 + j < 3000 by omega, show ¬(2025 + j < 2000) by omega,
        show ¬(2025 + j < 2000 + 25) by omega, show 2025 + j < 2000 + 50 by omega,
        show 2025 + j - (2000 + 25) = j by omega]
    · simp [expMemBExtra1, evalKExpr, env2, extendLoopVars, hstep3 2,
        show ¬(3000 + j < 3000) by omega, show 3000 + j < 3000 + 25 by omega]
    · simp [expMemBExtra1, evalKExpr, env2, extendLoopVars, hstep3 3,
        show ¬(3025 + j < 3000) by omega, show ¬(3025 + j < 3000 + 25) by omega,
        show 3025 + j < 3000 + 50 by omega, show 3025 + j - (3000 + 25) = j by omega]
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsExtraA).vars (2000 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, env1, extendLoopVars, hstep3 0,
        show 2000 + idx < 3000 by omega, show ¬(2000 + idx < 2000) by omega, show 2000 + idx < 2000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsExtraA).vars (2000 + 25 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, env1, extendLoopVars, hstep3 1,
        show 2000 + 25 + idx < 3000 by omega, show ¬(2000 + 25 + idx < 2000) by omega,
        show ¬(2000 + 25 + idx < 2000 + 25) by omega, show 2000 + 25 + idx < 2000 + 50 by omega]
    exact slotHolds_setPC _ (by simpa [hvLo, hvHi] using hslOut01 idx hidx)
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsExtraA).vars (3000 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, extendLoopVars, hstep3 2,
        show ¬(3000 + idx < 3000) by omega, show 3000 + idx < 3000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsExtraA).vars (3000 + 25 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, extendLoopVars, hstep3 3,
        show ¬(3000 + 25 + idx < 3000) by omega, show ¬(3000 + 25 + idx < 3000 + 25) by omega,
        show 3000 + 25 + idx < 3000 + 50 by omega]
    exact slotHolds_setPC _ (by simpa [hvLo, hvHi] using hslOut23 idx hidx)
  · simp only [KSpatial, cfgC, hspF, hrcF, henvSp, henvRc]; sep_frame

/-! ## 2. Extra-Block Body B (`+0x3374 → +0x3770 / +0x29ac`, `step_rej_site_extra1` + Clamp) -/

private def csExtra3541 : ClampState := (runClampRange cfgClamp 3493 48 csInitClamp).getD csInitClamp
private def csExtra3543 : ClampState := (runClampRange cfgClamp 3542 1 csExtra3541).getD csInitClamp
private def csExtra3545 : ClampState := (runClampRange cfgClamp 3544 1 csExtra3543).getD csInitClamp
private def csExtra3547 : ClampState := (runClampRange cfgClamp 3546 1 csExtra3545).getD csInitClamp

private theorem run_extra3541 : runClampRange cfgClamp 3493 48 csInitClamp = some csExtra3541 := by rfl_kernel
private theorem cmp_extra3541 : csExtra3541.cmpOpt = some (.var 803, 256#64) := by rfl_kernel
private theorem chk_extra3541 : checkClampFull slotsMidExtra01 slotsMidExtra23 csExtra3541.st = true := by rfl_kernel
private theorem run_extra3543 : runClampRange cfgClamp 3542 1 csExtra3541 = some csExtra3543 := by rfl_kernel
private theorem cmp_extra3543 : csExtra3543.cmpOpt = some (.var 802, 256#64) := by rfl_kernel
private theorem chk_extra3543 : checkClampFull slotsMidExtra01 slotsMidExtra23 csExtra3543.st = true := by rfl_kernel
private theorem run_extra3545 : runClampRange cfgClamp 3544 1 csExtra3543 = some csExtra3545 := by rfl_kernel
private theorem cmp_extra3545 : csExtra3545.cmpOpt = some (.var 801, 256#64) := by rfl_kernel
private theorem chk_extra3545 : checkClampFull slotsMidExtra01 slotsMidExtra23 csExtra3545.st = true := by rfl_kernel
private theorem run_extra3547 : runClampRange cfgClamp 3546 1 csExtra3545 = some csExtra3547 := by rfl_kernel
private theorem cmp_extra3547 : csExtra3547.cmpOpt = some (.var 800, 255#64) := by rfl_kernel
private theorem chk_extra3547 : checkClampFull slotsMidExtra01 slotsMidExtra23 csExtra3547.st = true := by rfl_kernel
private theorem chk_extra3547_common : checkClampCommon csExtra3547.st = true := by rfl_kernel

private theorem fw_3541 : fetchWordTree07 3541 = some (.bCond .CC (-(3496#64))) := by rfl_kernel
private theorem fw_3543 : fetchWordTree07 3543 = some (.bCond .CC (-(3504#64))) := by rfl_kernel
private theorem fw_3545 : fetchWordTree07 3545 = some (.bCond .CC (-(3512#64))) := by rfl_kernel
private theorem fw_3547 : fetchWordTree07 3547 = some (.bCond .LS (-(3520#64))) := by rfl_kernel

attribute [local irreducible] csExtra3541 csExtra3543 csExtra3545 csExtra3547

private theorem step_post_extra1_clamp [MlKemPlacement] {b sp rcBase : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 3493)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hsl01 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slotsMidExtra01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hsl23 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slotsMidExtra23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) (extra + 1) sampled' hws') :
    let F := MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      s ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗ (MultiLaneSampled (sp + 24720#64) 4 sampled' ∗ F)))
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
          RowExitState sp rcBase rho row Rest sf Pf
        else RowExtraState b sp rcBase rho row Rest (extra + 1) sf Pf) := by
  intro F
  have hsamp271 : ∀ c, c < 4 → sampled' c ≤ 271 := fun c hc => raw_sampled_le271 hraw hc
  have henvV := envClamp_valid (sp := sp) (rcBase := rcBase) (rho := rho) (row := row)
    (s := s) (tA := tA) hsamp271
  obtain ⟨hm0, hspEq0⟩ := stRawClamp_matches (sampled' := sampled') hsp hspA hgprs hhdr F
  rw [← hspEq0]
  have hloop : ∀ {csEnd : ClampState} {sf : State},
      allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) = false →
      checkClampFull slotsMidExtra01 slotsMidExtra23 csEnd.st = true →
      sf.pc = b + BitVec.ofNat 64 (4 * 2667) → sf.status = .Running →
      Seg2Clamp.ClampMatches (envClamp sp rcBase rho row s tA sampled') csEnd sf →
      SepWP (blkPC07.rebase b (fun _ => none))
        (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 3548)
         else b + BitVec.ofNat 64 (4 * 2667))
        sf (KSpatial cfgClamp (envClamp sp rcBase rho row s tA sampled') csEnd.st F)
        (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
          if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
            RowExitState sp rcBase rho row Rest sf' Pf
          else RowExtraState b sp rcBase rho row Rest (extra + 1) sf' Pf) := fun hd hc hp hr hm =>
    finish_clamp_loop (extra := extra + 1) (Rest := Rest) hsp hspA hsp16 hgprs hhdr hx1
      (by decide) rfl (by decide) rfl hsl01 hsl23 hraw hd hc hp hr hm
  refine with_frozen_env hcl hro ?_
  refine sepWP_of_runClampRange cfgClamp_valid henvV 48 3493 nr_extra_clamp (by decide)
    (by decide) (by decide) run_extra3541 hm0 hpc hrun fun s1 hpc1 hrun1 hm1 => ?_
  refine step_bCond_seg2 (cond := .CC) (disp := -(3496#64)) nr_extra_clamp (by decide) (by decide)
    (by decide) fw_3541 hpc1 hrun1 (fun hT3 => ?_) (fun hF3 => ?_)
  · have hlt3 : sampled' 3 < 256 := by
      have hp := hm1.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3541] at hp
      rw [eval_envClamp_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_true_eq] at hT3; exact hT3
    exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt3) chk_extra3541
      (by dsimp only [State.setPC]; bv_omega) ((status_setPC s1 _).trans hrun1)
      (clampMatches_setPC _ hm1)
  · have hge3 : 256 ≤ sampled' 3 := by
      have hp := hm1.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3541] at hp
      rw [eval_envClamp_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_false_iff_not] at hF3; omega
    refine sepWP_of_runClampRange cfgClamp_valid henvV 1 3542 nr_extra_clamp (by decide)
      (by decide) (by decide) run_extra3543 (clampMatches_setPC _ hm1)
      (by dsimp only [State.setPC]) ((status_setPC s1 _).trans hrun1) fun s2 hpc2 hrun2 hm2 => ?_
    refine step_bCond_seg2 (cond := .CC) (disp := -(3504#64)) nr_extra_clamp (by decide) (by decide)
      (by decide) fw_3543 hpc2 hrun2 (fun hT2 => ?_) (fun hF2 => ?_)
    · have hlt2 : sampled' 2 < 256 := by
        have hp := hm2.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3543] at hp
        rw [eval_envClamp_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_true_eq] at hT2; exact hT2
      exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt2) chk_extra3543
        (by dsimp only [State.setPC]; bv_omega) ((status_setPC s2 _).trans hrun2)
        (clampMatches_setPC _ hm2)
    · have hge2 : 256 ≤ sampled' 2 := by
        have hp := hm2.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3543] at hp
        rw [eval_envClamp_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_false_iff_not] at hF2; omega
      refine sepWP_of_runClampRange cfgClamp_valid henvV 1 3544 nr_extra_clamp (by decide)
        (by decide) (by decide) run_extra3545 (clampMatches_setPC _ hm2)
        (by dsimp only [State.setPC]) ((status_setPC s2 _).trans hrun2) fun s3 hpc3 hrun3 hm3 => ?_
      refine step_bCond_seg2 (cond := .CC) (disp := -(3512#64)) nr_extra_clamp (by decide) (by decide)
        (by decide) fw_3545 hpc3 hrun3 (fun hT1 => ?_) (fun hF1 => ?_)
      · have hlt1 : sampled' 1 < 256 := by
          have hp := hm3.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3545] at hp
          rw [eval_envClamp_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_true_eq] at hT1; exact hT1
        exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt1) chk_extra3545
          (by dsimp only [State.setPC]; bv_omega) ((status_setPC s3 _).trans hrun3)
          (clampMatches_setPC _ hm3)
      · have hge1 : 256 ≤ sampled' 1 := by
          have hp := hm3.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3545] at hp
          rw [eval_envClamp_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_false_iff_not] at hF1; omega
        refine sepWP_of_runClampRange cfgClamp_valid henvV 1 3546 nr_extra_clamp (by decide)
          (by decide) (by decide) run_extra3547 (clampMatches_setPC _ hm3)
          (by dsimp only [State.setPC]) ((status_setPC s3 _).trans hrun3) fun s4 hpc4 hrun4 hm4 => ?_
        refine step_bCond_seg2 (cond := .LS) (disp := -(3520#64)) nr_extra_clamp (by decide) (by decide)
          (by decide) fw_3547 hpc4 hrun4 (fun hT0 => ?_) (fun hF0 => ?_)
        · have hlt0 : sampled' 0 < 256 := by
            have hp := hm4.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3547] at hp
            rw [eval_envClamp_800 (c := 0) (by decide)] at hp
            rw [hp, condLS_255_of_le271 (hsamp271 0 (by decide)), decide_eq_true_eq] at hT0; exact hT0
          exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt0) chk_extra3547
            (by dsimp only [State.setPC]; bv_omega) ((status_setPC s4 _).trans hrun4)
            (clampMatches_setPC _ hm4)
        · have hge0 : 256 ≤ sampled' 0 := by
            have hp := hm4.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_extra3547] at hp
            rw [eval_envClamp_800 (c := 0) (by decide)] at hp
            rw [hp, condLS_255_of_le271 (hsamp271 0 (by decide)), decide_eq_false_iff_not] at hF0; omega
          have hdT := allLanesDone4_true_of_ge256 hraw hge0 hge1 hge2 hge3
          exact finish_clamp_exit (Rest := Rest) hsp16 hx1 hraw hdT chk_extra3547_common
            (by dsimp only [State.setPC]) ((status_setPC s4 _).trans hrun4)
            (clampMatches_setPC _ hm4)

theorem seg2_extra_bodyB_ok [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) {rho : List (BitVec 8)} {row extra : Nat} {Rest : SepProp}
    {sm : State} {Pm : SepProp}
    (hpc : sm.pc = pcAt (b + BitVec.ofNat 64 (4 * 3289)) 4) (hrun : sm.status = .Running)
    (hmid : RowMidState sp rcBase rho row Rest extra sm Pm) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      sm Pm
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
          RowExitState sp rcBase rho row Rest sf Pf
        else RowExtraState b sp rcBase rho row Rest (extra + 1) sf Pf) := by
  rcases hmid with ⟨hsp, hspA, hsp16, hcl, hro, hgprs, hx1, hx10, hx8,
    tA, tB, sampled, hws, hhdr, hsq, hsl01, hsl23, hraw0, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hsite : SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 3493)) sm
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        BTreeMem (sp + 26768#64) 84 tB ∗ MultiLaneSampled (sp + 24720#64) 4 sampled ∗
        MultiLaneSlots (sp + 2560#64) 544 4 hws ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)
      (fun s1 P1 =>
        SitePreserved rejCfgExtra1 sm s1 ∧
        ∃ sampled' hws',
          MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) (extra + 1) sampled' hws' ∧
          (P1 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (sp + 144#64) 286 tA ∗
              (MultiLaneSampled (sp + 24720#64) 4 sampled' ∗
                (MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
                  memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest))))) := by
    refine SepWP.weaken_pre (by sep_frame : _ ⊢ BTreeMem (sp + 26768#64) 84 tB ∗
      (MultiLaneSampled (sp + 24720#64) 4 sampled ∗
        (MultiLaneSlots (sp + 2560#64) 544 4 hws ∗
          ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
            memRegion (sp + 28848#64) 2016 ∗ Rest)))) ?_
    refine step_rej_site_extra1 (pcBase := b + BitVec.ofNat 64 (4 * 3289))
      (sqBase := sp + 26768#64) (sampBase := sp + 24720#64)
      (slotsBase := sp + 2560#64) (cfg := rejCfgExtra1)
      (seeds := fun c => rowSeed rho row c) (bufs := fun c => btreeBytesFrom (21 * c) 21 tB)
      hpc hrun rejCfgExtra1_valid rfl
      (fetches_rejExtra1_outer b) (fetches_rejExtra1_inner b)
      (fun i hi => rejBufReadable_of_btreeMem (offWords := 21 * i)
        (by dsimp only [rejCfgExtra1]; bv_omega) (by dsimp only [rejCfgExtra1] at hi ⊢; omega) rfl)
      (fun i _ => by rw [btreeBytesFrom_length]; decide)
      (fun i hi => by
        have hlen : (btreeBytesFrom (21 * i) 21 tB).length = 168 := by rw [btreeBytesFrom_length]
        rw [List.take_of_length_le (by omega)]
        exact hsq i (by dsimp only [rejCfgExtra1] at hi; exact hi))
      hraw0 hx10 (by dsimp only [rejCfgExtra1]; rw [hx8]; bv_omega)
      hgprs.2.2.2.2.2.2.2.1 hgprs.2.2.2.2.2.2.2.2.1 hgprs.1
      fun sF sampled' hws' hp hraw => ?_
    have hpcF : (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 3289)) 204)).pc =
        b + BitVec.ofNat 64 (4 * 3493) := by dsimp only [State.setPC, pcAt]; bv_omega
    have hp1 : SitePreserved rejCfgExtra1 sm (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 3289)) 204)) :=
      ⟨(status_setPC sF _).trans hp.1, (sp_setPC sF _).trans hp.2.1,
       (vregs_setPC sF _).trans hp.2.2.1,
       fun r hr => (readReg64_setPC sF _ r).trans (hp.2.2.2 r hr)⟩
    refine SepWP.done hpcF ((status_setPC sF _).trans hp.1) ⟨hp1, sampled', hws', hraw, ?_⟩
    have h672 : BTreeMem (sp + 26768#64) 84 tB ⊢ memRegion (sp + 26768#64) 672 :=
      BTreeMem_entails_memRegion (sp + 26768#64) 84 tB
    exact Entails.trans (sepConj_mono_left h672) (by sep_frame)
  refine sepWP_seq_env hcl hro hsite fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hp, sampled', hws', hraw, hP1⟩ => ?_
  have hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp],
      r ∉ rejCfgExtra1.siteClobberedRegs :=
    @of_decide_eq_true _ (decBallNotMem rejCfgExtra1.siteClobberedRegs
      [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp]) rfl
  obtain ⟨_, hsp1, hspA1, hgprs1, hx1_1, hsl_tr⟩ :=
    sitePreserved_row (pc := s1.pc) (cfgS := cfgC) (tA := tA) hp hsp hspA hgprs hclob
  have hs1_eq : s1.setPC s1.pc = s1 := by cases s1; rfl
  rw [hs1_eq] at hsp1 hspA1 hgprs1 hx1_1 hsl_tr
  refine SepWP.weaken_pre hP1 ?_
  exact step_post_extra1_clamp hpc1 hrun1 hsp1 hspA1 hsp16 hcl1 hro1 hgprs1 hhdr
    (hx1_1.trans hx1) (fun idx hidx => hsl_tr _ _ _ (hsl01 idx hidx))
    (fun idx hidx => hsl_tr _ _ _ (hsl23 idx hidx)) hraw

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Extra
