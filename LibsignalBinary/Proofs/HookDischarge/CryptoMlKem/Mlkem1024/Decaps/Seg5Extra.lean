/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitB
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 Extra-Block While Body

Proves `seg5_extra_bodyA_ok` (`+0x6348 → +0x6d10`, 1-block 4-lane `L7`/`L8` squeeze) and
`seg5_extra_bodyB_ok` (`+0x6d10 → +0x710c / +0x6348`, `step_rej_site_extra1` + post-site clamp).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakAbsorb keccakF1600 keccakPermuteN)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  SitePreserved decBallNotMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone step_rej_site_extra1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  condCC_256_of_le271 raw_sampled_le271)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06 blkPl06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (fetchWordTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMem_entails_memRegion KSpatial KStateMatches SepWP.of_memRegion_btreeMem
  btreeBytesFrom btreeBytesFrom_length evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  btreeBytesFrom_eq_extractRate_21 rejBufReadable_of_btreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep evalExprList25 evalKExpr_congr_ok eval_checked_gpr eval_checked_memB
  extendLoopVars exprVarsOk rowSeed specEnvSteps)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  slotsInv01 slotsInv23 slotsL7 slotsL8 slotsMidExtra01 slotsMidExtra23)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  checkOutSlots checked_outSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB (
  keccakAbsorb_rowSeed_size keccakPermuteN_size keccakPermuteN_succ_right slotExprsHi slotExprsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp (
  ClampCmpMatches ClampMatches ClampState condLS_255_of_le271)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init (
  allLanesDone4_false_of_lt256 allLanesDone4_true_of_ge256 clampMatches_setPC with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowCalleeGprs06 RowExitState06 RowExtraState06 RowMidState06 cfgC06 cfgC06_valid
  cfgClamp06 cfgClamp06_valid fetches_rejExtra1_06_inner fetches_rejExtra1_06_outer
  rejCfgExtra1_06 rejCfgExtra1_06_valid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06 (
  runAndCheckKProg06 sepWP_of_runAndCheckKProg06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA (
  checkCalleeGprsPreserved06 checkHeaderPreserved06 checked_calleeGprs06 checked_headerOk06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitB (
  envInitB06 evalExprList25_slotExprs06 stRawB06 stRawB06_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp (
  checkClampCommon06 csInitClamp06 envClamp06 envClamp06_valid runClampRange06
  sepWP_of_runClampRange06 sitePreserved_row06 stRawClamp06_matches step_bCond_seg5 step_b_seg5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init (
  checkClampFull06 eval_envClamp06_800 finish_clamp_exit06 finish_clamp_loop06)

attribute [local irreducible] blkPC06 mlkemMultiLib keccakF1600 keccakAbsorb BTreeMem allLanesDone

private theorem status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
private theorem sp_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := rfl
private theorem vregs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).vregs = s.vregs := rfl
private theorem spAligned_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := rfl
private theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl
private theorem rowCalleeGprs06_setPC [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    {s : State} (pc : BitVec 64) (hg : RowCalleeGprs06 sp rcBase fpVal row s) :
    RowCalleeGprs06 sp rcBase fpVal row (s.setPC pc) := hg
private theorem slotHolds_setPC {cfg : KCfg} {s : State} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {vLo vHi : BitVec 64} (pc : BitVec 64)
    (h : slotHolds cfg s tA sl vLo vHi) : slotHolds cfg (s.setPC pc) tA sl vLo vHi := h

/-! ## 1. Extra-Block Body A (`+0x6348 → +0x6d10`, `L7`–`L8` 1-Block Squeeze) -/

private def stepsExtraA06 : List KProgStep :=
  [.range 6354 19,
   .loop 6373 205 8#5 slotsL7 (slotExprsLo cfgC06 stRawB06 slotsInv01) (slotExprsHi cfgC06 stRawB06 slotsInv01) 2000,
   .range 6579 83,
   .loop 6662 206 10#5 slotsL8 (slotExprsLo cfgC06 stRawB06 slotsInv23) (slotExprsHi cfgC06 stRawB06 slotsInv23) 3000,
   .range 6869 106]

private def expMemBExtra1_06 (c j : Nat) : KExpr :=
  match c with
  | 0 => .var (2000 + j)
  | 1 => .var (2025 + j)
  | 2 => .var (3000 + j)
  | _ => .var (3025 + j)

private def chkMemBExtra1_06 (ok : Nat → Bool) (st : KState) : Bool :=
  (List.range 4).all fun c => (List.range 21).all fun j =>
    let e := expMemBExtra1_06 c j
    (st.memB.get (21 * c + j)).beq e && exprVarsOk ok e

private def chkExtraA06 (ok : Nat → Bool) (st : KState) : Bool :=
  (st.gprs.get 1).beq (.var 66) && exprVarsOk ok (.var 66) &&
  (st.gprs.get 10).beq (.const64 0#64) && exprVarsOk ok (.const64 0#64) &&
  (st.gprs.get 8).beq (.spAdd 28379#64) && exprVarsOk ok (.spAdd 28379#64) &&
  checkHeaderPreserved06 ok st && checkCalleeGprsPreserved06 ok st && chkMemBExtra1_06 ok st &&
  checkOutSlots cfgC06 ok st slotsMidExtra01 2000 && checkOutSlots cfgC06 ok st slotsMidExtra23 3000

private theorem cert_extraA06 :
    runAndCheckKProg06 cfgC06 6354 6975 6354 6975 1600 stepsExtraA06 stRawB06 chkExtraA06 = true := by
  decide +kernel

private theorem nr_extra_clamp06 : blk06NoRelocInRange 6975 7236 = true := by rfl_kernel
private theorem fw_6975 : fetchWordTree06 6975 = some (.b 20#64) := by rfl_kernel

theorem seg5_extra_bodyA_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 b) {rho : List (BitVec 8)} {row extra : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) {st : State} {P : SepProp}
    (hpre : RowExtraState06 b sp rcBase fpVal rho row Rest extra st P) :
    SepWP (blkPC06.rebase b (fun _ => none)) (pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4) st P
      (RowMidState06 sp rcBase fpVal rho row Rest extra) := by
  rcases hpre with ⟨hpc, hrun, hsp, hspA, hsp16, hcl, hro, hgprs, hx1,
    tA0, sampled, hws, hhdr0, hsl01, hsl23, hinv, hP⟩
  refine with_frozen_env hcl hro ?_
  refine SepWP.weaken_pre hP ?_
  refine SepWP.of_memRegion_btreeMem 84 (sp + 28368#64) (by decide) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun tB0 => ?_
  rcases stRawB06_matches hsp hspA hgprs hhdr0 (tB := tB0) with ⟨hm0, htA0, htB0⟩
  let env0 := envInitB06 sp rcBase fpVal rho row st tA0 tB0
  change KStateMatches env0 stRawB06 st at hm0
  change evalMemTree env0 stRawB06.memA = tA0 at htA0
  change evalMemTree env0 stRawB06.memB = tB0 at htB0
  have henvSp : env0.sp = sp := rfl
  have henvRc : env0.rcBase = rcBase := rfl
  have hspEnt :
      (BTreeMem (sp + 28368#64) 84 tB0 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
        MultiLaneSampled (sp + 26320#64) 4 sampled ∗
        MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
        memRegion (sp + 30448#64) 2016 ∗ Rest)) ⊢
      KSpatial cfgC06 env0 stRawB06 (MultiLaneSampled (sp + 26320#64) 4 sampled ∗
        MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
        memRegion (sp + 30448#64) 2016 ∗ Rest) := by
    simp only [KSpatial, cfgC06, henvSp, henvRc, htA0, htB0]; sep_frame
  refine SepWP.weaken_pre hspEnt ?_
  have hpc' : st.pc = b + BitVec.ofNat 64 (4 * 6354) := by simpa using hpc
  refine sepWP_of_runAndCheckKProg06 cfgC06_valid (env0 := env0) (show 0 < 24 by decide) cert_extraA06 hm0 hpc' hrun ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _ heval hmF hchk
  simp only [chkExtraA06, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx1_eq, hx1_ok⟩, hx10_eq⟩, hx10_ok⟩, hx8_eq⟩, hx8_ok⟩,
    hhdr_chk⟩, hgpr_chk⟩, hmemB_chk⟩, hout01⟩, hout23⟩
  let sk (col : Nat) := keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row col))
  have hkSz (col : Nat) : (sk col).size = 25 :=
    keccakPermuteN_size (extra + 2) (keccakAbsorb_rowSeed_size hrho row col)
  have hlt800_01 : evalExprList25 env0 (slotExprsLo cfgC06 stRawB06 slotsInv01) = sk 0 ∧
      evalExprList25 env0 (slotExprsHi cfgC06 stRawB06 slotsInv01) = sk 1 :=
    evalExprList25_slotExprs06 hm0 htA0 (fun _ _ => rfl) (by decide) (by decide) rfl
      (hkSz 0) (hkSz 1) hsl01
  let env1 := extendLoopVars env0 2000 (sk 0) (sk 1)
  have hsub1 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true → evalKExpr env1 e = evalKExpr env0 e :=
    evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid; simp [env1, extendLoopVars, show id < 2000 by omega]
  have hlt800_23 : evalExprList25 env1 (slotExprsLo cfgC06 stRawB06 slotsInv23) = sk 2 ∧
      evalExprList25 env1 (slotExprsHi cfgC06 stRawB06 slotsInv23) = sk 3 :=
    evalExprList25_slotExprs06 hm0 htA0 hsub1 (by decide) (by decide) rfl
      (hkSz 2) (hkSz 3) hsl23
  let env2 := extendLoopVars env1 3000 (sk 2) (sk 3)
  have hspecEq : specEnvSteps env0 stepsExtraA06 = env2 := by
    simp only [stepsExtraA06, specEnvSteps, hlt800_01.1, hlt800_01.2]
    change specEnvSteps env1 [.range 6579 83,
      .loop 6662 206 10#5 slotsL8 (slotExprsLo cfgC06 stRawB06 slotsInv23) (slotExprsHi cfgC06 stRawB06 slotsInv23) 3000,
      .range 6869 106] = env2
    simp only [specEnvSteps, hlt800_23.1, hlt800_23.2]; rfl
  have hsub2 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (specEnvSteps env0 stepsExtraA06) e = evalKExpr env0 e := by
    rw [hspecEq]
    exact evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid
      simp [env2, env1, extendLoopVars, show id < 3000 by omega, show id < 2000 by omega]
  have hspecSp : (specEnvSteps env0 stepsExtraA06).sp = sp := by rw [hspecEq]; rfl
  have hspecRc : (specEnvSteps env0 stepsExtraA06).rcBase = rcBase := by rw [hspecEq]; rfl
  have hspec64 : (specEnvSteps env0 stepsExtraA06).vars 64 = BitVec.ofNat 64 row :=
    (hsub2 (.var 64) (by decide)).trans rfl
  have hspec66 : (specEnvSteps env0 stepsExtraA06).vars 66 = BitVec.ofNat 64 (row + 1) :=
    (hsub2 (.var 66) (by decide)).trans hx1
  have hspec99 : (specEnvSteps env0 stepsExtraA06).vars 99 = fpVal :=
    (hsub2 (.var 99) (by decide)).trans rfl
  have hx1F := eval_checked_gpr hmF heval 1#5 (by decide) (.var 66) hx1_eq hx1_ok
  have hx10F := eval_checked_gpr hmF heval 10#5 (by decide) (.const64 0#64) hx10_eq hx10_ok
  have hx8F := eval_checked_gpr hmF heval 8#5 (by decide) (.spAdd 28379#64) hx8_eq hx8_ok
  have hhdrF := checked_headerOk06 heval hspecSp
    ((hsub2 (.var 100) (by decide)).trans rfl)
    ((hsub2 (.var 101) (by decide)).trans rfl)
    ((hsub2 (.var 102) (by decide)).trans rfl)
    ((hsub2 (.var 103) (by decide)).trans rfl) hhdr_chk
  have hgprsF := checked_calleeGprs06 hmF heval hspecSp hspecRc hspec64 hspec99 hgpr_chk
  have hslOut01 := checked_outSlots hmF heval (by decide) (by decide) hout01
  have hslOut23 := checked_outSlots hmF heval (by decide) (by decide) hout23
  refine step_b_seg5 (disp := 20#64) nr_extra_clamp06 (by decide) (by decide) (by decide)
    fw_6975 hpcF hrunF ?_
  have hpcMid : (sf.setPC (b + BitVec.ofNat 64 (4 * 6975) + 20#64)).pc =
      pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4 := by dsimp only [State.setPC, pcAt]; bv_omega
  refine SepWP.done hpcMid ((status_setPC sf _).trans hrunF) fun hclM hroM => ?_
  have hstep3 (col : Nat) : keccakF1600 (sk col) =
      keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row col)) := by
    simpa [sk, Nat.add_assoc] using keccakPermuteN_succ_right (extra + 2)
      (keccakAbsorb 21 0x1f#8 (rowSeed rho row col))
  refine ⟨(sp_setPC sf _).trans (hmF.hsp.trans hspF), (spAligned_setPC sf _).trans hmF.hsp_al,
    hsp16, hclM, hroM, rowCalleeGprs06_setPC _ hgprsF,
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
    · simp [expMemBExtra1_06, evalKExpr, env2, env1, extendLoopVars, hstep3 0,
        show 2000 + j < 3000 by omega, show ¬(2000 + j < 2000) by omega, show 2000 + j < 2000 + 25 by omega]
    · simp [expMemBExtra1_06, evalKExpr, env2, env1, extendLoopVars, hstep3 1,
        show 2025 + j < 3000 by omega, show ¬(2025 + j < 2000) by omega,
        show ¬(2025 + j < 2000 + 25) by omega, show 2025 + j < 2000 + 50 by omega,
        show 2025 + j - (2000 + 25) = j by omega]
    · simp [expMemBExtra1_06, evalKExpr, env2, extendLoopVars, hstep3 2,
        show ¬(3000 + j < 3000) by omega, show 3000 + j < 3000 + 25 by omega]
    · simp [expMemBExtra1_06, evalKExpr, env2, extendLoopVars, hstep3 3,
        show ¬(3025 + j < 3000) by omega, show ¬(3025 + j < 3000 + 25) by omega,
        show 3025 + j < 3000 + 50 by omega, show 3025 + j - (3000 + 25) = j by omega]
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsExtraA06).vars (2000 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, env1, extendLoopVars, hstep3 0,
        show 2000 + idx < 3000 by omega, show ¬(2000 + idx < 2000) by omega, show 2000 + idx < 2000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsExtraA06).vars (2000 + 25 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, env1, extendLoopVars, hstep3 1,
        show 2000 + 25 + idx < 3000 by omega, show ¬(2000 + 25 + idx < 2000) by omega,
        show ¬(2000 + 25 + idx < 2000 + 25) by omega, show 2000 + 25 + idx < 2000 + 50 by omega]
    exact slotHolds_setPC _ (by simpa [hvLo, hvHi] using hslOut01 idx hidx)
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsExtraA06).vars (3000 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, extendLoopVars, hstep3 2,
        show ¬(3000 + idx < 3000) by omega, show 3000 + idx < 3000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsExtraA06).vars (3000 + 25 + idx) =
        (keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64 := by
      rw [hspecEq]; simp [env2, extendLoopVars, hstep3 3,
        show ¬(3025 + idx < 3000) by omega, show ¬(3025 + idx < 3000 + 25) by omega,
        show 3025 + idx < 3000 + 50 by omega]
    exact slotHolds_setPC _ (by simpa [hvLo, hvHi] using hslOut23 idx hidx)
  · simp only [KSpatial, cfgC06, hspF, hrcF, henvSp, henvRc]; sep_frame

/-! ## 2. Extra-Block Body B (`+0x6d10 → +0x710c / +0x6348`, `step_rej_site_extra1` + Clamp) -/

private def csExtra7228 : ClampState := (runClampRange06 cfgClamp06 7180 48 csInitClamp06).getD csInitClamp06
private def csExtra7230 : ClampState := (runClampRange06 cfgClamp06 7229 1 csExtra7228).getD csInitClamp06
private def csExtra7232 : ClampState := (runClampRange06 cfgClamp06 7231 1 csExtra7230).getD csInitClamp06
private def csExtra7234 : ClampState := (runClampRange06 cfgClamp06 7233 1 csExtra7232).getD csInitClamp06

private theorem run_extra7228 : runClampRange06 cfgClamp06 7180 48 csInitClamp06 = some csExtra7228 := by rfl_kernel
private theorem cmp_extra7228 : csExtra7228.cmpOpt = some (.var 803, 256#64) := by rfl_kernel
private theorem chk_extra7228 : checkClampFull06 slotsMidExtra01 slotsMidExtra23 csExtra7228.st = true := by rfl_kernel
private theorem run_extra7230 : runClampRange06 cfgClamp06 7229 1 csExtra7228 = some csExtra7230 := by rfl_kernel
private theorem cmp_extra7230 : csExtra7230.cmpOpt = some (.var 802, 256#64) := by rfl_kernel
private theorem chk_extra7230 : checkClampFull06 slotsMidExtra01 slotsMidExtra23 csExtra7230.st = true := by rfl_kernel
private theorem run_extra7232 : runClampRange06 cfgClamp06 7231 1 csExtra7230 = some csExtra7232 := by rfl_kernel
private theorem cmp_extra7232 : csExtra7232.cmpOpt = some (.var 801, 256#64) := by rfl_kernel
private theorem chk_extra7232 : checkClampFull06 slotsMidExtra01 slotsMidExtra23 csExtra7232.st = true := by rfl_kernel
private theorem run_extra7234 : runClampRange06 cfgClamp06 7233 1 csExtra7232 = some csExtra7234 := by rfl_kernel
private theorem cmp_extra7234 : csExtra7234.cmpOpt = some (.var 800, 255#64) := by rfl_kernel
private theorem chk_extra7234 : checkClampFull06 slotsMidExtra01 slotsMidExtra23 csExtra7234.st = true := by rfl_kernel
private theorem chk_extra7234_common : checkClampCommon06 csExtra7234.st = true := by rfl_kernel

private theorem fw_7228 : fetchWordTree06 7228 = some (.bCond .CC (-(3496#64))) := by rfl_kernel
private theorem fw_7230 : fetchWordTree06 7230 = some (.bCond .CC (-(3504#64))) := by rfl_kernel
private theorem fw_7232 : fetchWordTree06 7232 = some (.bCond .CC (-(3512#64))) := by rfl_kernel
private theorem fw_7234 : fetchWordTree06 7234 = some (.bCond .LS (-(3520#64))) := by rfl_kernel

attribute [local irreducible] csExtra7228 csExtra7230 csExtra7232 csExtra7234

private theorem step_post_extra1_clamp06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 7180)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hsl01 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slotsMidExtra01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hsl23 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slotsMidExtra23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) (extra + 1) sampled' hws') :
    let F := MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      s ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗ (MultiLaneSampled (sp + 26320#64) 4 sampled' ∗ F)))
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
          RowExitState06 sp rcBase fpVal rho row Rest sf Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest (extra + 1) sf Pf) := by
  intro F
  have hsamp271 : ∀ c, c < 4 → sampled' c ≤ 271 := fun c hc => raw_sampled_le271 hraw hc
  have henvV := envClamp06_valid (sp := sp) (rcBase := rcBase) (fpVal := fpVal) (rho := rho) (row := row)
    (s := s) (tA := tA) hsamp271
  obtain ⟨hm0, hspEq0⟩ := stRawClamp06_matches (sampled' := sampled') hsp hspA hgprs hhdr F
  rw [← hspEq0]
  have hloop : ∀ {csEnd : ClampState} {sf : State},
      allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) = false →
      checkClampFull06 slotsMidExtra01 slotsMidExtra23 csEnd.st = true →
      sf.pc = b + BitVec.ofNat 64 (4 * 6354) → sf.status = .Running →
      ClampMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd sf →
      SepWP (blkPC06.rebase b (fun _ => none))
        (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 7235)
         else b + BitVec.ofNat 64 (4 * 6354))
        sf (KSpatial cfgClamp06 (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd.st F)
        (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
          if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
            RowExitState06 sp rcBase fpVal rho row Rest sf' Pf
          else RowExtraState06 b sp rcBase fpVal rho row Rest (extra + 1) sf' Pf) := fun hd hc hp hr hm =>
    finish_clamp_loop06 (extra := extra + 1) (Rest := Rest) hsp hspA hsp16 hgprs hhdr hx1
      (by decide) rfl (by decide) rfl hsl01 hsl23 hraw hd hc hp hr hm
  refine with_frozen_env hcl hro ?_
  refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 48 7180 nr_extra_clamp06 (by decide)
    (by decide) (by decide) run_extra7228 hm0 hpc hrun fun s1 hpc1 hrun1 hm1 => ?_
  refine step_bCond_seg5 (cond := .CC) (disp := -(3496#64)) nr_extra_clamp06 (by decide) (by decide)
    (by decide) fw_7228 hpc1 hrun1 (fun hT3 => ?_) (fun hF3 => ?_)
  · have hlt3 : sampled' 3 < 256 := by
      have hp := hm1.2.2; simp only [ClampCmpMatches, cmp_extra7228] at hp
      rw [eval_envClamp06_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_true_eq] at hT3; exact hT3
    exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt3) chk_extra7228
      (by dsimp only [State.setPC]; bv_omega) ((status_setPC s1 _).trans hrun1)
      (clampMatches_setPC _ hm1)
  · have hge3 : 256 ≤ sampled' 3 := by
      have hp := hm1.2.2; simp only [ClampCmpMatches, cmp_extra7228] at hp
      rw [eval_envClamp06_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_false_iff_not] at hF3; omega
    refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 1 7229 nr_extra_clamp06 (by decide)
      (by decide) (by decide) run_extra7230 (clampMatches_setPC _ hm1)
      (by dsimp only [State.setPC]) ((status_setPC s1 _).trans hrun1) fun s2 hpc2 hrun2 hm2 => ?_
    refine step_bCond_seg5 (cond := .CC) (disp := -(3504#64)) nr_extra_clamp06 (by decide) (by decide)
      (by decide) fw_7230 hpc2 hrun2 (fun hT2 => ?_) (fun hF2 => ?_)
    · have hlt2 : sampled' 2 < 256 := by
        have hp := hm2.2.2; simp only [ClampCmpMatches, cmp_extra7230] at hp
        rw [eval_envClamp06_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_true_eq] at hT2; exact hT2
      exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt2) chk_extra7230
        (by dsimp only [State.setPC]; bv_omega) ((status_setPC s2 _).trans hrun2)
        (clampMatches_setPC _ hm2)
    · have hge2 : 256 ≤ sampled' 2 := by
        have hp := hm2.2.2; simp only [ClampCmpMatches, cmp_extra7230] at hp
        rw [eval_envClamp06_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_false_iff_not] at hF2; omega
      refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 1 7231 nr_extra_clamp06 (by decide)
        (by decide) (by decide) run_extra7232 (clampMatches_setPC _ hm2)
        (by dsimp only [State.setPC]) ((status_setPC s2 _).trans hrun2) fun s3 hpc3 hrun3 hm3 => ?_
      refine step_bCond_seg5 (cond := .CC) (disp := -(3512#64)) nr_extra_clamp06 (by decide) (by decide)
        (by decide) fw_7232 hpc3 hrun3 (fun hT1 => ?_) (fun hF1 => ?_)
      · have hlt1 : sampled' 1 < 256 := by
          have hp := hm3.2.2; simp only [ClampCmpMatches, cmp_extra7232] at hp
          rw [eval_envClamp06_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_true_eq] at hT1; exact hT1
        exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt1) chk_extra7232
          (by dsimp only [State.setPC]; bv_omega) ((status_setPC s3 _).trans hrun3)
          (clampMatches_setPC _ hm3)
      · have hge1 : 256 ≤ sampled' 1 := by
          have hp := hm3.2.2; simp only [ClampCmpMatches, cmp_extra7232] at hp
          rw [eval_envClamp06_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_false_iff_not] at hF1; omega
        refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 1 7233 nr_extra_clamp06 (by decide)
          (by decide) (by decide) run_extra7234 (clampMatches_setPC _ hm3)
          (by dsimp only [State.setPC]) ((status_setPC s3 _).trans hrun3) fun s4 hpc4 hrun4 hm4 => ?_
        refine step_bCond_seg5 (cond := .LS) (disp := -(3520#64)) nr_extra_clamp06 (by decide) (by decide)
          (by decide) fw_7234 hpc4 hrun4 (fun hT0 => ?_) (fun hF0 => ?_)
        · have hlt0 : sampled' 0 < 256 := by
            have hp := hm4.2.2; simp only [ClampCmpMatches, cmp_extra7234] at hp
            rw [eval_envClamp06_800 (c := 0) (by decide)] at hp
            rw [hp, condLS_255_of_le271 (hsamp271 0 (by decide)), decide_eq_true_eq] at hT0; exact hT0
          exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt0) chk_extra7234
            (by dsimp only [State.setPC]; bv_omega) ((status_setPC s4 _).trans hrun4)
            (clampMatches_setPC _ hm4)
        · have hge0 : 256 ≤ sampled' 0 := by
            have hp := hm4.2.2; simp only [ClampCmpMatches, cmp_extra7234] at hp
            rw [eval_envClamp06_800 (c := 0) (by decide)] at hp
            rw [hp, condLS_255_of_le271 (hsamp271 0 (by decide)), decide_eq_false_iff_not] at hF0; omega
          have hdT := allLanesDone4_true_of_ge256 hraw hge0 hge1 hge2 hge3
          exact finish_clamp_exit06 (Rest := Rest) hsp16 hx1 hraw hdT chk_extra7234_common
            (by dsimp only [State.setPC]) ((status_setPC s4 _).trans hrun4)
            (clampMatches_setPC _ hm4)

theorem seg5_extra_bodyB_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 b) {rho : List (BitVec 8)} {row extra : Nat} {Rest : SepProp}
    {sm : State} {Pm : SepProp}
    (hpc : sm.pc = pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4) (hrun : sm.status = .Running)
    (hmid : RowMidState06 sp rcBase fpVal rho row Rest extra sm Pm) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      sm Pm
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) then
          RowExitState06 sp rcBase fpVal rho row Rest sf Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest (extra + 1) sf Pf) := by
  rcases hmid with ⟨hsp, hspA, hsp16, hcl, hro, hgprs, hx1, hx10, hx8,
    tA, tB, sampled, hws, hhdr, hsq, hsl01, hsl23, hraw0, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hsite : SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 7180)) sm
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        BTreeMem (sp + 28368#64) 84 tB ∗ MultiLaneSampled (sp + 26320#64) 4 sampled ∗
        MultiLaneSlots (sp + 4160#64) 544 4 hws ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)
      (fun s1 P1 =>
        SitePreserved rejCfgExtra1_06 sm s1 ∧
        ∃ sampled' hws',
          MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) (extra + 1) sampled' hws' ∧
          (P1 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (sp + 144#64) 286 tA ∗
              (MultiLaneSampled (sp + 26320#64) 4 sampled' ∗
                (MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
                  memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest))))) := by
    refine SepWP.weaken_pre (by sep_frame : _ ⊢ BTreeMem (sp + 28368#64) 84 tB ∗
      (MultiLaneSampled (sp + 26320#64) 4 sampled ∗
        (MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
          ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
            memRegion (sp + 30448#64) 2016 ∗ Rest)))) ?_
    refine step_rej_site_extra1 (pcBase := b + BitVec.ofNat 64 (4 * 6976))
      (sqBase := sp + 28368#64) (sampBase := sp + 26320#64)
      (slotsBase := sp + 4160#64) (cfg := rejCfgExtra1_06)
      (seeds := fun c => rowSeed rho row c) (bufs := fun c => btreeBytesFrom (21 * c) 21 tB)
      hpc hrun rejCfgExtra1_06_valid rfl
      (fetches_rejExtra1_06_outer b) (fetches_rejExtra1_06_inner b)
      (fun i hi => rejBufReadable_of_btreeMem (offWords := 21 * i)
        (by dsimp only [rejCfgExtra1_06]; bv_omega) (by dsimp only [rejCfgExtra1_06] at hi ⊢; omega) rfl)
      (fun i _ => by rw [btreeBytesFrom_length]; decide)
      (fun i hi => by
        have hlen : (btreeBytesFrom (21 * i) 21 tB).length = 168 := by rw [btreeBytesFrom_length]
        rw [List.take_of_length_le (by omega)]
        exact hsq i (by dsimp only [rejCfgExtra1_06] at hi; exact hi))
      hraw0 hx10 (by dsimp only [rejCfgExtra1_06]; rw [hx8]; bv_omega)
      hgprs.2.2.2.2.1 hgprs.1 hgprs.2.2.2.1
      fun sF sampled' hws' hp hraw => ?_
    have hpcF : (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 6976)) 204)).pc =
        b + BitVec.ofNat 64 (4 * 7180) := by dsimp only [State.setPC, pcAt]; bv_omega
    have hp1 : SitePreserved rejCfgExtra1_06 sm (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 6976)) 204)) :=
      ⟨(status_setPC sF _).trans hp.1, (sp_setPC sF _).trans hp.2.1,
       (vregs_setPC sF _).trans hp.2.2.1,
       fun r hr => (readReg64_setPC sF _ r).trans (hp.2.2.2 r hr)⟩
    refine SepWP.done hpcF ((status_setPC sF _).trans hp.1) ⟨hp1, sampled', hws', hraw, ?_⟩
    have h672 : BTreeMem (sp + 28368#64) 84 tB ⊢ memRegion (sp + 28368#64) 672 :=
      BTreeMem_entails_memRegion (sp + 28368#64) 84 tB
    exact Entails.trans (sepConj_mono_left h672) (by sep_frame)
  refine sepWP_seq_env hcl hro hsite fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hp, sampled', hws', hraw, hP1⟩ => ?_
  have hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp],
      r ∉ rejCfgExtra1_06.siteClobberedRegs :=
    @of_decide_eq_true _ (decBallNotMem rejCfgExtra1_06.siteClobberedRegs
      [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp]) rfl
  obtain ⟨_, hsp1, hspA1, hgprs1, hx1_1, hsl_tr⟩ :=
    sitePreserved_row06 (pc := s1.pc) (cfgS := cfgC06) (tA := tA) hp hsp hspA hgprs hclob
  have hs1_eq : s1.setPC s1.pc = s1 := by cases s1; rfl
  rw [hs1_eq] at hsp1 hspA1 hgprs1 hx1_1 hsl_tr
  refine SepWP.weaken_pre hP1 ?_
  exact step_post_extra1_clamp06 hpc1 hrun1 hsp1 hspA1 hsp16 hcl1 hro1 hgprs1 hhdr
    (hx1_1.trans hx1) (fun idx hidx => hsl_tr _ _ _ (hsl01 idx hidx))
    (fun idx hidx => hsl_tr _ _ _ (hsl23 idx hidx)) hraw

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra
