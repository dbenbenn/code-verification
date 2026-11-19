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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitB

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 End-to-End Row Initialization

Composes `seg5_initA_ok`, `seg5_initB_ok`, 3-block `step_rej_site_init3`, and the 4 post-site
clamp/branch paths (`+0x6290 → +0x710c / +0x6348`) into `seg5_init_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init

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
  MultiLaneClampedInv MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  SitePreserved decBallNotMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone step_rej_site_init3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  condCC_256_of_le271 condHI_255_of_le271 raw_sampled_le271)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06 blkPl06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (fetchWordTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMem_entails_memRegion KSpatial btreeBytesFrom btreeBytesFrom_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  rejBufReadable_of_btreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  slotsInv01 slotsInv23 slotsMidInit01 slotsMidInit23)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp (
  ClampCmpMatches ClampMatches ClampState slotHolds_congr_cfg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init (
  allLanesDone4_false_of_lt256 allLanesDone4_true_of_ge256 clampMatches_setPC with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowCalleeGprs06 RowExitState06 RowExtraState06 cfgC06 cfgClamp06 cfgClamp06_valid
  fetches_rejInit3_06_inner fetches_rejInit3_06_outer rejCfgInit3_06 rejCfgInit3_06_valid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA (
  RowInitAPre06 seg5_initA_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitB (seg5_initB_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp (
  checkClampCommon06 checkSlotsMoved06 csInitClamp06 envClamp06 envClamp06_valid
  extract_clamp_common06 extract_slots_moved06 runClampRange06 sepWP_of_runClampRange06
  sitePreserved_row06 stRawClamp06_matches step_bCond_seg5 step_b_seg5)

attribute [local irreducible] blkPC06 mlkemMultiLib keccakF1600 keccakAbsorb BTreeMem allLanesDone

/-! ## 1. Post-Init3 Clamp Certificates & Exit/Loop Packaging (`+0x6290 → +0x710c / +0x6348`) -/

@[expose] def checkClampFull06 (slots01 slots23 : List KSlot) (stEnd : KState) : Bool :=
  checkClampCommon06 stEnd &&
  checkSlotsMoved06 slots01 slotsInv01 stEnd &&
  checkSlotsMoved06 slots23 slotsInv23 stEnd

private def csInit6334 : ClampState := (runClampRange06 cfgClamp06 6308 26 csInitClamp06).getD csInitClamp06
private def csInitEnd1 : ClampState := (runClampRange06 cfgClamp06 6346 4 csInit6334).getD csInitClamp06
private def csInit6337 : ClampState := (runClampRange06 cfgClamp06 6335 2 csInit6334).getD csInitClamp06
private def csInitEnd2 : ClampState := (runClampRange06 cfgClamp06 6351 3 csInit6337).getD csInitClamp06
private def csInit6339 : ClampState := (runClampRange06 cfgClamp06 6338 1 csInit6337).getD csInitClamp06
private def csInitEnd3 : ClampState := (runClampRange06 cfgClamp06 6351 3 csInit6339).getD csInitClamp06
private def csInit6344 : ClampState := (runClampRange06 cfgClamp06 6340 4 csInit6339).getD csInitClamp06

private theorem run_init6334 : runClampRange06 cfgClamp06 6308 26 csInitClamp06 = some csInit6334 := by rfl_kernel
private theorem cmp_init6334 : csInit6334.cmpOpt = some (.var 803, 256#64) := by rfl_kernel
private theorem run_initEnd1 : runClampRange06 cfgClamp06 6346 4 csInit6334 = some csInitEnd1 := by rfl_kernel
private theorem chk_initEnd1 : checkClampFull06 slotsMidInit01 slotsMidInit23 csInitEnd1.st = true := by rfl_kernel
private theorem run_init6337 : runClampRange06 cfgClamp06 6335 2 csInit6334 = some csInit6337 := by rfl_kernel
private theorem cmp_init6337 : csInit6337.cmpOpt = some (.var 802, 256#64) := by rfl_kernel
private theorem run_initEnd2 : runClampRange06 cfgClamp06 6351 3 csInit6337 = some csInitEnd2 := by rfl_kernel
private theorem chk_initEnd2 : checkClampFull06 slotsMidInit01 slotsMidInit23 csInitEnd2.st = true := by rfl_kernel
private theorem run_init6339 : runClampRange06 cfgClamp06 6338 1 csInit6337 = some csInit6339 := by rfl_kernel
private theorem cmp_init6339 : csInit6339.cmpOpt = some (.var 801, 256#64) := by rfl_kernel
private theorem run_initEnd3 : runClampRange06 cfgClamp06 6351 3 csInit6339 = some csInitEnd3 := by rfl_kernel
private theorem chk_initEnd3 : checkClampFull06 slotsMidInit01 slotsMidInit23 csInitEnd3.st = true := by rfl_kernel
private theorem run_init6344 : runClampRange06 cfgClamp06 6340 4 csInit6339 = some csInit6344 := by rfl_kernel
private theorem cmp_init6344 : csInit6344.cmpOpt = some (.var 800, 255#64) := by rfl_kernel
private theorem chk_init6344 : checkClampFull06 slotsMidInit01 slotsMidInit23 csInit6344.st = true := by rfl_kernel
private theorem chk_init6344_common : checkClampCommon06 csInit6344.st = true := by rfl_kernel

private theorem fw_6103 : fetchWordTree06 6103 = some (.b 20#64) := by rfl_kernel
private theorem fw_6334 : fetchWordTree06 6334 = some (.bCond .CC 48#64) := by rfl_kernel
private theorem fw_6337 : fetchWordTree06 6337 = some (.bCond .CC 56#64) := by rfl_kernel
private theorem fw_6339 : fetchWordTree06 6339 = some (.bCond .CC 48#64) := by rfl_kernel
private theorem fw_6344 : fetchWordTree06 6344 = some (.bCond .HI 3564#64) := by rfl_kernel
private theorem fw_6345 : fetchWordTree06 6345 = some (.b 36#64) := by rfl_kernel
private theorem fw_6350 : fetchWordTree06 6350 = some (.b 16#64) := by rfl_kernel

attribute [local irreducible]
  csInit6334 csInitEnd1 csInit6337 csInitEnd2 csInit6339 csInitEnd3 csInit6344

theorem eval_envClamp06_800 {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat} {c : Nat} (hc : c < 4) :
    evalKExpr (envClamp06 sp rcBase fpVal rho row s tA sampled') (.var (800 + c)) =
      BitVec.ofNat 64 (sampled' c) := by
  simp only [evalKExpr, envClamp06, show ¬(800 + c < 800) by omega,
    show 800 + c < 804 by omega, ↓reduceIte, show 800 + c - 800 = c by omega]

theorem finish_clamp_loop06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s sf : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    {slots01 slots23 : List KSlot} {csEnd : ClampState}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hv01 : slots01.all (slotValid cfgClamp06) = true) (hl01 : slots01.length = 25)
    (hv23 : slots23.all (slotValid cfgClamp06) = true) (hl23 : slots23.length = 25)
    (hslots01 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slots01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hslots23 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slots23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled' hws')
    (hdoneF : allLanesDone 4 (fun c => rowSeed rho row c) extra = false)
    (hchk : checkClampFull06 slots01 slots23 csEnd.st = true)
    (hpc : sf.pc = b + BitVec.ofNat 64 (4 * 6354)) (hrun : sf.status = .Running)
    (hm : ClampMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd sf) :
    let F := MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) extra then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      sf (KSpatial cfgClamp06 (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd.st F)
      (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
        if allLanesDone 4 (fun c => rowSeed rho row c) extra then
          RowExitState06 sp rcBase fpVal rho row Rest sf' Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest extra sf' Pf) := by
  intro F
  simp only [checkClampFull06, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hcomm, hm01⟩, hm23⟩
  rcases extract_clamp_common06 hm.1 hx1 hcomm (F := F) with ⟨hhdr', hgpr', hx1', hspOut⟩
  have hs01 := extract_slots_moved06 (sampled' := sampled') hsp hspA hgprs hhdr hm.1 hv01 hl01 (by decide) rfl hslots01 hm01
  have hs23 := extract_slots_moved06 (sampled' := sampled') hsp hspA hgprs hhdr hm.1 hv23 hl23 (by decide) rfl hslots23 hm23
  simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
  refine SepWP.done hpc hrun fun hcl hro => ⟨?_, hrun, hm.1.hsp, hm.1.hsp_al, hsp16, hcl, hro, hgpr', hx1',
    _, _, _, hhdr', hs01, hs23, hraw.clamp, ?_⟩
  · simpa using hpc
  · rw [hspOut]; dsimp only [F]; sep_frame

theorem finish_clamp_exit06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s sf : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)} {csEnd : ClampState}
    (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled' hws')
    (hdoneT : allLanesDone 4 (fun c => rowSeed rho row c) extra = true)
    (hchk : checkClampCommon06 csEnd.st = true)
    (hpc : sf.pc = b + BitVec.ofNat 64 (4 * 7235)) (hrun : sf.status = .Running)
    (hm : ClampMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd sf) :
    let F := MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) extra then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      sf (KSpatial cfgClamp06 (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd.st F)
      (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
        if allLanesDone 4 (fun c => rowSeed rho row c) extra then
          RowExitState06 sp rcBase fpVal rho row Rest sf' Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest extra sf' Pf) := by
  intro F
  rcases extract_clamp_common06 hm.1 hx1 hchk (F := F) with ⟨hhdr', hgpr', hx1', hspOut⟩
  simp only [hdoneT, ↓reduceIte]
  refine SepWP.done hpc hrun fun hcl hro => ⟨hm.1.hsp, hm.1.hsp_al, hsp16, hcl, hro, hgpr', hx1',
    extra, _, _, _, hhdr', hraw.clamp, hdoneT, ?_⟩
  rw [hspOut]; dsimp only [F]; sep_frame

private theorem nr_init_clamp06 : blk06NoRelocInRange 6103 6354 = true := by rfl_kernel

private theorem status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
private theorem mem_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
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

theorem step_post_init3_clamp06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row : Nat} {Rest : SepProp} {s : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 6308)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hsl01 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slotsMidInit01.getD idx (.vreg 0))
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hsl23 : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slotsMidInit23.getD idx (.vreg 0))
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) 0 sampled' hws') :
    let F := MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      s ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗ (MultiLaneSampled (sp + 26320#64) 4 sampled' ∗ F)))
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState06 sp rcBase fpVal rho row Rest sf Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest 0 sf Pf) := by
  intro F
  have hsamp271 : ∀ c, c < 4 → sampled' c ≤ 271 := fun c hc => raw_sampled_le271 hraw hc
  have henvV := envClamp06_valid (sp := sp) (rcBase := rcBase) (fpVal := fpVal) (rho := rho) (row := row)
    (s := s) (tA := tA) hsamp271
  obtain ⟨hm0, hspEq0⟩ := stRawClamp06_matches (sampled' := sampled') hsp hspA hgprs hhdr F
  rw [← hspEq0]
  have hloop : ∀ {csEnd : ClampState} {sf : State},
      allLanesDone 4 (fun c => rowSeed rho row c) 0 = false →
      checkClampFull06 slotsMidInit01 slotsMidInit23 csEnd.st = true →
      sf.pc = b + BitVec.ofNat 64 (4 * 6354) → sf.status = .Running →
      ClampMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd sf →
      SepWP (blkPC06.rebase b (fun _ => none))
        (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 7235)
         else b + BitVec.ofNat 64 (4 * 6354))
        sf (KSpatial cfgClamp06 (envClamp06 sp rcBase fpVal rho row s tA sampled') csEnd.st F)
        (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
          if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState06 sp rcBase fpVal rho row Rest sf' Pf
          else RowExtraState06 b sp rcBase fpVal rho row Rest 0 sf' Pf) := fun hd hc hp hr hm =>
    finish_clamp_loop06 (extra := 0) (Rest := Rest) hsp hspA hsp16 hgprs hhdr hx1
      (by decide) rfl (by decide) rfl hsl01 hsl23 hraw hd hc hp hr hm
  refine with_frozen_env hcl hro ?_
  refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 26 6308 nr_init_clamp06 (by decide)
    (by decide) (by decide) run_init6334 hm0 hpc hrun fun s1 hpc1 hrun1 hm1 => ?_
  refine step_bCond_seg5 (cond := .CC) (disp := 48#64) nr_init_clamp06 (by decide) (by decide)
    (by decide) fw_6334 hpc1 hrun1 (fun hT3 => ?_) (fun hF3 => ?_)
  · have hlt3 : sampled' 3 < 256 := by
      have hp := hm1.2.2; simp only [ClampCmpMatches, cmp_init6334] at hp
      rw [eval_envClamp06_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_true_eq] at hT3; exact hT3
    refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 4 6346 nr_init_clamp06 (by decide)
      (by decide) (by decide) run_initEnd1 (clampMatches_setPC _ hm1) (by dsimp only [State.setPC]; bv_omega)
      ((status_setPC s1 _).trans hrun1) fun sE hpcE hrunE hmE => ?_
    refine step_b_seg5 (disp := 16#64) nr_init_clamp06 (by decide) (by decide) (by decide)
      fw_6350 hpcE hrunE ?_
    exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt3) chk_initEnd1
      (by dsimp only [State.setPC]; bv_omega) ((status_setPC sE _).trans hrunE) (clampMatches_setPC _ hmE)
  · have hge3 : 256 ≤ sampled' 3 := by
      have hp := hm1.2.2; simp only [ClampCmpMatches, cmp_init6334] at hp
      rw [eval_envClamp06_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_false_iff_not] at hF3; omega
    refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 2 6335 nr_init_clamp06 (by decide)
      (by decide) (by decide) run_init6337 (clampMatches_setPC _ hm1)
      (by dsimp only [State.setPC]) ((status_setPC s1 _).trans hrun1) fun s2 hpc2 hrun2 hm2 => ?_
    refine step_bCond_seg5 (cond := .CC) (disp := 56#64) nr_init_clamp06 (by decide) (by decide)
      (by decide) fw_6337 hpc2 hrun2 (fun hT2 => ?_) (fun hF2 => ?_)
    · have hlt2 : sampled' 2 < 256 := by
        have hp := hm2.2.2; simp only [ClampCmpMatches, cmp_init6337] at hp
        rw [eval_envClamp06_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_true_eq] at hT2; exact hT2
      refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 3 6351 nr_init_clamp06 (by decide)
        (by decide) (by decide) run_initEnd2 (clampMatches_setPC _ hm2) (by dsimp only [State.setPC]; bv_omega)
        ((status_setPC s2 _).trans hrun2) fun sE hpcE hrunE hmE =>
        hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt2) chk_initEnd2 hpcE hrunE hmE
    · have hge2 : 256 ≤ sampled' 2 := by
        have hp := hm2.2.2; simp only [ClampCmpMatches, cmp_init6337] at hp
        rw [eval_envClamp06_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_false_iff_not] at hF2; omega
      refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 1 6338 nr_init_clamp06 (by decide)
        (by decide) (by decide) run_init6339 (clampMatches_setPC _ hm2)
        (by dsimp only [State.setPC]) ((status_setPC s2 _).trans hrun2) fun s3 hpc3 hrun3 hm3 => ?_
      refine step_bCond_seg5 (cond := .CC) (disp := 48#64) nr_init_clamp06 (by decide) (by decide)
        (by decide) fw_6339 hpc3 hrun3 (fun hT1 => ?_) (fun hF1 => ?_)
      · have hlt1 : sampled' 1 < 256 := by
          have hp := hm3.2.2; simp only [ClampCmpMatches, cmp_init6339] at hp
          rw [eval_envClamp06_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_true_eq] at hT1; exact hT1
        refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 3 6351 nr_init_clamp06 (by decide)
          (by decide) (by decide) run_initEnd3 (clampMatches_setPC _ hm3) (by dsimp only [State.setPC]; bv_omega)
          ((status_setPC s3 _).trans hrun3) fun sE hpcE hrunE hmE =>
          hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt1) chk_initEnd3 hpcE hrunE hmE
      · have hge1 : 256 ≤ sampled' 1 := by
          have hp := hm3.2.2; simp only [ClampCmpMatches, cmp_init6339] at hp
          rw [eval_envClamp06_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_false_iff_not] at hF1; omega
        refine sepWP_of_runClampRange06 cfgClamp06_valid henvV 4 6340 nr_init_clamp06 (by decide)
          (by decide) (by decide) run_init6344 (clampMatches_setPC _ hm3)
          (by dsimp only [State.setPC]) ((status_setPC s3 _).trans hrun3) fun s4 hpc4 hrun4 hm4 => ?_
        refine step_bCond_seg5 (cond := .HI) (disp := 3564#64) nr_init_clamp06 (by decide) (by decide)
          (by decide) fw_6344 hpc4 hrun4 (fun hT0 => ?_) (fun hF0 => ?_)
        · have hge0 : 256 ≤ sampled' 0 := by
            have hp := hm4.2.2; simp only [ClampCmpMatches, cmp_init6344] at hp
            rw [eval_envClamp06_800 (c := 0) (by decide)] at hp
            rw [hp, condHI_255_of_le271 (hsamp271 0 (by decide)), decide_eq_true_eq] at hT0; exact hT0
          have hdT := allLanesDone4_true_of_ge256 hraw hge0 hge1 hge2 hge3
          have hpcEx : (s4.setPC (b + BitVec.ofNat 64 (4 * 6344) + 3564#64)).pc =
              b + BitVec.ofNat 64 (4 * 7235) := by dsimp only [State.setPC]; bv_omega
          exact finish_clamp_exit06 (Rest := Rest) hsp16 hx1 hraw hdT chk_init6344_common hpcEx
            ((status_setPC s4 _).trans hrun4) (clampMatches_setPC _ hm4)
        · have hlt0 : sampled' 0 < 256 := by
            have hp := hm4.2.2; simp only [ClampCmpMatches, cmp_init6344] at hp
            rw [eval_envClamp06_800 (c := 0) (by decide)] at hp
            rw [hp, condHI_255_of_le271 (hsamp271 0 (by decide)), decide_eq_false_iff_not] at hF0; omega
          refine step_b_seg5 (disp := 36#64) nr_init_clamp06 (by decide) (by decide) (by decide)
            fw_6345 (by dsimp only [State.setPC]) ((status_setPC s4 _).trans hrun4) ?_
          exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt0) chk_init6344
            (by dsimp only [State.setPC]; bv_omega)
            ((status_setPC _ _).trans ((status_setPC s4 _).trans hrun4))
            (clampMatches_setPC _ (clampMatches_setPC _ hm4))

/-! ## 2. Full Row Initialization `seg5_init_ok` (`+0x4170 → +0x710c / +0x6348`) -/

theorem seg5_init_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4188)) (hrun : s.status = .Running)
    (hpre : RowInitAPre06 sp rcBase fpVal rho row Rest s P) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 7235)
       else b + BitVec.ofNat 64 (4 * 6354))
      s P
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState06 sp rcBase fpVal rho row Rest sf Pf
        else RowExtraState06 b sp rcBase fpVal rho row Rest 0 sf Pf) := by
  refine SepWP.seq (seg5_initA_ok hb hbase hrho hrow hpc hrun hpre) fun sA PA hpcA hrunA hpostA => ?_
  refine SepWP.seq (seg5_initB_ok hb hrho hpcA hrunA hpostA) fun sB PB hpcB hrunB hpostB => ?_
  rcases hpostB with ⟨hspB, hspAB, hsp16, hclB, hroB, hgprsB, hx1B, hx8B, hx9B,
    tA, tB, hhdrB, hsqB, hsl01B, hsl23B, hPB⟩
  refine SepWP.weaken_pre hPB ?_
  have hpcB' : sB.pc = b + BitVec.ofNat 64 (4 * 6103) := by simpa using hpcB
  refine step_b_seg5 (disp := 20#64) nr_init_clamp06 (by decide) (by decide) (by decide)
    fw_6103 hpcB' hrunB ?_
  let pcS0 := pcAt (b + BitVec.ofNat 64 (4 * 6104)) 4
  have hs0_eq : sB.setPC (b + BitVec.ofNat 64 (4 * 6103) + 20#64) =
      sB.setPC pcS0 := congrArg sB.setPC (by dsimp only [pcS0, pcAt]; bv_omega)
  rw [hs0_eq]
  let s0 := sB.setPC pcS0
  have hsite : SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 6308)) s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        BTreeMem (sp + 30448#64) 252 tB ∗ MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
        MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 28368#64) 672 ∗ Rest)
      (fun s1 P1 =>
        SitePreserved rejCfgInit3_06 s0 s1 ∧
        ∃ sampled' hws',
          MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) 0 sampled' hws' ∧
          (P1 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (sp + 144#64) 286 tA ∗
              (MultiLaneSampled (sp + 26320#64) 4 sampled' ∗
                (MultiLaneSlots (sp + 4160#64) 544 4 hws' ∗
                  memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest))))) := by
    refine SepWP.weaken_pre (by sep_frame : _ ⊢ BTreeMem (sp + 30448#64) 252 tB ∗
      (MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
        (MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
          ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
            memRegion (sp + 28368#64) 672 ∗ Rest)))) ?_
    refine step_rej_site_init3 (pcBase := b + BitVec.ofNat 64 (4 * 6104))
      (sqBase := sp + 30448#64) (sampBase := sp + 26320#64)
      (slotsBase := sp + 4160#64) (cfg := rejCfgInit3_06)
      (seeds := fun c => rowSeed rho row c) (bufs := fun c => btreeBytesFrom (63 * c) 63 tB)
      rfl ((status_setPC sB _).trans hrunB) rejCfgInit3_06_valid rfl
      (fetches_rejInit3_06_outer b) (fetches_rejInit3_06_inner b)
      (fun i hi => rejBufReadable_of_btreeMem (offWords := 63 * i)
        (by dsimp only [rejCfgInit3_06]; bv_omega) (by dsimp only [rejCfgInit3_06] at hi ⊢; omega) rfl)
      (fun i _ => by rw [btreeBytesFrom_length]; decide)
      (fun i hi => by
        have hlen : (btreeBytesFrom (63 * i) 63 tB).length = 504 := by rw [btreeBytesFrom_length]
        rw [List.take_of_length_le (by omega)]
        exact hsqB i (by dsimp only [rejCfgInit3_06] at hi; exact hi))
      (MultiLaneClampedInv.init_zero 4).toRaw
      ((readReg64_setPC sB _ _).trans hx8B)
      (by dsimp only [s0, rejCfgInit3_06]; rw [readReg64_setPC, hx9B]; bv_omega)
      ((readReg64_setPC sB _ _).trans hgprsB.2.2.2.2.1)
      ((readReg64_setPC sB _ _).trans hgprsB.1)
      ((readReg64_setPC sB _ _).trans hgprsB.2.2.2.1)
      fun sF sampled' hws' hp hraw => ?_
    have hpcF : (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 6104)) 204)).pc =
        b + BitVec.ofNat 64 (4 * 6308) := by
      dsimp only [State.setPC, pcAt]; bv_omega
    have hp1 : SitePreserved rejCfgInit3_06 s0 (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 6104)) 204)) :=
      ⟨(status_setPC sF _).trans hp.1, (sp_setPC sF _).trans hp.2.1,
       (vregs_setPC sF _).trans hp.2.2.1,
       fun r hr => (readReg64_setPC sF _ r).trans (hp.2.2.2 r hr)⟩
    refine SepWP.done hpcF ((status_setPC sF _).trans hp.1) ⟨hp1, sampled', hws', hraw, ?_⟩
    have h2016 : BTreeMem (sp + 30448#64) 252 tB ⊢ memRegion (sp + 30448#64) 2016 :=
      BTreeMem_entails_memRegion (sp + 30448#64) 252 tB
    exact Entails.trans (sepConj_mono_left h2016) (by sep_frame)
  have hmem0 : s0.mem = sB.mem := mem_setPC sB pcS0
  have hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem := by rw [hmem0]; exact hclB
  have hro0 : MlKemRoOk mlkemMpl s0.mem := by rw [hmem0]; exact hroB
  refine sepWP_seq_env hcl0 hro0 hsite fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hp, sampled', hws', hraw, hP1⟩ => ?_
  have hgprs0 : RowCalleeGprs06 sp rcBase fpVal row s0 := rowCalleeGprs06_setPC pcS0 hgprsB
  have hsp0 : s0.sp = sp := (sp_setPC sB pcS0).trans hspB
  have hspA0 : s0.spAligned = true := (spAligned_setPC sB pcS0).trans hspAB
  have hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp],
      r ∉ rejCfgInit3_06.siteClobberedRegs :=
    @of_decide_eq_true _ (decBallNotMem rejCfgInit3_06.siteClobberedRegs
      [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp]) rfl
  obtain ⟨_, hsp1, hspA1, hgprs1, hx1_1, hsl_tr⟩ :=
    sitePreserved_row06 (pc := s1.pc) (cfgS := cfgC06) (tA := tA) hp hsp0 hspA0 hgprs0 hclob
  have hs1_eq : s1.setPC s1.pc = s1 := by cases s1; rfl
  rw [hs1_eq] at hsp1 hspA1 hgprs1 hx1_1 hsl_tr
  have hx1_s1 : s1.readReg64 .x1 = BitVec.ofNat 64 (row + 1) :=
    hx1_1.trans ((readReg64_setPC sB pcS0 .x1).trans hx1B)
  refine SepWP.weaken_pre hP1 ?_
  exact step_post_init3_clamp06 hpc1 hrun1 hsp1 hspA1 hsp16 hcl1 hro1 hgprs1 hhdrB hx1_s1
    (fun idx hidx => hsl_tr _ _ _ (slotHolds_setPC pcS0
      ((slotHolds_congr_cfg rfl).mp (hsl01B idx hidx))))
    (fun idx hidx => hsl_tr _ _ _ (slotHolds_setPC pcS0
      ((slotHolds_congr_cfg rfl).mp (hsl23B idx hidx)))) hraw

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init
