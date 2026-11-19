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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Row Initialization (`Seg2Init`)

Composes `seg2_initA_ok`, `seg2_initB_ok`, 3-block `step_rej_site_init3`, and the 4 post-site
clamp/branch paths (`+0x28f4 → +0x3770 / +0x29ac`) into `seg2_init_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakAbsorb keccakF1600 keccakPermuteN
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneClampedInv MultiLaneSampled MultiLaneSlots
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  SitePreserved decBallNotMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone allLanesDone_eq_false_iff
  allLanesDone_eq_true_iff step_rej_site_init3
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  condCC_256_of_le271 condHI_255_of_le271 raw_sampled_le271
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blkPC07 blkPl07 fetchWordTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KEnv KSlot KState evalKExpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMem_entails_memRegion KSpatial blk07NoRelocInRange btreeBytesFrom
  btreeBytesFrom_length evalMemTree
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval (matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  rejBufReadable_of_btreeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowCalleeGprs RowExitState RowExtraState cfgB cfgC
  fetches_rejInit3_inner fetches_rejInit3_outer rejCfgInit3 rejCfgInit3_valid
  slotsInv01 slotsInv23 slotsMidInit01 slotsMidInit23
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (seg2_initA_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB (seg2_initB_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp (
  ClampMatches ClampState cfgClamp cfgClamp_valid checkClampCommon checkSlotsMoved csInitClamp
  envClamp envClamp_valid extract_clamp_common extract_slots_moved runClampRange
  sepWP_of_runClampRange sitePreserved_row slotHolds_congr_cfg stRawClamp_matches
  step_bCond_seg2 step_b_seg2
)

attribute [local irreducible] blkPC07 mlkemMultiLib keccakF1600 keccakAbsorb BTreeMem allLanesDone

/-! ## 1. Post-Init3 Clamp Certificates & Exit/Loop Packaging (`+0x28f4 → +0x3770 / +0x29ac`) -/

@[expose] def checkClampFull (slots01 slots23 : List KSlot) (stEnd : KState) : Bool :=
  checkClampCommon stEnd &&
  checkSlotsMoved slots01 slotsInv01 stEnd &&
  checkSlotsMoved slots23 slotsInv23 stEnd

@[expose] def csInit2647 : ClampState := (runClampRange cfgClamp 2621 26 csInitClamp).getD csInitClamp
@[expose] def csInitEnd1 : ClampState := (runClampRange cfgClamp 2659 4 csInit2647).getD csInitClamp
@[expose] def csInit2650 : ClampState := (runClampRange cfgClamp 2648 2 csInit2647).getD csInitClamp
@[expose] def csInitEnd2 : ClampState := (runClampRange cfgClamp 2664 3 csInit2650).getD csInitClamp
@[expose] def csInit2652 : ClampState := (runClampRange cfgClamp 2651 1 csInit2650).getD csInitClamp
@[expose] def csInitEnd3 : ClampState := (runClampRange cfgClamp 2664 3 csInit2652).getD csInitClamp
@[expose] def csInit2657 : ClampState := (runClampRange cfgClamp 2653 4 csInit2652).getD csInitClamp

theorem run_init2647 : runClampRange cfgClamp 2621 26 csInitClamp = some csInit2647 := by rfl_kernel
theorem cmp_init2647 : csInit2647.cmpOpt = some (.var 803, 256#64) := by rfl_kernel
theorem run_initEnd1 : runClampRange cfgClamp 2659 4 csInit2647 = some csInitEnd1 := by rfl_kernel
theorem chk_initEnd1 : checkClampFull slotsMidInit01 slotsMidInit23 csInitEnd1.st = true := by rfl_kernel
theorem run_init2650 : runClampRange cfgClamp 2648 2 csInit2647 = some csInit2650 := by rfl_kernel
theorem cmp_init2650 : csInit2650.cmpOpt = some (.var 802, 256#64) := by rfl_kernel
theorem run_initEnd2 : runClampRange cfgClamp 2664 3 csInit2650 = some csInitEnd2 := by rfl_kernel
theorem chk_initEnd2 : checkClampFull slotsMidInit01 slotsMidInit23 csInitEnd2.st = true := by rfl_kernel
theorem run_init2652 : runClampRange cfgClamp 2651 1 csInit2650 = some csInit2652 := by rfl_kernel
theorem cmp_init2652 : csInit2652.cmpOpt = some (.var 801, 256#64) := by rfl_kernel
theorem run_initEnd3 : runClampRange cfgClamp 2664 3 csInit2652 = some csInitEnd3 := by rfl_kernel
theorem chk_initEnd3 : checkClampFull slotsMidInit01 slotsMidInit23 csInitEnd3.st = true := by rfl_kernel
theorem run_init2657 : runClampRange cfgClamp 2653 4 csInit2652 = some csInit2657 := by rfl_kernel
theorem cmp_init2657 : csInit2657.cmpOpt = some (.var 800, 255#64) := by rfl_kernel
theorem chk_init2657 : checkClampFull slotsMidInit01 slotsMidInit23 csInit2657.st = true := by rfl_kernel
theorem chk_init2657_common : checkClampCommon csInit2657.st = true := by rfl_kernel

private theorem fw_2416 : fetchWordTree07 2416 = some (.b 20#64) := by rfl_kernel
private theorem fw_2647 : fetchWordTree07 2647 = some (.bCond .CC 48#64) := by rfl_kernel
private theorem fw_2650 : fetchWordTree07 2650 = some (.bCond .CC 56#64) := by rfl_kernel
private theorem fw_2652 : fetchWordTree07 2652 = some (.bCond .CC 48#64) := by rfl_kernel
private theorem fw_2657 : fetchWordTree07 2657 = some (.bCond .HI 3564#64) := by rfl_kernel
private theorem fw_2658 : fetchWordTree07 2658 = some (.b 36#64) := by rfl_kernel
private theorem fw_2663 : fetchWordTree07 2663 = some (.b 16#64) := by rfl_kernel

attribute [local irreducible]
  csInit2647 csInitEnd1 csInit2650 csInitEnd2 csInit2652 csInitEnd3 csInit2657

theorem eval_envClamp_800 {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat} {c : Nat} (hc : c < 4) :
    evalKExpr (envClamp sp rcBase rho row s tA sampled') (.var (800 + c)) =
      BitVec.ofNat 64 (sampled' c) := by
  simp only [evalKExpr, envClamp, show ¬(800 + c < 800) by omega,
    show 800 + c < 804 by omega, ↓reduceIte, show 800 + c - 800 = c by omega]

theorem finish_clamp_loop [MlKemPlacement] {b sp rcBase : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s sf : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    {slots01 slots23 : List KSlot} {csEnd : ClampState}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hv01 : slots01.all (KeccakLoop.slotValid cfgClamp) = true) (hl01 : slots01.length = 25)
    (hv23 : slots23.all (KeccakLoop.slotValid cfgClamp) = true) (hl23 : slots23.length = 25)
    (hslots01 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slots01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hslots23 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slots23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled' hws')
    (hdoneF : allLanesDone 4 (fun c => rowSeed rho row c) extra = false)
    (hchk : checkClampFull slots01 slots23 csEnd.st = true)
    (hpc : sf.pc = b + BitVec.ofNat 64 (4 * 2667)) (hrun : sf.status = .Running)
    (hm : ClampMatches (envClamp sp rcBase rho row s tA sampled') csEnd sf) :
    let F := MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) extra then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      sf (KSpatial cfgClamp (envClamp sp rcBase rho row s tA sampled') csEnd.st F)
      (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
        if allLanesDone 4 (fun c => rowSeed rho row c) extra then
          RowExitState sp rcBase rho row Rest sf' Pf
        else RowExtraState b sp rcBase rho row Rest extra sf' Pf) := by
  intro F
  simp only [checkClampFull, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hcomm, hm01⟩, hm23⟩
  rcases extract_clamp_common hm.1 hx1 hcomm (F := F) with ⟨hhdr', hgpr', hx1', hspOut⟩
  have hs01 := extract_slots_moved (sampled' := sampled') hsp hspA hgprs hhdr hm.1 hv01 hl01 (by decide) rfl hslots01 hm01
  have hs23 := extract_slots_moved (sampled' := sampled') hsp hspA hgprs hhdr hm.1 hv23 hl23 (by decide) rfl hslots23 hm23
  simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
  refine SepWP.done hpc hrun fun hcl hro => ⟨?_, hrun, hm.1.hsp, hm.1.hsp_al, hsp16, hcl, hro, hgpr', hx1',
    _, _, _, hhdr', hs01, hs23, hraw.clamp, ?_⟩
  · simpa using hpc
  · rw [hspOut]; dsimp only [F]; sep_frame

theorem finish_clamp_exit [MlKemPlacement] {b sp rcBase : BitVec 64} {rho : List (BitVec 8)}
    {row extra : Nat} {Rest : SepProp} {s sf : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)} {csEnd : ClampState}
    (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled' hws')
    (hdoneT : allLanesDone 4 (fun c => rowSeed rho row c) extra = true)
    (hchk : checkClampCommon csEnd.st = true)
    (hpc : sf.pc = b + BitVec.ofNat 64 (4 * 3548)) (hrun : sf.status = .Running)
    (hm : ClampMatches (envClamp sp rcBase rho row s tA sampled') csEnd sf) :
    let F := MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) extra then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      sf (KSpatial cfgClamp (envClamp sp rcBase rho row s tA sampled') csEnd.st F)
      (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
        if allLanesDone 4 (fun c => rowSeed rho row c) extra then
          RowExitState sp rcBase rho row Rest sf' Pf
        else RowExtraState b sp rcBase rho row Rest extra sf' Pf) := by
  intro F
  rcases extract_clamp_common hm.1 hx1 hchk (F := F) with ⟨hhdr', hgpr', hx1', hspOut⟩
  simp only [hdoneT, ↓reduceIte]
  refine SepWP.done hpc hrun fun hcl hro => ⟨hm.1.hsp, hm.1.hsp_al, hsp16, hcl, hro, hgpr', hx1',
    extra, _, _, _, hhdr', hraw.clamp, hdoneT, ?_⟩
  rw [hspOut]; dsimp only [F]; sep_frame

theorem clampMatches_setPC {env : KEnv} {cs : ClampState} {s : State} (pc : BitVec 64)
    (hm : ClampMatches env cs s) : ClampMatches env cs (s.setPC pc) :=
  ⟨matches_setPC hm.1 pc, hm.2.1, by
    have hp := hm.2.2; cases h : cs.cmpOpt <;> simp [Seg2Clamp.ClampCmpMatches, h] at hp ⊢; exact hp⟩

theorem allLanesDone4_false_of_lt256 {seeds : Nat → List (BitVec 8)} {extra c : Nat}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawXofInv 4 seeds extra sampled' hws') (hc : c < 4) (hlt : sampled' c < 256) :
    allLanesDone 4 seeds extra = false := by
  rw [allLanesDone_eq_false_iff]
  exact ⟨c, hc, (hraw.lt256_iff hc).mp hlt⟩

theorem allLanesDone4_true_of_ge256 {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawXofInv 4 seeds extra sampled' hws')
    (h0 : 256 ≤ sampled' 0) (h1 : 256 ≤ sampled' 1) (h2 : 256 ≤ sampled' 2) (h3 : 256 ≤ sampled' 3) :
    allLanesDone 4 seeds extra = true := by
  rw [hraw.allLanesDone_iff_ge256]
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> assumption

theorem with_frozen_env [MlKemPlacement] {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf =>
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem → post sf Pf)) :
    SepWP prog tgt s P post :=
  SepWP.mono_frozen (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
    ⟨hcl, hro⟩ h (fun _ _ _ _ ⟨hc, hr⟩ hp => hp hc hr)

private theorem nr_init_clamp : blk07NoRelocInRange 2416 2667 = true := by rfl_kernel

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

theorem step_post_init3_clamp [MlKemPlacement] {b sp rcBase : BitVec 64} {rho : List (BitVec 8)}
    {row : Nat} {Rest : SepProp} {s : State} {tA : BTree (BitVec 64) 9}
    {sampled' : Nat → Nat} {hws' : Nat → List (BitVec 16)}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 2621)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hsl01 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slotsMidInit01.getD idx (.vreg 0))
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64))
    (hsl23 : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slotsMidInit23.getD idx (.vreg 0))
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64))
    (hraw : MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) 0 sampled' hws') :
    let F := MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      s ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗ (MultiLaneSampled (sp + 24720#64) 4 sampled' ∗ F)))
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState sp rcBase rho row Rest sf Pf
        else RowExtraState b sp rcBase rho row Rest 0 sf Pf) := by
  intro F
  have hsamp271 : ∀ c, c < 4 → sampled' c ≤ 271 := fun c hc => raw_sampled_le271 hraw hc
  have henvV := envClamp_valid (sp := sp) (rcBase := rcBase) (rho := rho) (row := row)
    (s := s) (tA := tA) hsamp271
  obtain ⟨hm0, hspEq0⟩ := stRawClamp_matches (sampled' := sampled') hsp hspA hgprs hhdr F
  rw [← hspEq0]
  have hloop : ∀ {csEnd : ClampState} {sf : State},
      allLanesDone 4 (fun c => rowSeed rho row c) 0 = false →
      checkClampFull slotsMidInit01 slotsMidInit23 csEnd.st = true →
      sf.pc = b + BitVec.ofNat 64 (4 * 2667) → sf.status = .Running →
      ClampMatches (envClamp sp rcBase rho row s tA sampled') csEnd sf →
      SepWP (blkPC07.rebase b (fun _ => none))
        (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 3548)
         else b + BitVec.ofNat 64 (4 * 2667))
        sf (KSpatial cfgClamp (envClamp sp rcBase rho row s tA sampled') csEnd.st F)
        (fun sf' Pf => mlkemMultiLib.CodeLoaded mlkemMpl sf'.mem → MlKemRoOk mlkemMpl sf'.mem →
          if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState sp rcBase rho row Rest sf' Pf
          else RowExtraState b sp rcBase rho row Rest 0 sf' Pf) := fun hd hc hp hr hm =>
    finish_clamp_loop (extra := 0) (Rest := Rest) hsp hspA hsp16 hgprs hhdr hx1
      (by decide) rfl (by decide) rfl hsl01 hsl23 hraw hd hc hp hr hm
  refine with_frozen_env hcl hro ?_
  refine sepWP_of_runClampRange cfgClamp_valid henvV 26 2621 nr_init_clamp (by decide)
    (by decide) (by decide) run_init2647 hm0 hpc hrun fun s1 hpc1 hrun1 hm1 => ?_
  refine step_bCond_seg2 (cond := .CC) (disp := 48#64) nr_init_clamp (by decide) (by decide)
    (by decide) fw_2647 hpc1 hrun1 (fun hT3 => ?_) (fun hF3 => ?_)
  · have hlt3 : sampled' 3 < 256 := by
      have hp := hm1.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2647] at hp
      rw [eval_envClamp_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_true_eq] at hT3; exact hT3
    refine sepWP_of_runClampRange cfgClamp_valid henvV 4 2659 nr_init_clamp (by decide)
      (by decide) (by decide) run_initEnd1 (clampMatches_setPC _ hm1) (by dsimp only [State.setPC]; bv_omega)
      ((status_setPC s1 _).trans hrun1) fun sE hpcE hrunE hmE => ?_
    refine step_b_seg2 (disp := 16#64) nr_init_clamp (by decide) (by decide) (by decide)
      fw_2663 hpcE hrunE ?_
    exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt3) chk_initEnd1
      (by dsimp only [State.setPC]; bv_omega) ((status_setPC sE _).trans hrunE) (clampMatches_setPC _ hmE)
  · have hge3 : 256 ≤ sampled' 3 := by
      have hp := hm1.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2647] at hp
      rw [eval_envClamp_800 (c := 3) (by decide)] at hp
      rw [hp, condCC_256_of_le271 (hsamp271 3 (by decide)), decide_eq_false_iff_not] at hF3; omega
    refine sepWP_of_runClampRange cfgClamp_valid henvV 2 2648 nr_init_clamp (by decide)
      (by decide) (by decide) run_init2650 (clampMatches_setPC _ hm1)
      (by dsimp only [State.setPC]) ((status_setPC s1 _).trans hrun1) fun s2 hpc2 hrun2 hm2 => ?_
    refine step_bCond_seg2 (cond := .CC) (disp := 56#64) nr_init_clamp (by decide) (by decide)
      (by decide) fw_2650 hpc2 hrun2 (fun hT2 => ?_) (fun hF2 => ?_)
    · have hlt2 : sampled' 2 < 256 := by
        have hp := hm2.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2650] at hp
        rw [eval_envClamp_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_true_eq] at hT2; exact hT2
      refine sepWP_of_runClampRange cfgClamp_valid henvV 3 2664 nr_init_clamp (by decide)
        (by decide) (by decide) run_initEnd2 (clampMatches_setPC _ hm2) (by dsimp only [State.setPC]; bv_omega)
        ((status_setPC s2 _).trans hrun2) fun sE hpcE hrunE hmE =>
        hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt2) chk_initEnd2 hpcE hrunE hmE
    · have hge2 : 256 ≤ sampled' 2 := by
        have hp := hm2.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2650] at hp
        rw [eval_envClamp_800 (c := 2) (by decide)] at hp
        rw [hp, condCC_256_of_le271 (hsamp271 2 (by decide)), decide_eq_false_iff_not] at hF2; omega
      refine sepWP_of_runClampRange cfgClamp_valid henvV 1 2651 nr_init_clamp (by decide)
        (by decide) (by decide) run_init2652 (clampMatches_setPC _ hm2)
        (by dsimp only [State.setPC]) ((status_setPC s2 _).trans hrun2) fun s3 hpc3 hrun3 hm3 => ?_
      refine step_bCond_seg2 (cond := .CC) (disp := 48#64) nr_init_clamp (by decide) (by decide)
        (by decide) fw_2652 hpc3 hrun3 (fun hT1 => ?_) (fun hF1 => ?_)
      · have hlt1 : sampled' 1 < 256 := by
          have hp := hm3.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2652] at hp
          rw [eval_envClamp_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_true_eq] at hT1; exact hT1
        refine sepWP_of_runClampRange cfgClamp_valid henvV 3 2664 nr_init_clamp (by decide)
          (by decide) (by decide) run_initEnd3 (clampMatches_setPC _ hm3) (by dsimp only [State.setPC]; bv_omega)
          ((status_setPC s3 _).trans hrun3) fun sE hpcE hrunE hmE =>
          hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt1) chk_initEnd3 hpcE hrunE hmE
      · have hge1 : 256 ≤ sampled' 1 := by
          have hp := hm3.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2652] at hp
          rw [eval_envClamp_800 (c := 1) (by decide)] at hp
          rw [hp, condCC_256_of_le271 (hsamp271 1 (by decide)), decide_eq_false_iff_not] at hF1; omega
        refine sepWP_of_runClampRange cfgClamp_valid henvV 4 2653 nr_init_clamp (by decide)
          (by decide) (by decide) run_init2657 (clampMatches_setPC _ hm3)
          (by dsimp only [State.setPC]) ((status_setPC s3 _).trans hrun3) fun s4 hpc4 hrun4 hm4 => ?_
        refine step_bCond_seg2 (cond := .HI) (disp := 3564#64) nr_init_clamp (by decide) (by decide)
          (by decide) fw_2657 hpc4 hrun4 (fun hT0 => ?_) (fun hF0 => ?_)
        · have hge0 : 256 ≤ sampled' 0 := by
            have hp := hm4.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2657] at hp
            rw [eval_envClamp_800 (c := 0) (by decide)] at hp
            rw [hp, condHI_255_of_le271 (hsamp271 0 (by decide)), decide_eq_true_eq] at hT0; exact hT0
          have hdT := allLanesDone4_true_of_ge256 hraw hge0 hge1 hge2 hge3
          have hpcEx : (s4.setPC (b + BitVec.ofNat 64 (4 * 2657) + 3564#64)).pc =
              b + BitVec.ofNat 64 (4 * 3548) := by dsimp only [State.setPC]; bv_omega
          exact finish_clamp_exit (Rest := Rest) hsp16 hx1 hraw hdT chk_init2657_common hpcEx
            ((status_setPC s4 _).trans hrun4) (clampMatches_setPC _ hm4)
        · have hlt0 : sampled' 0 < 256 := by
            have hp := hm4.2.2; simp only [Seg2Clamp.ClampCmpMatches, cmp_init2657] at hp
            rw [eval_envClamp_800 (c := 0) (by decide)] at hp
            rw [hp, condHI_255_of_le271 (hsamp271 0 (by decide)), decide_eq_false_iff_not] at hF0; omega
          refine step_b_seg2 (disp := 36#64) nr_init_clamp (by decide) (by decide) (by decide)
            fw_2658 (by dsimp only [State.setPC]) ((status_setPC s4 _).trans hrun4) ?_
          exact hloop (allLanesDone4_false_of_lt256 hraw (by decide) hlt0) chk_init2657
            (by dsimp only [State.setPC]; bv_omega)
            ((status_setPC _ _).trans ((status_setPC s4 _).trans hrun4))
            (clampMatches_setPC _ (clampMatches_setPC _ hm4))


/-! ## 2. Full Row Initialization `seg2_init_ok` (`+0x07d8 → +0x3770 / +0x29ac`) -/

theorem seg2_init_ok [MlKemPlacement] {b sp rcBase : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 2008) (hrun : s.status = .Running)
    (hpre : Seg2InitA.RowInitAPre sp rcBase rho row Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if allLanesDone 4 (fun c => rowSeed rho row c) 0 then b + BitVec.ofNat 64 (4 * 3548)
       else b + BitVec.ofNat 64 (4 * 2667))
      s P
      (fun sf Pf =>
        if allLanesDone 4 (fun c => rowSeed rho row c) 0 then RowExitState sp rcBase rho row Rest sf Pf
        else RowExtraState b sp rcBase rho row Rest 0 sf Pf) := by
  refine SepWP.seq (seg2_initA_ok hb hbase hrho hrow hpc hrun hpre) fun sA PA hpcA hrunA hpostA => ?_
  refine SepWP.seq (seg2_initB_ok hb hrho hpcA hrunA hpostA) fun sB PB hpcB hrunB hpostB => ?_
  rcases hpostB with ⟨hspB, hspAB, hsp16, hclB, hroB, hgprsB, hx1B, hx8B, hx9B,
    tA, tB, hhdrB, hsqB, hsl01B, hsl23B, hPB⟩
  refine SepWP.weaken_pre hPB ?_
  have hpcB' : sB.pc = b + BitVec.ofNat 64 (4 * 2416) := by simpa using hpcB
  refine step_b_seg2 (disp := 20#64) nr_init_clamp (by decide) (by decide) (by decide)
    fw_2416 hpcB' hrunB ?_
  have hs0_eq : sB.setPC (b + BitVec.ofNat 64 (4 * 2416) + 20#64) =
      sB.setPC (b + BitVec.ofNat 64 9684) := congrArg sB.setPC (by bv_omega)
  rw [hs0_eq]
  let s0 := sB.setPC (b + BitVec.ofNat 64 9684)
  have hsite : SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 2621)) s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        BTreeMem (sp + 28848#64) 252 tB ∗ MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
        MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 26768#64) 672 ∗ Rest)
      (fun s1 P1 =>
        SitePreserved rejCfgInit3 s0 s1 ∧
        ∃ sampled' hws',
          MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) 0 sampled' hws' ∧
          (P1 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (sp + 144#64) 286 tA ∗
              (MultiLaneSampled (sp + 24720#64) 4 sampled' ∗
                (MultiLaneSlots (sp + 2560#64) 544 4 hws' ∗
                  memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest))))) := by
    refine SepWP.weaken_pre (by sep_frame : _ ⊢ BTreeMem (sp + 28848#64) 252 tB ∗
      (MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
        (MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
          ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
            memRegion (sp + 26768#64) 672 ∗ Rest)))) ?_
    refine step_rej_site_init3 (pcBase := b + BitVec.ofNat 64 (4 * 2417))
      (sqBase := sp + BitVec.ofNat 64 28848) (sampBase := sp + BitVec.ofNat 64 24720)
      (slotsBase := sp + 2560#64) (cfg := rejCfgInit3)
      (seeds := fun c => rowSeed rho row c) (bufs := fun c => btreeBytesFrom (63 * c) 63 tB)
      (by dsimp only [s0, State.setPC, pcAt]; bv_omega)
      ((status_setPC sB _).trans hrunB) rejCfgInit3_valid rfl
      (fetches_rejInit3_outer b) (fetches_rejInit3_inner b)
      (fun i hi => rejBufReadable_of_btreeMem (offWords := 63 * i)
        (by dsimp only [rejCfgInit3]; bv_omega) (by dsimp only [rejCfgInit3] at hi ⊢; omega) rfl)
      (fun i _ => by rw [btreeBytesFrom_length]; decide)
      (fun i hi => by
        have hlen : (btreeBytesFrom (63 * i) 63 tB).length = 504 := by rw [btreeBytesFrom_length]
        rw [List.take_of_length_le (by omega)]
        exact hsqB i (by dsimp only [rejCfgInit3] at hi; exact hi))
      (MultiLaneClampedInv.init_zero 4).toRaw
      ((readReg64_setPC sB _ _).trans hx8B)
      (by dsimp only [s0, rejCfgInit3]; rw [readReg64_setPC, hx9B]; bv_omega)
      ((readReg64_setPC sB _ _).trans hgprsB.2.2.2.2.2.2.2.1)
      ((readReg64_setPC sB _ _).trans hgprsB.2.2.2.2.2.2.2.2.1)
      ((readReg64_setPC sB _ _).trans hgprsB.1)
      fun sF sampled' hws' hp hraw => ?_
    have hpcF : (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 2417)) 204)).pc =
        b + BitVec.ofNat 64 (4 * 2621) := by
      dsimp only [State.setPC, pcAt]; bv_omega
    have hp1 : SitePreserved rejCfgInit3 s0 (sF.setPC (pcAt (b + BitVec.ofNat 64 (4 * 2417)) 204)) :=
      ⟨(status_setPC sF _).trans hp.1, (sp_setPC sF _).trans hp.2.1,
       (vregs_setPC sF _).trans hp.2.2.1,
       fun r hr => (readReg64_setPC sF _ r).trans (hp.2.2.2 r hr)⟩
    refine SepWP.done hpcF ((status_setPC sF _).trans hp.1) ⟨hp1, sampled', hws', hraw, ?_⟩
    have h2016 : BTreeMem (sp + 28848#64) 252 tB ⊢ memRegion (sp + 28848#64) 2016 :=
      BTreeMem_entails_memRegion (sp + 28848#64) 252 tB
    exact Entails.trans (sepConj_mono_left h2016) (by sep_frame)
  have hmem0 : s0.mem = sB.mem := mem_setPC sB (b + BitVec.ofNat 64 9684)
  have hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem := by rw [hmem0]; exact hclB
  have hro0 : MlKemRoOk mlkemMpl s0.mem := by rw [hmem0]; exact hroB
  refine sepWP_seq_env hcl0 hro0 hsite fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hp, sampled', hws', hraw, hP1⟩ => ?_
  have hgprs0 : RowCalleeGprs sp rcBase row s0 := rowCalleeGprs_setPC (b + BitVec.ofNat 64 9684) hgprsB
  have hsp0 : s0.sp = sp := (sp_setPC sB (b + BitVec.ofNat 64 9684)).trans hspB
  have hspA0 : s0.spAligned = true := (spAligned_setPC sB (b + BitVec.ofNat 64 9684)).trans hspAB
  have hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp],
      r ∉ rejCfgInit3.siteClobberedRegs :=
    @of_decide_eq_true _ (decBallNotMem rejCfgInit3.siteClobberedRegs
      [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp]) rfl
  obtain ⟨_, hsp1, hspA1, hgprs1, hx1_1, hsl_tr⟩ :=
    sitePreserved_row (pc := s1.pc) (cfgS := cfgC) (tA := tA) hp hsp0 hspA0 hgprs0 hclob
  have hs1_eq : s1.setPC s1.pc = s1 := by cases s1; rfl
  rw [hs1_eq] at hsp1 hspA1 hgprs1 hx1_1 hsl_tr
  have hx1_s1 : s1.readReg64 .x1 = BitVec.ofNat 64 (row + 1) :=
    hx1_1.trans ((readReg64_setPC sB (b + BitVec.ofNat 64 9684) .x1).trans hx1B)
  refine SepWP.weaken_pre hP1 ?_
  exact step_post_init3_clamp hpc1 hrun1 hsp1 hspA1 hsp16 hcl1 hro1 hgprs1 hhdrB hx1_s1
    (fun idx hidx => hsl_tr _ _ _ (slotHolds_setPC (b + BitVec.ofNat 64 9684)
      ((slotHolds_congr_cfg rfl).mp (hsl01B idx hidx))))
    (fun idx hidx => hsl_tr _ _ _ (slotHolds_setPC (b + BitVec.ofNat 64 9684)
      ((slotHolds_congr_cfg rfl).mp (hsl23B idx hidx)))) hraw

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init
