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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit

/-!
# `encapsulate1_serialized` (`B03`) — `Seg2` Row Init Step (`+0x0504 → +0x026c / +0x2580`)

Combines `seg2_row_header_memset`, `sepWP_of_runAndCheckKProg` (`stepsInit`),
`step_rej_site_init3`, and `seg2_row_clamp_init3` into `seg2_row_init_wp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowStep

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakExtractRate keccakF1600 keccakZeroState shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneClampedInv MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  decMemReg rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone step_rej_site_init3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blkPC03 blkPl03 sepWP_with_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeWords checkInstrsAt03 fetchesInstrsAt_blk03_seg2b seedConstsWords sepWP_elim_treeMem
  treeMem_entails_memRegion wordsToBytes wordsToBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KConstsLoOpt KSpatial KStateMatches evalMemTree matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  readSlot slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  btreeWords_split rejBufReadable_of_treeMem wordsToBytes_append
  wordsToBytes_btreeWords_eq_extractRate_21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  Seg2LoopState Seg2RowExit cfgClamp cfgInit cfgInit_wf cfgRejInit3 cfgRejInit3_valid
  exprVarsOk keccakRc_intro rowPermState rowSeeds runAndCheckKProg
  shake128FirstBlocks_rowSeeds_three specEnvSteps step_b_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner (
  eval_checked_gpr eval_checked_memB eval_checked_slot sepWP_of_runAndCheckKProg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp (
  checkSeedConstsMemA checkSegRegGprs extract_seedConsts extract_segRegInv
  mkSegEnv mkSegState_matches preClamp01Slots preClamp2Slots sepWP_drop_left with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit (
  pc_add_eq pc_of_eq seg2_row_clamp_init3 seg2_row_header_memset
  segRegInv_of_sitePreserved setPC_disp_eq slotHolds_of_sitePreserved
  specEnv_stepsInit_vars stInit0 stepsInit)

attribute [local irreducible] keccakF1600 blkPC03

@[expose] def chkSq21 (ok : Nat → Bool) (st : KState) (start base : Nat) : Bool :=
  (List.range 21).all fun j =>
    (st.memB.get (start + j)).beq (.var (base + j)) && ok (base + j)

@[expose] def chkSlotsPair25 (ok : Nat → Bool) (st : KState) (slots : List KSlot)
    (bLo bHi : Nat) : Bool :=
  (List.range 25).all fun idx =>
    let sl := slots.getD idx (.vreg 0)
    slotValid cfgClamp sl &&
      (readSlot cfgClamp st sl).1.beq (.var (bLo + idx)) &&
      (readSlot cfgClamp st sl).2.beq (.var (bHi + idx)) &&
      ok (bLo + idx) && ok (bHi + idx)

@[expose] def chkSlotsSingle25 (ok : Nat → Bool) (st : KState) (slots : List KSlot)
    (bLo : Nat) : Bool :=
  (List.range 25).all fun idx =>
    let sl := slots.getD idx (.vreg 0)
    slotValid cfgClamp sl &&
      (readSlot cfgClamp st sl).1.beq (.var (bLo + idx)) &&
      (readSlot cfgClamp st sl).2.beq (.const64 0#64) &&
      ok (bLo + idx)

private def chkInitHdr (ok : Nat → Bool) (st : KState) : Bool :=
  (checkSegRegGprs st (.add64 (.var 96) (.const64 1#64)) && ok 96) &&
  (checkSeedConstsMemA st && (ok 97 && ok 98 && ok 99 && ok 100)) &&
  ((st.gprs.get 9).beq (.const64 0#64) && (st.gprs.get 10).beq (.spAdd 2203#64))

private def chkInitSq (ok : Nat → Bool) (st : KState) : Bool :=
  (chkSq21 ok st 0 2000 && chkSq21 ok st 21 4000 && chkSq21 ok st 42 5000) &&
  (chkSq21 ok st 63 2025 && chkSq21 ok st 84 4025 && chkSq21 ok st 105 5025) &&
  (chkSq21 ok st 126 3000 && chkSq21 ok st 147 6000 && chkSq21 ok st 168 7000)

private def chkInitPost (ok : Nat → Bool) (st : KState) : Bool :=
  chkInitHdr ok st && chkInitSq ok st &&
  (chkSlotsPair25 ok st preClamp01Slots 5000 5025 && chkSlotsSingle25 ok st preClamp2Slots 7000)

private theorem cert_stepsInit :
    runAndCheckKProg cfgInit 330 2163 330 2163 1000 stepsInit stInit0 chkInitPost = true := by
  decide +kernel

theorem extract_sq21 {ok : Nat → Bool} {envFinal envSpec : KEnv} {st : KState}
    {start base : Nat} {ks : KeccakState}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hvars : ∀ j, j < 25 → envSpec.vars (base + j) = ks.getD j 0#64)
    (hchk : chkSq21 ok st start base = true) :
    wordsToBytes (btreeWords start 21 (evalMemTree envFinal st.memB)) =
      keccakExtractRate 21 ks := by
  refine wordsToBytes_btreeWords_eq_extractRate_21 fun j hj => ?_
  have hjc := (List.all_eq_true.mp hchk) j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at hjc
  rw [eval_checked_memB heval (start + j) (.var (base + j)) hjc.1 hjc.2,
      evalKExpr, hvars j (by omega)]

private theorem extract_sq63_firstBlocks {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {st : KState} {rho : List (BitVec 8)} {row c start b0 b1 b2 : Nat}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hv0 : ∀ j, j < 25 → envSpec.vars (b0 + j) = (rowPermState rho row c 0).getD j 0#64)
    (hv1 : ∀ j, j < 25 → envSpec.vars (b1 + j) = (rowPermState rho row c 1).getD j 0#64)
    (hv2 : ∀ j, j < 25 → envSpec.vars (b2 + j) = (rowPermState rho row c 2).getD j 0#64)
    (hc0 : chkSq21 ok st start b0 = true)
    (hc1 : chkSq21 ok st (start + 21) b1 = true)
    (hc2 : chkSq21 ok st (start + 42) b2 = true) :
    wordsToBytes (btreeWords start 63 (evalMemTree envFinal st.memB)) =
      shake128FirstBlocks (rowSeeds rho row c) 3 := by
  rw [show (63 : Nat) = 21 + 42 from rfl, btreeWords_split start 21 42,
      show (42 : Nat) = 21 + 21 from rfl, btreeWords_split (start + 21) 21 21,
      show start + 21 + 21 = start + 42 by omega,
      wordsToBytes_append, wordsToBytes_append,
      extract_sq21 heval hv0 hc0, extract_sq21 heval hv1 hc1, extract_sq21 heval hv2 hc2,
      shake128FirstBlocks_rowSeeds_three]

theorem extract_slotsPair25 {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {st : KState} {sf : State} {slots : List KSlot} {bLo bHi : Nat} {kLo kHi : KeccakState}
    (hm : KStateMatches envFinal st sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hvLo : ∀ idx, idx < 25 → envSpec.vars (bLo + idx) = kLo.getD idx 0#64)
    (hvHi : ∀ idx, idx < 25 → envSpec.vars (bHi + idx) = kHi.getD idx 0#64)
    (hchk : chkSlotsPair25 ok st slots bLo bHi = true) :
    ∀ idx, idx < 25 → slotHolds cfgClamp sf (evalMemTree envFinal st.memA)
      (slots.getD idx (.vreg 0)) (kLo.getD idx 0#64) (kHi.getD idx 0#64) := by
  intro idx hidx
  have hc := (List.all_eq_true.mp hchk) idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨hv, h1⟩, h2⟩, ho1⟩, ho2⟩
  have hs := eval_checked_slot (cfg := cfgClamp) hm heval (slots.getD idx (.vreg 0)) hv
    (.var (bLo + idx)) (.var (bHi + idx)) h1 h2 ho1 ho2
  simpa [evalKExpr, hvLo idx hidx, hvHi idx hidx] using hs

theorem extract_slotsSingle25 {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {st : KState} {sf : State} {slots : List KSlot} {bLo : Nat} {kLo : KeccakState}
    (hm : KStateMatches envFinal st sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hvLo : ∀ idx, idx < 25 → envSpec.vars (bLo + idx) = kLo.getD idx 0#64)
    (hchk : chkSlotsSingle25 ok st slots bLo = true) :
    ∀ idx, idx < 25 → slotHolds cfgClamp sf (evalMemTree envFinal st.memA)
      (slots.getD idx (.vreg 0)) (kLo.getD idx 0#64) 0#64 := by
  intro idx hidx
  have hc := (List.all_eq_true.mp hchk) idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hv, h1⟩, h2⟩, ho1⟩
  have hs := eval_checked_slot (cfg := cfgClamp) hm heval (slots.getD idx (.vreg 0)) hv
    (.var (bLo + idx)) (.const64 0#64) h1 h2 ho1 rfl
  simpa [evalKExpr, hvLo idx hidx] using hs

theorem sepWP_congr_pre_entails {prog : Program} {tgt : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hEnt : P2 ⊢ P1) (h : SepWP prog tgt s P1 post oom) :
    SepWP prog tgt s P2 post oom :=
  SepWP.weaken_pre hEnt h

theorem status_setPC {st : State} {pc : BitVec 64} (h : st.status = .Running) :
    (st.setPC pc).status = .Running := h

theorem readReg64_setPC {st : State} {pc : BitVec 64} {r : Reg} {v : BitVec 64}
    (h : st.readReg64 r = v) : (st.setPC pc).readReg64 r = v := h

theorem segRegInv_setPC [MlKemPlacement] {sp pc : BitVec 64} {st : State} (h : Seg2RegInv sp st) :
    Seg2RegInv sp (st.setPC pc) := h

theorem slotHolds_setPC {cfg : KCfg} {st : State} {pc : BitVec 64} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {v0 v1 : BitVec 64} (h : slotHolds cfg st tA sl v0 v1) :
    slotHolds cfg (st.setPC pc) tA sl v0 v1 := h

theorem not_mem_of_dec {r : Reg} {rs : List Reg} (h : (decMemReg r rs).decide = false) : r ∉ rs :=
  match decMemReg r rs, h with
  | isFalse hnot, _ => hnot
  | isTrue _, h => Bool.noConfusion h

private theorem cert_rejInitO : checkInstrsAt03 2164 (rejOuterInstrs cfgRejInit3) = true := by
  decide +kernel

private theorem cert_rejInitI : checkInstrsAt03 2175 (rejInnerInstrs cfgRejInit3.v) = true := by
  decide +kernel

theorem seg2_row_init_wp [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 row)
    (htA : ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0 then b + 0x026c#64 else b + 0x2580#64) s
      (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg2RowExit b sp rho row F sf Pf
        else Seg2LoopState b sp rho row F 0 sf Pf) := by
  have status_setPC : ∀ {st : State} {pc : BitVec 64},
      st.status = .Running → (st.setPC pc).status = .Running := fun h => h
  let Rest0 := Seg2ConstsLo sp ∗ memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.seq (mid := b + 0x0528#64)
    (Mid := fun s1 P1 =>
      mlkemMultiLib.CodeLoaded mlkemMpl s1.mem ∧ MlKemRoOk mlkemMpl s1.mem ∧
      Seg2RegInv sp s1 ∧ s1.readReg64 .x22 = BitVec.ofNat 64 row ∧
      (P1 ⊢ TreeMem (sp + 96#64) 262 tA ∗
        MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
        MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗ Rest0)) ?_ ?_
  · refine SepWP.congr_pre
      (P1 := TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 12448#64) 24 ∗ Rest0)
      (by dsimp only [Rest0]; apply sepProp_ext <;> sep_frame) ?_
    exact seg2_row_header_memset hb hbase hpc hrun hcl hro hreg hx8 htA
  · rintro s1 P1 hpc1 hrun1 ⟨hcl1, hro1, hreg1, hx22_1, hP1⟩
    refine sepWP_congr_pre_entails
      (P1 := memRegion (sp + 2192#64) (8 * 189) ∗
        (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
          MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗ memRegion (sp + 13984#64) 504 ∗ F))
      (Entails.trans hP1 (by dsimp only [Rest0]; sep_frame)) ?_
    refine sepWP_elim_treeMem (len := 189) (by decide) fun tB0 => ?_
    refine SepWP.seq (sepWP_with_env hcl1 hro1 (target := b + 0x2500#64)
      (post := fun sC PC => mlkemMultiLib.CodeLoaded mlkemMpl sC.mem → MlKemRoOk mlkemMpl sC.mem →
        SepWP (blkPC03.rebase b (fun _ => none))
          (if allLanesDone 3 (rowSeeds rho row) 0 then b + 0x026c#64 else b + 0x2580#64) sC PC
          (fun sf Pf =>
            if allLanesDone 3 (rowSeeds rho row) 0 then Seg2RowExit b sp rho row F sf Pf
            else Seg2LoopState b sp rho row F 0 sf Pf)) ?_)
      (fun _ _ _ _ ⟨_, _, hclC, hroC, hk⟩ => hk hclC hroC)
    apply keccakRc_intro hro1
    let env0 := mkSegEnv sp row rho keccakZeroState keccakZeroState keccakZeroState s1 tA tB0
    rcases mkSegState_matches (cfg := cfgInit) (hasSeedConsts := true) (slots01 := []) (slots2 := [])
      (row := row) (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState)
      (tA := tA) (tB := tB0) (by decide) (by decide) hreg1 hx22_1 (fun _ => htA)
      (by intro _ h; simp at h) (by intro _ h; simp at h) with ⟨hm0, htA0, htB0⟩
    let FF1 := MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗ memRegion (sp + 13984#64) 504 ∗ F
    refine SepWP.congr_pre (P1 := KSpatial cfgInit env0 stInit0 FF1) ?_ ?_
    · dsimp only [stInit0, KSpatial]
      rw [htA0, htB0]
      dsimp only [KConstsLoOpt, cfgInit, FF1]
      rw [show env0.sp = sp from rfl,
        show env0.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
        show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
        show sp + BitVec.ofNat 64 2192 = sp + 2192#64 from rfl]
      apply sepProp_ext <;> sep_frame
    have hr0 : env0.rLoop < 24 := show (0 : Nat) < 24 by decide
    refine sepWP_of_runAndCheckKProg cfgInit_wf hr0 cert_stepsInit hm0
      (by rw [BitVec.ofNat_mul 4 330]; exact pc_of_eq hpc1 (by decide +kernel)) hrun1 ?_
    intro s2 envFinal stEnd hpc2 hrun2 hspF hrcF _ heval hm2 hchk
    have hv96_0 : env0.vars 96 = BitVec.ofNat 64 row := rfl
    have hvRho_0 : ∀ k, k < 4 → env0.vars (100 - k) = ByteSlice.readLE rho (8 * k) 8 := by
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp [env0, mkSegEnv]
    rcases specEnv_stepsInit_vars hrho hrow hv96_0 hvRho_0 with
      ⟨hs96, hs97, hs98, hs99, hs100, hp00, hp10, hp20, hp01, hp11, hp02, hp12, hp21, hp22⟩
    simp only [chkInitPost, Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨hHdr, hSq⟩, hsl01, hsl2⟩
    simp only [chkInitHdr, Bool.and_eq_true] at hHdr
    rcases hHdr with ⟨⟨⟨hregC, ho96⟩, hseedC, ⟨⟨ho97, ho98⟩, ho99⟩, ho100⟩, hg9, hg10⟩
    simp only [chkInitSq, Bool.and_eq_true] at hSq
    rcases hSq with ⟨⟨⟨⟨hsq00, hsq01⟩, hsq02⟩, ⟨hsq10, hsq11⟩, hsq12⟩, ⟨hsq20, hsq21⟩, hsq22⟩
    have hv96F : envFinal.vars 96 = BitVec.ofNat 64 row :=
      (heval (.var 96) ho96).trans hs96
    have hv97F : envFinal.vars 97 = ByteSlice.readLE rho 24 8 := (heval (.var 97) ho97).trans hs97
    have hv98F : envFinal.vars 98 = ByteSlice.readLE rho 16 8 := (heval (.var 98) ho98).trans hs98
    have hv99F : envFinal.vars 99 = ByteSlice.readLE rho 8 8 := (heval (.var 99) ho99).trans hs99
    have hv100F : envFinal.vars 100 = ByteSlice.readLE rho 0 8 := (heval (.var 100) ho100).trans hs100
    rcases extract_segRegInv hm2 hspF hrcF hv96F hregC with ⟨hreg2, hx8_2, hx22_2⟩
    have hx8_eq : s2.readReg64 .x8 = BitVec.ofNat 64 (row + 1) := by
      rw [hx8_2, evalKExpr, evalKExpr, evalKExpr, hv96F, BitVec.ofNat_add row 1]
    have htA2 := extract_seedConsts hv97F hv98F hv99F hv100F hseedC
    have hx9_2 : s2.readReg64 .x9 = 0#64 :=
      eval_checked_gpr hm2 heval 9#5 (by decide) (.const64 0#64) hg9 rfl
    have hx10_2 : s2.readReg64 .x10 = (sp + 2192#64) + 11#64 := by
      have r := eval_checked_gpr hm2 heval 10#5 (by decide) (.spAdd 2203#64) hg10 rfl
      dsimp only [evalKExpr] at r; rw [r, show (specEnvSteps env0 stepsInit).sp = sp from rfl]
      rw [BitVec.add_assoc]; rfl
    have hs01_2 := extract_slotsPair25 hm2 heval hp02 hp12 hsl01
    have hs2_2 := extract_slotsSingle25 hm2 heval hp22 hsl2
    have hbuf0 := extract_sq63_firstBlocks heval hp00 hp01 hp02 hsq00 hsq01 hsq02
    have hbuf1 := extract_sq63_firstBlocks heval hp10 hp11 hp12 hsq10 hsq11 hsq12
    have hbuf2 := extract_sq63_firstBlocks heval hp20 hp21 hp22 hsq20 hsq21 hsq22
    apply sepWP_drop_left
    refine step_b_seg2b (w := 2163) (disp := 20#64) (by omega) (by omega) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_
    let tSq := evalMemTree envFinal stEnd.memB
    let bufs : Nat → List (BitVec 8) := fun i => wordsToBytes (btreeWords (63 * i) 63 tSq)
    let FF2 := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 (evalMemTree envFinal stEnd.memA) ∗
      memRegion (sp + 13984#64) 504 ∗ F
    refine SepWP.congr_pre
      (P1 := TreeMem (sp + 2192#64) 189 tSq ∗
        (MultiLaneSampled (sp + 12448#64) 3 (fun _ => 0) ∗
          (MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) ∗ FF2)))
      (by
        dsimp only [KConstsLoOpt, cfgInit, FF1, FF2, tSq]
        rw [hspF, show env0.sp = sp from rfl,
          show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
          show sp + BitVec.ofNat 64 2192 = sp + 2192#64 from rfl]
        apply sepProp_ext <;> sep_frame) ?_
    rcases hreg2 with ⟨hsp2, hspA2, r19, hx20_2, hx21_2, r23, hx24_2, r25, r26, r27, r28⟩
    have hreg2' : Seg2RegInv sp s2 := ⟨hsp2, hspA2, r19, hx20_2, hx21_2, r23, hx24_2, r25, r26, r27, r28⟩
    refine step_rej_site_init3 (pcBase := b + 0x21d0#64) (sqBase := sp + 2192#64)
      (sampBase := sp + 12448#64) (slotsBase := sp + 4272#64) (cfg := cfgRejInit3)
      (seeds := rowSeeds rho row) (bufs := bufs)
      ((setPC_disp_eq s2 b 2163 20#64 0x21e0#64 (by decide +kernel)).trans
        (by change b + 0x21e0#64 = (b + 0x21d0#64) + 16#64; rw [BitVec.add_assoc]; rfl))
      (status_setPC hrun2) cfgRejInit3_valid rfl
      (fetchesInstrsAt_blk03_seg2b (w0 := 2164) (by omega)
        (by rw [show (rejOuterInstrs cfgRejInit3).length = 11 from rfl]; omega)
        (by
          change (b + 0x21d0#64) + 0#64 = b + BitVec.ofNat 64 (4 * 2164)
          rw [BitVec.add_zero, BitVec.ofNat_mul 4 2164])
        cert_rejInitO)
      (fetchesInstrsAt_blk03_seg2b (w0 := 2175) (by omega)
        (by rw [show (rejInnerInstrs cfgRejInit3.v).length = 193 from rfl]; omega)
        (by
          rw [BitVec.add_assoc, BitVec.ofNat_mul 4 11, BitVec.ofNat_mul 4 2175]
          exact congrArg (b + ·) (by decide))
        cert_rejInitI)
      (fun i hi => by
        dsimp only [cfgRejInit3] at hi ⊢
        exact rejBufReadable_of_treeMem (offWords := 63 * i)
          (by congr 1; exact eq_of_beq (by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> decide))
          (by omega) rfl)
      (fun i hi => by
        dsimp only [cfgRejInit3, bufs] at hi ⊢
        rw [wordsToBytes_length, Seg2Mem.btreeWords_length])
      (fun i hi => by
        dsimp only [cfgRejInit3] at hi
        rw [List.take_of_length_le (by dsimp only [bufs]; rw [wordsToBytes_length, Seg2Mem.btreeWords_length])]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · exact hbuf0
        · exact hbuf1
        · exact hbuf2)
      (MultiLaneClampedInv.init_zero 3).toRaw
      (readReg64_setPC hx9_2) (readReg64_setPC hx10_2)
      (readReg64_setPC hx21_2) (readReg64_setPC hx24_2) (readReg64_setPC hx20_2) ?_
    intro sF sampled' hws' hpSite hraw'
    rcases segRegInv_of_sitePreserved (pc := pcAt (b + 0x21d0#64) 204) hpSite
      (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
      (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
      (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
      (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
      (segRegInv_setPC hreg2') (readReg64_setPC hx8_eq) (readReg64_setPC hx22_2)
      with ⟨hregF, hx8F, hx22F⟩
    have hs01F := fun idx h =>
      slotHolds_of_sitePreserved (pc := pcAt (b + 0x21d0#64) 204) hpSite (slotHolds_setPC (hs01_2 idx h))
    have hs2F := fun idx h =>
      slotHolds_of_sitePreserved (pc := pcAt (b + 0x21d0#64) 204) hpSite (slotHolds_setPC (hs2_2 idx h))
    have hpcF : (sF.setPC (pcAt (b + 0x21d0#64) 204)).pc = b + 0x2500#64 := by
      change (b + 0x21d0#64) + BitVec.ofNat 64 (4 * 204) = b + 0x2500#64
      rw [BitVec.add_assoc, BitVec.ofNat_mul 4 204]
      exact congrArg (b + ·) (by decide)
    refine SepWP.done hpcF (status_setPC hpSite.1) fun hclF hroF => ?_
    refine sepWP_congr_pre_entails
      (show TreeMem (sp + 2192#64) 189 tSq ∗
          (MultiLaneSampled (sp + 12448#64) 3 sampled' ∗
            (MultiLaneSlots (sp + 4272#64) 544 3 hws' ∗ FF2)) ⊢
          Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 (evalMemTree envFinal stEnd.memA) ∗
            memRegion (sp + 2192#64) 1512 ∗ MultiLaneSlots (sp + 4272#64) 544 3 hws' ∗
            MultiLaneSampled (sp + 12448#64) 3 sampled' ∗ memRegion (sp + 13984#64) 504 ∗ F by
        dsimp only [FF2]
        have htm := treeMem_entails_memRegion (ptr := sp + 2192#64) tSq (len := 189) (by decide)
        rw [show 8 * 189 = 1512 from rfl] at htm
        exact Entails.trans (sepConj_mono_left htm) (by sep_frame)) ?_
    exact seg2_row_clamp_init3 hpcF (status_setPC hpSite.1) hclF hroF hregF hx8F hx22F htA2 hraw' hs01F hs2F

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowStep
