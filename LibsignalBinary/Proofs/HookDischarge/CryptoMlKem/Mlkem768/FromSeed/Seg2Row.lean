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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit

/-!
# `generate_keypair_compressed` (`B05`): single-row `SampleNTT` initialization

Proves `seg2_row_init_wp` (`+0x02b8 → +0x3048 / +0x2300`), covering the initial 3-block absorb,
squeeze, `rej_sample`, and post-clamp dispatch. The extra-block loop and full row theorems live
in `Seg2RowLoop`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState Shake128SeedTerminates keccakExtractRate keccakF1600 shake128BlockAt shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneClampedInv MultiLaneRawInv MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  SitePreserved decMemReg rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone sampleNttRow_safeSepWP sampleNttRow_sepWP
  step_rej_site_extra1 step_rej_site_init3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blkPC05 blkPl05 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem btreeWords checkInstrsAt05 fetchesInstrsAt_blk05_seg2 memRegion_entails_exists_treeMem
  treeMem_entails_memRegion wordsToBytes wordsToBytes_length btreeWords_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KSpatial KStateMatches matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep (sepWP_of_runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  readSlot slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  btreeWords_split inv01Slots inv2Slots rejBufReadable_of_treeMem slotsEA slotsEB
  wordsToBytes_append wordsToBytes_btreeWords_eq_extractRate_21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memB eval_checked_pstate eval_checked_slot
  exprVarsOk extendLoopVars progBases rhoW rowPermState rowPermState_succ rowSeeds runAndCheckKProg
  sepWP_of_runAndCheckKProg shake128FirstBlocks_rowSeeds_three specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2ConstWordsInv Seg2LoopState Seg2RegInv Seg2RowDone cfgClamp cfgClamp_wf cfgExtra cfgExtra_wf
  cfgInit cfgInit_wf cfgRejExtra1 cfgRejExtra1_valid cfgRejInit3 cfgRejInit3_valid
  condCC_256_of_le271 condCS_256_of_le271 condHI_255_of_le271 keccakRc_intro
  multiLaneSampled3_eq_treeMem raw_sampled_le271 seg2_row_memset slotHoldsLo step_bCond_seg2 step_b_seg2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  checkConstWordsMemA checkSegRegGprs eq_some_getD extract_constWords extract_segRegInv
  exprVarsOk_true finish_clamp_branch kexprBeq_refl mkSegEnv mkSegState mkSegState_matches
  preClamp01Slots preClamp2Slots preExtra01Slots preExtra2Slots with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit (
  checkPStateEq evalExprList25_varRange expVarRange pc_add_eq pc_of_eq
  seg2_row_clamp_init3 segRegInv_of_sitePreserved setPC_disp_eq setPC_disp_w_eq setPC_fall_eq
  setPC_fall_w_eq slotHoldsLo_of_sitePreserved slotHolds_of_sitePreserved specEnv_stepsInit_vars
  stInit0 status_setPC stepsInit)

attribute [local irreducible] keccakF1600 blkPC05

/-! ## 1. Precomputed Symbolic Certificates (`stepsInit` & `rej_sample` Fetches) -/

private def checkCol2Var (base j : Nat) (e : KExpr) : Bool :=
  e.beq (.var (base + j)) || e.beq (.var (base + 25 + j))

private def checkInitEnd (st : KState) : Bool :=
  checkSegRegGprs st (.add64 (.var 100) (.const64 1#64)) &&
  checkConstWordsMemA st &&
  (st.gprs.get 8).beq (.const64 0#64) &&
  (st.gprs.get 9).beq (.spAdd 9995#64) &&
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
    slotValid cfgClamp sl01 &&
      (readSlot cfgClamp st sl01).1.beq (.var (5000 + idx)) &&
      (readSlot cfgClamp st sl01).2.beq (.var (5025 + idx)) &&
      slotValid cfgClamp sl2 &&
      checkCol2Var 7000 idx (readSlot cfgClamp st sl2).1)

private theorem cert_stepsInit :
    runAndCheckKProg cfgInit 183 2008 183 2007 1500 stepsInit stInit0
      (fun _ st => checkInitEnd st) = true := by decide +kernel

private theorem cert_rejInitO : checkInstrsAt05 2008 (rejOuterInstrs cfgRejInit3) = true := by decide +kernel
private theorem cert_rejInitI : checkInstrsAt05 2019 (rejInnerInstrs .varB) = true := by decide +kernel

/-! ## 2. `+0x02b8 → +0x3048 / +0x2300` Initial 3-Block Absorb, Squeeze & `rej_sample` (`seg2_row_init_wp`) -/

theorem eval_checked_slotLo {cfg : KCfg} {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (sl : KSlot) (hsl : slotValid cfg sl = true) (eLo : KExpr)
    (heqLo : (readSlot cfg stEnd sl).1.beq eLo = true) (hokLo : exprVarsOk ok eLo = true) :
    slotHoldsLo cfg sf (stEnd.memA.map (evalKExpr envFinal)) sl (evalKExpr envSpec eLo) :=
  ⟨evalKExpr envFinal (readSlot cfg stEnd sl).2,
    eval_checked_slot (ok := fun _ => true) hm (envSpec := envFinal) (fun _ _ => rfl) sl hsl
      (readSlot cfg stEnd sl).1 (readSlot cfg stEnd sl).2
      (kexprBeq_refl _) (kexprBeq_refl _) (exprVarsOk_true _) (exprVarsOk_true _) |> fun h => by
      rwa [KExpr.beq_eq_true heqLo, heval eLo hokLo] at h⟩

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

theorem specEnvSteps_sp (env : KEnv) (steps : List KProgStep) :
    (specEnvSteps env steps).sp = env.sp := by
  induction steps generalizing env with
  | nil => rfl
  | cons s tl ih => cases s <;> exact ih _

private theorem okInit_all :
    ([2000, 3000, 4000, 5000, 6000, 7000].all fun b =>
      (List.range 25).all fun i =>
        validSpecVar 1500 (progBases stepsInit) (b + i) &&
        validSpecVar 1500 (progBases stepsInit) (b + 25 + i)) = true := by decide +kernel

private theorem okInit_lo (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000, 4000, 5000, 6000, 7000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsInit) (b + i) = true := by
  have h1 := (List.all_eq_true.mp okInit_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).1

private theorem okInit_hi (b : Nat) {i : Nat} (hb : b ∈ [2000, 3000, 4000, 5000, 6000, 7000]) (hi : i < 25) :
    validSpecVar 1500 (progBases stepsInit) (b + 25 + i) = true := by
  have h1 := (List.all_eq_true.mp okInit_all) b hb
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp h1) i (List.mem_range.mpr hi))).2

private theorem okInit_low {id : Nat} (h : id < 1500) :
    validSpecVar 1500 (progBases stepsInit) id = true := by
  simp [validSpecVar, Nat.blt_eq, h]

attribute [local irreducible] validSpecVar progBases specEnvSteps extendLoopVars TreeMem MultiLaneSlots MultiLaneSampled

theorem sepWP_mono_pre {prog : Program} {tgt : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P ⊢ Q) (h : SepWP prog tgt s Q post oom) : SepWP prog tgt s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  exact SepWP.to_reaches_pc h (Satisfies.mono (sepConj_mono_left hp) hm)

theorem sepWP_seq_frozen [MlKemPlacement] {prog : Program} {mid tgt : BitVec 64} {s0 : State}
    {P0 : SepProp} {post1 post2 : State → SepProp → Prop}
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (h1 : SepWP prog mid s0 P0 post1)
    (h2 : ∀ s1 P1, s1.pc = mid → s1.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl s1.mem → MlKemRoOk mlkemMpl s1.mem → post1 s1 P1 →
      SepWP prog tgt s1 P1 post2) :
    SepWP prog tgt s0 P0 post2 :=
  sepWP_seq_env hcl0 hro0 h1 h2

private def Seg2InitPreClampPost [MlKemPlacement] (sp fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (F : SepProp) (sF : State) (PF : SepProp) : Prop :=
  Seg2RegInv sp fpVal sF ∧ sF.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  sF.readReg64 .x22 = BitVec.ofNat 64 row ∧
  ∃ tA2 sampled' hws', Seg2ConstWordsInv sp rho tA2 ∧
    MultiLaneRawXofInv 3 (rowSeeds rho row) 0 sampled' hws' ∧
    (∀ idx, idx < 25 → slotHolds cfgClamp sF tA2 (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHoldsLo cfgClamp sF tA2 (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64)) ∧
    (PF ⊢ TreeMem (sp + 64#64) 268 tA2 ∗ memRegion (sp + 9984#64) 1512 ∗
      MultiLaneSlots (sp + 17376#64) 544 3 hws' ∗ memRegion (sp + 27840#64) 504 ∗
      MultiLaneSampled (sp + 29024#64) 3 sampled' ∗ F)

theorem readReg64_setPC {s : State} {pc v : BitVec 64} {r : Reg}
    (h : s.readReg64 r = v) : (s.setPC pc).readReg64 r = v := by
  cases r <;> simpa [State.readReg64, State.setPC] using h

theorem segRegInv_setPC [MlKemPlacement] {sp fpVal pc : BitVec 64} {s : State}
    (h : Seg2RegInv sp fpVal s) : Seg2RegInv sp fpVal (s.setPC pc) := by
  rcases h with ⟨⟨hsp, hal, r29, r19, r21, r24, r26, r27, r28⟩, r20, r23⟩
  exact ⟨⟨hsp, hal, readReg64_setPC r29, readReg64_setPC r19, readReg64_setPC r21,
    readReg64_setPC r24, readReg64_setPC r26, readReg64_setPC r27, readReg64_setPC r28⟩,
    readReg64_setPC r20, readReg64_setPC r23⟩

theorem slotHolds_setPC {cfg : KCfg} {s : State} {pc : BitVec 64} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {lo hi : BitVec 64} (h : slotHolds cfg s tA sl lo hi) :
    slotHolds cfg (s.setPC pc) tA sl lo hi := by
  cases sl with
  | vreg r => exact ⟨h.1, by simpa [State.readVReg128, State.setPC] using h.2⟩
  | spillQ _ => exact h

theorem not_mem_of_dec {r : Reg} {rs : List Reg} (h : (decMemReg r rs).decide = false) : r ∉ rs :=
  match decMemReg r rs, h with
  | isFalse hnot, _ => hnot
  | isTrue _, h => Bool.noConfusion h

private theorem step_init_rej [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} {F : SepProp}
    {s2 : State} {envF : KEnv} {stEnd : KState}
    (hpc2 : s2.pc = b + BitVec.ofNat 64 (4 * 2007)) (hrun2 : s2.status = .Running)
    (hspEq : envF.sp = sp)
    (hreg2 : Seg2RegInv sp fpVal s2 ∧
      (s2.readReg64 .x1 = evalKExpr envF (.add64 (.var 100) (.const64 1#64)) ∧
       s2.readReg64 .x22 = BitVec.ofNat 64 row))
    (hx1_2 : s2.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (htA2 : Seg2ConstWordsInv sp rho (stEnd.memA.map (evalKExpr envF)))
    (hx8_2 : s2.readReg64 .x8 = 0#64)
    (hx9_2 : s2.readReg64 .x9 = sp + 9995#64)
    (hs01_2 : ∀ idx, idx < 25 → slotHolds cfgClamp s2 (stEnd.memA.map (evalKExpr envF))
      (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64))
    (hs2_2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp s2 (stEnd.memA.map (evalKExpr envF))
      (preClamp2Slots.getD idx (.vreg 0)) ((rowPermState rho row 2 2).getD idx 0#64))
    (hbuf0 : wordsToBytes (btreeWords 0 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 0) 3)
    (hbuf1 : wordsToBytes (btreeWords 63 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 1) 3)
    (hbuf2 : wordsToBytes (btreeWords 126 63 (stEnd.memB.map (evalKExpr envF))) =
      shake128FirstBlocks (rowSeeds rho row 2) 3) :
    let FF := MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 27840#64) 504 ∗ MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗ F
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x2290#64) s2
      (KSpatial cfgInit envF stEnd FF)
      (Seg2InitPreClampPost sp fpVal rho row F) := by
  intro FF
  let tA2 := stEnd.memA.map (evalKExpr envF)
  let tB2 := stEnd.memB.map (evalKExpr envF)
  dsimp only [KSpatial, cfgInit]
  apply Seg2Clamp.sepWP_drop_left
  refine sepWP_mono_pre (Q := TreeMem (sp + 9984#64) 189 tB2 ∗
      (MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗
        (MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          (TreeMem (sp + 64#64) 268 tA2 ∗ memRegion (sp + 27840#64) 504 ∗ F)))) ?_ ?_
  · rw [hspEq, show sp + BitVec.ofNat 64 64 = sp + 64#64 from rfl,
        show sp + BitVec.ofNat 64 9984 = sp + 9984#64 from rfl]
    dsimp only [FF]; sep_frame
  refine step_b_seg2 (w := 2007) (disp := 20#64) (by decide) (by decide) (by decide +kernel) hpc2 hrun2 ?_
  let pcBaseI := b + (4016#64 + 4016#64)
  let bufsI : Nat → List (BitVec 8) := fun i => wordsToBytes (btreeWords (63 * i) 63 tB2)
  refine step_rej_site_init3 (pcBase := pcBaseI) (sqBase := sp + 9984#64)
    (sampBase := sp + 29024#64) (slotsBase := sp + 17376#64) (cfg := cfgRejInit3)
    (seeds := rowSeeds rho row) (bufs := bufsI)
    (hpc := by
      change b + BitVec.ofNat 64 (4 * 2007) + 20#64 = b + (4016#64 + 4016#64) + 16#64
      rw [BitVec.add_assoc b, BitVec.add_assoc b]
      exact congrArg (b + ·) (eq_of_beq (by decide +kernel)))
    (hrun := (status_setPC _ _).trans hrun2) cfgRejInit3_valid rfl
    (fetchesInstrsAt_blk05_seg2 (by omega)
      (by rw [show (rejOuterInstrs cfgRejInit3).length = 11 from rfl]; omega)
      (by dsimp only [pcBaseI]; rw [BitVec.add_assoc, BitVec.ofNat_mul 4 2008]; exact congrArg (b + ·) (eq_of_beq (by decide +kernel)))
      cert_rejInitO)
    (fetchesInstrsAt_blk05_seg2 (by omega)
      (by rw [show (rejInnerInstrs cfgRejInit3.v).length = 193 from rfl]; omega)
      (by dsimp only [pcBaseI]; rw [BitVec.add_assoc, BitVec.ofNat_mul 4 2019]; exact congrArg (b + ·) (eq_of_beq (by decide +kernel)))
      cert_rejInitI)
    (fun i hi => by
      dsimp only [cfgRejInit3] at hi ⊢
      exact rejBufReadable_of_treeMem (offWords := 63 * i)
        (by
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
          · simp
          · rw [BitVec.add_assoc]
          · rw [BitVec.add_assoc])
        (by omega) rfl)
    (fun i _ => by dsimp only [bufsI, cfgRejInit3]; rw [wordsToBytes_length, btreeWords_length])
    (fun i hi => by
      dsimp only [cfgRejInit3] at hi
      rw [List.take_of_length_le (by dsimp only [bufsI]; rw [wordsToBytes_length, btreeWords_length])]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact hbuf0
      · exact hbuf1
      · exact hbuf2)
    (MultiLaneClampedInv.init_zero 3).toRaw
    (readReg64_setPC hx8_2)
    (by dsimp only [cfgRejInit3]; rw [readReg64_setPC hx9_2, BitVec.add_assoc]; rfl)
    (readReg64_setPC hreg2.1.1.2.2.2.2.1)
    (readReg64_setPC hreg2.1.1.2.2.2.2.2.2.2.1)
    (readReg64_setPC hreg2.1.1.2.2.2.1) ?_
  intro sF sampled' hws' hp hraw
  rcases segRegInv_of_sitePreserved (pc := pcAt pcBaseI 204) hp
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (not_mem_of_dec (by decide)) (not_mem_of_dec (by decide))
    (segRegInv_setPC hreg2.1) (readReg64_setPC hx1_2) (readReg64_setPC hreg2.2.2)
    with ⟨hregF, hx1F, hx22F⟩
  refine SepWP.done
    (by
      change (b + (4016#64 + 4016#64)) + BitVec.ofNat 64 (4 * 204) = b + 0x2290#64
      rw [BitVec.add_assoc, BitVec.ofNat_mul 4 204]; exact congrArg (b + ·) (eq_of_beq (by decide +kernel)))
    ((status_setPC _ _).trans hp.1)
    ⟨hregF, hx1F, hx22F, tA2, sampled', hws', htA2, hraw,
     fun idx hidx => slotHolds_of_sitePreserved hp (slotHolds_setPC (hs01_2 idx hidx)),
     fun idx hidx => by rcases hs2_2 idx hidx with ⟨vh, hh⟩; exact slotHoldsLo_of_sitePreserved hp ⟨vh, slotHolds_setPC hh⟩,
     Entails.trans (sepConj_mono_left
       (by simpa using treeMem_entails_memRegion (ptr := sp + 9984#64) (len := 189) tB2 (by decide))) (by sep_frame)⟩

private theorem seg2_row_init_rej [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {F : SepProp} {s2 : State} {env0 envF : KEnv} {stEnd : KState}
    (hev0_100 : env0.vars 100 = BitVec.ofNat 64 row)
    (hev0_102 : env0.vars 102 = fpVal)
    (hev0_rho : ∀ k, k < 4 → env0.vars (103 + k) = rhoW rho k)
    (hev0_sp : env0.sp = sp)
    (hpc2 : s2.pc = b + BitVec.ofNat 64 (4 * 2007)) (hrun2 : s2.status = .Running)
    (hspF : envF.sp = env0.sp)
    (hrcF : envF.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (heval : ∀ e, exprVarsOk (validSpecVar 1500 (progBases stepsInit)) e = true →
      evalKExpr envF e = evalKExpr (specEnvSteps env0 stepsInit) e)
    (hm2 : KStateMatches envF stEnd s2)
    (hchk : checkInitEnd stEnd = true) :
    let FF := MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 27840#64) 504 ∗ MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗ F
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x2290#64) s2
      (KSpatial cfgInit envF stEnd FF)
      (Seg2InitPreClampPost sp fpVal rho row F) := by
  intro FF
  have hrcEq : envF.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" := hrcF
  have hspEq : envF.sp = sp := hspF.trans hev0_sp
  have hspec := specEnv_stepsInit_vars hrho hrow hev0_100 hev0_rho
  rcases hspec with ⟨hv100S, hv102S, hvRhoS, hv2000, hv2025, hv3000, hv3025,
    hv4000, hv4025, hv5000, hv5025, hv6000, hv6025, hv7000, hv7025⟩
  simp only [checkInitEnd, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hchkG, hchkC⟩, hx8B⟩, hx9B⟩, hmemB⟩, hslots⟩
  have hreg2 := extract_segRegInv (eX1 := .add64 (.var 100) (.const64 1#64)) hm2 hspEq hrcEq
    (by simpa [evalKExpr, hv100S] using (heval (.var 100) (okInit_low (by decide))))
    (by simpa [evalKExpr, hv102S, hev0_102] using (heval (.var 102) (okInit_low (by decide)))) hchkG
  have hx1_2 : s2.readReg64 .x1 = BitVec.ofNat 64 (row + 1) := by
    have hokAdd : exprVarsOk (validSpecVar 1500 (progBases stepsInit)) (.add64 (.var 100) (.const64 1#64)) = true :=
      by simp [exprVarsOk, okInit_low (show 100 < 1500 by decide)]
    rw [hreg2.2.1, heval _ hokAdd]
    simp [evalKExpr, hv100S, BitVec.ofNat_add]
  have htA2 : Seg2ConstWordsInv sp rho (stEnd.memA.map (evalKExpr envF)) :=
    extract_constWords hspEq
      (by simpa [evalKExpr, hvRhoS 0 (by decide)] using heval (.var 103) (okInit_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 1 (by decide)] using heval (.var 104) (okInit_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 2 (by decide)] using heval (.var 105) (okInit_low (by decide)))
      (by simpa [evalKExpr, hvRhoS 3 (by decide)] using heval (.var 106) (okInit_low (by decide))) hchkC
  have hx8_2 : s2.readReg64 .x8 = 0#64 :=
    eval_checked_gpr hm2 heval 8#5 (by decide) (.const64 0#64) hx8B rfl
  have hx9_2 : s2.readReg64 .x9 = sp + 9995#64 := by
    simpa [evalKExpr, specEnvSteps_sp, hev0_sp] using
      eval_checked_gpr hm2 heval 9#5 (by decide) (.spAdd 9995#64) hx9B rfl
  let tA2 := stEnd.memA.map (evalKExpr envF)
  let tB2 := stEnd.memB.map (evalKExpr envF)
  have hs01_2 : ∀ idx, idx < 25 → slotHolds cfgClamp s2 tA2 (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    have h := eval_checked_slot hm2 heval _ hs.1.1.1.1 (.var (5000 + idx)) (.var (5025 + idx))
      hs.1.1.1.2 hs.1.1.2 (okInit_lo 5000 (by decide) hidx) (okInit_hi 5000 (by decide) hidx)
    rwa [evalKExpr, evalKExpr, hv5000 idx hidx, hv5025 idx hidx] at h
  have hs2_2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp s2 tA2 (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64) := fun idx hidx => by
    have hs := (List.all_eq_true.mp hslots) idx (List.mem_range.mpr hidx)
    simp only [Bool.and_eq_true] at hs
    exact eval_col2_slotLo hm2 heval hs.1.2 hs.2
      (okInit_lo 7000 (by decide) hidx) (okInit_hi 7000 (by decide) hidx) (hv7000 idx hidx) (hv7025 idx hidx)
  have hbuf0 : wordsToBytes (btreeWords 0 63 tB2) = shake128FirstBlocks (rowSeeds rho row 0) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval j (.var (2000 + j)) hm.1.1.1.1.1.1.1.1 (okInit_lo 2000 (by decide) (by omega))).trans (hv2000 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval (21 + j) (.var (4000 + j)) hm.1.1.1.1.1.1.1.2 (okInit_lo 4000 (by decide) (by omega))).trans (hv4000 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      simpa only [tB2, Nat.zero_add, evalKExpr] using
        (eval_checked_memB heval (42 + j) (.var (5000 + j)) hm.1.1.1.1.1.1.2 (okInit_lo 5000 (by decide) (by omega))).trans (hv5000 j (by omega))
  have hbuf1 : wordsToBytes (btreeWords 63 63 tB2) = shake128FirstBlocks (rowSeeds rho row 1) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact (eval_checked_memB heval (63 + j) (.var (2025 + j)) hm.1.1.1.1.1.2 (okInit_hi 2000 (by decide) (by omega))).trans (hv2025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 63 + 21 + j = 84 + j by omega]
      exact (eval_checked_memB heval (84 + j) (.var (4025 + j)) hm.1.1.1.1.2 (okInit_hi 4000 (by decide) (by omega))).trans (hv4025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 63 + 42 + j = 105 + j by omega]
      exact (eval_checked_memB heval (105 + j) (.var (5025 + j)) hm.1.1.1.2 (okInit_hi 5000 (by decide) (by omega))).trans (hv5025 j (by omega))
  have hbuf2 : wordsToBytes (btreeWords 126 63 tB2) = shake128FirstBlocks (rowSeeds rho row 2) 3 := by
    refine btreeWords63_bytes_eq_firstBlocks3 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      exact eval_col2_memB heval hm.1.1.2 (okInit_lo 3000 (by decide) (by omega)) (okInit_hi 3000 (by decide) (by omega)) (hv3000 j (by omega)) (hv3025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 126 + 21 + j = 147 + j by omega]
      exact eval_col2_memB heval hm.1.2 (okInit_lo 6000 (by decide) (by omega)) (okInit_hi 6000 (by decide) (by omega)) (hv6000 j (by omega)) (hv6025 j (by omega))
    · have hm := (List.all_eq_true.mp hmemB) j (List.mem_range.mpr hj); simp only [Bool.and_eq_true] at hm
      rw [show 126 + 42 + j = 168 + j by omega]
      exact eval_col2_memB heval hm.2 (okInit_lo 7000 (by decide) (by omega)) (okInit_hi 7000 (by decide) (by omega)) (hv7000 j (by omega)) (hv7025 j (by omega))
  exact step_init_rej hpc2 hrun2 hspEq hreg2 hx1_2 htA2 hx8_2 hx9_2 hs01_2 hs2_2 hbuf0 hbuf1 hbuf2

private theorem seg2_row_init_pre_clamp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} (htA : Seg2ConstWordsInv sp rho tA)
    {F : SepProp} {s1 : State} {P1 : SepProp}
    (hpc1 : s1.pc = b + 0x02dc#64) (hrun1 : s1.status = .Running)
    (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hreg1 : Seg2RegInv sp fpVal s1) (hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 row)
    (hP1 : P1 ⊢ MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
      MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗
      (TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗ memRegion (sp + 27840#64) 504 ∗ F)) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x2290#64) s1 P1
      (Seg2InitPreClampPost sp fpVal rho row F) := by
  refine sepWP_mono_pre (Entails.trans hP1 (Entails.trans (by sep_frame :
      MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
        MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗
        (TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗ memRegion (sp + 27840#64) 504 ∗ F) ⊢
      memRegion (sp + 9984#64) 1512 ∗
        (TreeMem (sp + 64#64) 268 tA ∗ MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
          memRegion (sp + 27840#64) 504 ∗ MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗ F))
    (sepConj_mono_left (memRegion_entails_exists_treeMem (ptr := sp + 9984#64) (len := 189) (by decide))))) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tB0
  let env0 := mkSegEnv sp fpVal row rho #[] #[] #[] (fun _ => 0#64) s1 tA tB0
  rcases mkSegState_matches (cfg := cfgInit) (hasConsts := true) (slots01 := []) (slots2 := [])
    (k0 := #[]) (k1 := #[]) (k2 := #[]) (k2Hi := fun _ => 0#64) (tA := tA) (tB := tB0)
    (by decide) (by decide) hreg1 hx22_1 (fun _ => htA) (fun _ h => nomatch h) (fun _ h => nomatch h)
    with ⟨hm0, htA_eq, htB_eq⟩
  apply keccakRc_intro hro1
  let FF := MultiLaneSlots (sp + 17376#64) 544 3 (fun _ => List.replicate 272 0#16) ∗
    memRegion (sp + 27840#64) 504 ∗ MultiLaneSampled (sp + 29024#64) 3 (fun _ => 0) ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgInit env0 stInit0 FF) ?_ ?_
  · unfold stInit0; dsimp only [KSpatial, FF]
    rw [htA_eq, htB_eq]
    dsimp only [cfgInit]
    rw [show env0.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show env0.sp = sp from rfl,
      show sp + BitVec.ofNat 64 64 = sp + 64#64 from rfl,
      show sp + BitVec.ofNat 64 9984 = sp + 9984#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hr0 : env0.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runAndCheckKProg cfgInit_wf hr0 cert_stepsInit hm0
    (by rw [BitVec.ofNat_mul 4 183]; exact pc_of_eq hpc1 (by decide +kernel)) hrun1 ?_
  intro s2 envF stEnd hpc2 hrun2 hspF hrcF _hrlF heval hm2 hchk
  exact seg2_row_init_rej (fpVal := fpVal) hrho hrow (by simp [env0, mkSegEnv]) (by simp [env0, mkSegEnv])
    (fun k hk => by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [env0, mkSegEnv]) rfl hpc2 hrun2 hspF hrcF heval hm2 hchk

theorem seg2_row_init_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3)
    {tA : BTree (BitVec 64) 9} (htA : Seg2ConstWordsInv sp rho tA)
    {F : SepProp} {s0 : State}
    (hpc0 : s0.pc = b + 0x02b8#64) (hrun0 : s0.status = .Running)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hreg0 : Seg2RegInv sp fpVal s0) (hx1_0 : s0.readReg64 .x1 = BitVec.ofNat 64 row) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0 then b + 0x3048#64 else b + 0x2300#64) s0
      (TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
        memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
        memRegion (sp + 29024#64) 24 ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg2RowDone b sp fpVal rho row F sf Pf
        else Seg2LoopState b sp fpVal rho row F 0 sf Pf) := by
  refine SepWP.congr_pre (P1 := memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 29024#64) 24 ∗
      (TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗ memRegion (sp + 27840#64) 504 ∗ F))
      (by apply sepProp_ext <;> sep_frame) ?_
  refine sepWP_seq_frozen hcl0 hro0
    (seg2_row_memset hb hbase s0 sp fpVal row _ hpc0 hrun0 hreg0 hx1_0 hcl0) ?_
  intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hreg1, hx22_1, hP1⟩
  exact sepWP_seq_frozen hcl1 hro1
    (seg2_row_init_pre_clamp hrho hrow htA hpc1 hrun1 hro1 hreg1 hx22_1 hP1)
    (fun sF PF hpcF hrunF hclF hroF ⟨hrF, hx1F, hx22F, tA2, sampled', hws', htA2, hraw, hs01F, hs2F, hPF⟩ =>
      sepWP_mono_pre hPF (seg2_row_clamp_init3 hpcF hrunF hclF hroF hrF hx1F hx22F htA2 hraw hs01F hs2F))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row
