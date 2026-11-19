/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init

/-!
# `decapsulate_compressed_key` (`B04`) — `Seg5` Symbolic Entry, `KProg` Runner, & Clamp (`Seg5Clamp`)

Shared symbolic entry state constructor (`mkSegState04` / `mkSegEnv04`), `runAndCheckKProg04` /
`sepWP_of_runAndCheckKProg04`, and `finish_clamp_branch04` for both post-`rej_sample` clamp/branch
dispatchers (`+0x6370 → +0x63d8 / +0x40d8` and `+0x7040 → +0x63d8 / +0x40d8`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem treeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf KStateMatches KSpatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  btree_ext_get readSlot slotHolds slotValid vreg128_repack writeSlot)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep checkLoopInputs evalExprList25 evalKExpr_congr_ok eval_checked_slot exprVarsOk
  extendLoopVars progBases progBasesAux rhoW rowPermState rowSeeds specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  raw_sampled_le271 selHi255_of_le271)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  exprVarsOk_true kexprBeq_refl sepWP_drop_left writeSlotsPair)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  evalSlotsHi evalSlotsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (blkLib04 blkPC04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  InSeg5Word04 inv01Slots inv2Slots runKRange04
  sepWP_of_runKRange04 sepWP_of_stepKLoop04 stepKLoopSym04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init (
  Seg5ConstWordsInv Seg5LoopState Seg5RegInv Seg5RowDone cfgClamp04 multiLaneSampled3_eq_treeMem04)

attribute [local irreducible] keccakF1600 blkLib04

/-! ## 1. Multi-Step `KProg` Runner for `B04` `Seg5` (`4324 ≤ w ≤ 7236`) -/

@[expose] def runKProgSteps04 (cfg : KCfg) (wLo wHi initBnd : Nat) :
    Nat → List Nat → List KProgStep → KState → Option (Nat × List Nat × KState)
  | wCur, bases, [], st => some (wCur, bases, st)
  | wCur, bases, .range w count :: rest, st =>
      if Nat.beq wCur w && Nat.ble wLo w && Nat.ble (w + count) wHi then
        match runKRange04 cfg w count st with
        | none => none
        | some st' => runKProgSteps04 cfg wLo wHi initBnd (w + count) bases rest st'
      else none
  | wCur, bases, .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, st =>
      if Nat.beq wCur wHead && Nat.ble initBnd baseOut &&
         bases.all (fun b => Nat.ble (b + 658) baseOut) &&
         checkLoopInputs cfg (validSpecVar initBnd bases) st slots expLo expHi then
        match stepKLoopSym04 cfg wHead nBody rCnt slots baseOut st with
        | none => none
        | some st' =>
            runKProgSteps04 cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      else none

@[expose] def runAndCheckKProg04 (cfg : KCfg) (wLo wHi wStart wEnd initBnd : Nat)
    (steps : List KProgStep) (st0 : KState)
    (chk : (Nat → Bool) → KState → Bool) : Bool :=
  Nat.ble 4324 wLo && Nat.ble wHi 7236 &&
  match runKProgSteps04 cfg wLo wHi initBnd wStart [] steps st0 with
  | none => false
  | some (wFinal, finalBases, stEnd) =>
      Nat.beq wFinal wEnd && chk (validSpecVar initBnd finalBases) stEnd

private theorem validSpecVar_lt_baseOut {initBnd baseOut id : Nat} {bases : List Nat}
    (hinit : initBnd ≤ baseOut) (hbases : bases.all (fun b => Nat.ble (b + 658) baseOut) = true)
    (hv : validSpecVar initBnd bases id = true) : id < baseOut := by
  simp only [validSpecVar, Bool.or_eq_true, Nat.blt_eq, List.any_eq_true, Bool.and_eq_true,
    Nat.ble_eq] at hv
  rcases hv with hlt | ⟨b, hbmem, _, hlt50⟩
  · omega
  · have hb658 : b + 658 ≤ baseOut := by
      simpa [Nat.ble_eq] using List.all_eq_true.mp hbases b hbmem
    omega

private theorem sepWP_of_runKProgSteps04 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {wLo wHi initBnd : Nat}
    (hmin : 4324 ≤ wLo) (hmax : wHi ≤ 7236)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (steps : List KProgStep) (wCur wFinal : Nat) (bases finalBases : List Nat)
      (st stEnd : KState) (env envSpec : KEnv) (s0 : State),
      runKProgSteps04 cfg wLo wHi initBnd wCur bases steps st = some (wFinal, finalBases, stEnd) →
      env.rLoop < 24 →
      env.sp = envSpec.sp → env.rcBase = envSpec.rcBase → env.rLoop = envSpec.rLoop →
      (∀ id, validSpecVar initBnd bases id = true → env.vars id = envSpec.vars id) →
      KStateMatches env st s0 →
      s0.pc = b + BitVec.ofNat 64 (4 * wCur) →
      s0.status = .Running →
      (∀ (sf : State) (envFinal : KEnv),
        sf.pc = b + BitVec.ofNat 64 (4 * wFinal) →
        sf.status = .Running →
        finalBases = progBasesAux bases steps →
        envFinal.sp = envSpec.sp → envFinal.rcBase = envSpec.rcBase →
        envFinal.rLoop = envSpec.rLoop →
        (∀ id, validSpecVar initBnd finalBases id = true →
          envFinal.vars id = (specEnvSteps envSpec steps).vars id) →
        KStateMatches envFinal stEnd sf →
        SepWP (blkPC04.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env st F) post oom
  | [], wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, _, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps04, Option.some.injEq, Prod.mk.injEq] at hrun_p
      rcases hrun_p with ⟨rfl, rfl, rfl⟩
      exact hnext s0 env hpc0 hrun0 rfl hsp hrc hrl hvars hm0
  | .range w count :: rest, wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps04] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨hcur, hlo⟩, hhi⟩
        subst wCur
        cases hrng : runKRange04 cfg w count st with
        | none => simp [hrng] at hrun_p
        | some st' =>
            simp only [hrng] at hrun_p
            exact sepWP_of_runKRange04 hv hrLoop (fun k hk => Or.inr ⟨by omega, by omega⟩)
              hrng hpc0 hrun0 hm0 (fun sf1 hpc1 hrun1 hm1 =>
                sepWP_of_runKProgSteps04 hv hmin hmax rest (w + count) wFinal bases finalBases
                  st' stEnd env envSpec sf1 hrun_p hrLoop hsp hrc hrl hvars hm1 hpc1 hrun1 hnext)
      · contradiction
  | .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, wCur, wFinal, bases, finalBases,
      st, stEnd, env, envSpec, s0, hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0,
      hnext => by
      simp only [runKProgSteps04] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨⟨hcur, hinit⟩, hbases⟩, hinp⟩
        subst wCur
        cases hstep : stepKLoopSym04 cfg wHead nBody rCnt slots baseOut st with
        | none => simp [hstep] at hrun_p
        | some st' =>
            simp only [hstep] at hrun_p
            have hslotsLo : evalSlotsLo cfg env st slots = evalExprList25 envSpec expLo := by
              apply Array.ext
              · simp [evalSlotsLo, evalExprList25]
              · intro idx h1 _
                have hidx : idx < 25 := by simpa [evalSlotsLo] using h1
                have hinpIdx := List.all_eq_true.mp hinp idx (List.mem_range.mpr hidx)
                simp only [Bool.and_eq_true] at hinpIdx
                rcases hinpIdx with ⟨⟨⟨heqLo, _⟩, hokLo⟩, _⟩
                simp only [evalSlotsLo, evalExprList25, Array.getElem_ofFn, KExpr.beq_eq_true heqLo]
                exact evalKExpr_congr_ok hsp hrc hrl hvars _ hokLo
            have hslotsHi : evalSlotsHi cfg env st slots = evalExprList25 envSpec expHi := by
              apply Array.ext
              · simp [evalSlotsHi, evalExprList25]
              · intro idx h1 _
                have hidx : idx < 25 := by simpa [evalSlotsHi] using h1
                have hinpIdx := List.all_eq_true.mp hinp idx (List.mem_range.mpr hidx)
                simp only [Bool.and_eq_true] at hinpIdx
                rcases hinpIdx with ⟨⟨⟨_, heqHi⟩, _⟩, hokHi⟩
                simp only [evalSlotsHi, evalExprList25, Array.getElem_ofFn, KExpr.beq_eq_true heqHi]
                exact evalKExpr_congr_ok hsp hrc hrl hvars _ hokHi
            refine sepWP_of_stepKLoop04 hv hstep hm0 hpc0 hrun0 ?_
            intro sf1 envPost hpc1 hrun1 hspP hrcP hrlP hpreP hloP hhiP hm1
            let envSpec' :=
              extendLoopVars envSpec baseOut (evalExprList25 envSpec expLo) (evalExprList25 envSpec expHi)
            have hvars' : ∀ id, validSpecVar initBnd (baseOut :: bases) id = true →
                envPost.vars id = envSpec'.vars id := by
              intro id hv'
              by_cases hltB : id < baseOut
              · have hvOld : validSpecVar initBnd bases id = true := by
                  simp only [validSpecVar, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
                    Nat.ble_eq, Nat.blt_eq] at hv' ⊢
                  rcases hv' with h0 | hnew | hold
                  · exact Or.inl h0
                  · omega
                  · exact Or.inr hold
                rw [hpreP id hltB, hvars id hvOld]
                simp [envSpec', extendLoopVars, hltB]
              · by_cases hlt25 : id < baseOut + 25
                · have hidx : id - baseOut < 25 := by omega
                  have heq : baseOut + (id - baseOut) = id := by omega
                  have h1 := hloP (id - baseOut) hidx
                  rw [heq, hslotsLo] at h1
                  simp [envSpec', extendLoopVars, hltB, hlt25, h1]
                · by_cases hlt50 : id < baseOut + 50
                  · have hidx : id - (baseOut + 25) < 25 := by omega
                    have heq : baseOut + 25 + (id - (baseOut + 25)) = id := by omega
                    have h1 := hhiP (id - (baseOut + 25)) hidx
                    rw [heq, hslotsHi] at h1
                    simp [envSpec', extendLoopVars, hltB, hlt25, hlt50, h1]
                  · have hvOld : validSpecVar initBnd bases id = true := by
                      simp only [validSpecVar, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
                        Nat.ble_eq, Nat.blt_eq] at hv' ⊢
                      rcases hv' with h0 | hnew | hold
                      · exact Or.inl h0
                      · omega
                      · exact Or.inr hold
                    exact absurd (validSpecVar_lt_baseOut hinit hbases hvOld) hltB
            exact sepWP_of_runKProgSteps04 hv hmin hmax rest (wHead + nBody + 1) wFinal
              (baseOut :: bases) finalBases st' stEnd envPost envSpec' sf1 hrun_p
              (hrlP ▸ hrLoop) (hspP.trans hsp) (hrcP.trans hrc) (hrlP.trans hrl)
              hvars' hm1 hpc1 hrun1 hnext
      · contradiction

theorem sepWP_of_runAndCheckKProg04 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {env0 : KEnv} (hrLoop : env0.rLoop < 24)
    {wLo wHi wStart wEnd initBnd : Nat} {steps : List KProgStep} {st0 : KState}
    {chk : (Nat → Bool) → KState → Bool}
    (hcert : runAndCheckKProg04 cfg wLo wHi wStart wEnd initBnd steps st0 chk = true)
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hm0 : KStateMatches env0 st0 s0)
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wStart)) (hrun0 : s0.status = .Running)
    (hnext : ∀ (sf : State) (envFinal : KEnv) (stEnd : KState),
      sf.pc = b + BitVec.ofNat 64 (4 * wEnd) →
      sf.status = .Running →
      envFinal.sp = env0.sp → envFinal.rcBase = env0.rcBase → envFinal.rLoop = env0.rLoop →
      (∀ e, exprVarsOk (validSpecVar initBnd (progBases steps)) e = true →
        evalKExpr envFinal e = evalKExpr (specEnvSteps env0 steps) e) →
      KStateMatches envFinal stEnd sf →
      chk (validSpecVar initBnd (progBases steps)) stEnd = true →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 st0 F) post oom := by
  simp only [runAndCheckKProg04, Bool.and_eq_true, Nat.ble_eq] at hcert
  rcases hcert with ⟨⟨hmin, hmax⟩, hrest⟩
  cases hrun_p : runKProgSteps04 cfg wLo wHi initBnd wStart [] steps st0 with
  | none => simp [hrun_p] at hrest
  | some triple =>
      rcases triple with ⟨wFinal, finalBases, stEnd⟩
      simp only [hrun_p, Bool.and_eq_true, Nat.beq_eq] at hrest
      rcases hrest with ⟨rfl, hchk⟩
      refine sepWP_of_runKProgSteps04 hv hmin hmax steps wStart wFinal [] finalBases
        st0 stEnd env0 env0 s0 hrun_p hrLoop rfl rfl rfl (fun _ _ => rfl) hm0 hpc0 hrun0 ?_
      intro sf envFinal hpcF hrunF hfbEq hspF hrcF hrlF hvarsF hmF
      subst hfbEq
      have hspecEq : (specEnvSteps env0 steps).sp = env0.sp ∧
          (specEnvSteps env0 steps).rcBase = env0.rcBase ∧
          (specEnvSteps env0 steps).rLoop = env0.rLoop := by
        have aux : ∀ (es : List KProgStep) (e : KEnv),
            (specEnvSteps e es).sp = e.sp ∧
            (specEnvSteps e es).rcBase = e.rcBase ∧
            (specEnvSteps e es).rLoop = e.rLoop := by
          intro es; induction es with
          | nil => intro e; exact ⟨rfl, rfl, rfl⟩
          | cons s tl ih => intro e; cases s <;> exact ih _
        exact aux steps env0
      exact hnext sf envFinal stEnd hpcF hrunF hspF hrcF hrlF
        (fun e hok => evalKExpr_congr_ok
          (hspF.trans hspecEq.1.symm) (hrcF.trans hspecEq.2.1.symm) (hrlF.trans hspecEq.2.2.symm)
          hvarsF e hok)
        hmF hchk

/-! ## 2. Symbolic Entry State Builder (`mkSegState04` / `mkSegEnv04`) -/

@[expose] def constMemAIdxs04 : List Nat :=
  [0, 1, 2, 3, 5, 6, 7, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

@[expose] def constMemAExpr04 (i : Nat) : KExpr :=
  if i == 0 then .const64 0x001f0200#64 else if i == 1 then .const64 0#64
  else if i == 2 then .const64 0x001f0100#64 else if i == 3 then .const64 0#64
  else if i == 5 then .spAdd 22411#64 else if i == 6 then .spAdd 13392#64
  else if i == 7 then .spAdd 22664#64
  else if i == 38 then .const64 0xffffffffff0000ff#64
  else if i == 39 then .const64 0xffffffffffffffff#64
  else if i == 40 || i == 41 then .var 106
  else if i == 42 || i == 43 then .var 105
  else if i == 44 || i == 45 then .var 104
  else if i == 46 || i == 47 then .var 103
  else .var (300 + i)

@[expose] def segGprExpr04 (g : Nat) : KExpr :=
  if g == 8 then .var 101
  else if g == 19 then .var 100
  else if g == 20 then .spAdd 23704#64
  else if g == 21 then .const64 544#64
  else if g == 22 then .rcAdd 0#64
  else if g == 23 then .spAdd 19168#64
  else if g == 24 then .spAdd 20715#64
  else if g == 25 then .const64 256#64
  else if g == 26 then .spAdd 20704#64
  else if g == 27 then .spAdd 5680#64
  else if g == 28 then .spAdd 20968#64
  else if g == 29 then .var 102
  else .var (200 + g)

@[expose] def mkSegBaseState04 (hasConsts : Bool) : KState :=
  { vregs := BTree.ofFn 5 fun vr => (.var (110 + 2 * vr), .var (110 + 2 * vr + 1))
    gprs := BTree.ofFn 5 segGprExpr04
    memA := BTree.ofFn 9 fun i => if hasConsts then constMemAExpr04 i else .var (300 + i)
    memB := BTree.ofFn 9 fun i => .var (900 + i)
    pstate := none }

@[expose] def mkSegState04 (cfg : KCfg) (hasConsts : Bool) (slots01 slots2 : List KSlot) : KState :=
  writeSlotsPair cfg 50 75 0 slots2 (writeSlotsPair cfg 0 25 0 slots01 (mkSegBaseState04 hasConsts))

@[expose] def mkSegEnv04 [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat) (rho : List (BitVec 8))
    (k0 k1 k2 : KeccakState) (k2Hi : Nat → BitVec 64) (s : State) (tA tB : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp
    rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    rLoop := 0
    vars := fun id =>
      if id < 25 then k0.getD id 0#64
      else if id < 50 then k1.getD (id - 25) 0#64
      else if id < 75 then k2.getD (id - 50) 0#64
      else if id < 100 then k2Hi (id - 75)
      else if id == 100 then BitVec.ofNat 64 row
      else if id == 101 then s.readReg64 .x8
      else if id == 102 then fpVal
      else if id == 103 then rhoW rho 0
      else if id == 104 then rhoW rho 1
      else if id == 105 then rhoW rho 2
      else if id == 106 then rhoW rho 3
      else if id < 174 then
        let k := id - 110
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 }

private theorem writeSlot_preserves {cfg : KCfg} {env : KEnv} {st : KState} {s : State}
    {tA : BTree (BitVec 64) 9} {sl : KSlot} {p : KExpr × KExpr}
    (hm : KStateMatches env st s) (htA : st.memA.map (evalKExpr env) = tA)
    (hsl : slotHolds cfg s tA sl (evalKExpr env p.1) (evalKExpr env p.2)) :
    KStateMatches env (writeSlot cfg st sl p) s ∧
      (writeSlot cfg st sl p).memA.map (evalKExpr env) = tA ∧
      (writeSlot cfg st sl p).memB = st.memB := by
  cases sl with
  | vreg r =>
      rcases hsl with ⟨hr, hv⟩; refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpstate⟩, htA, rfl⟩
      intro vr; simp only [writeSlot]; rw [BTree.get_set _ r p hr vr.toNat vr.isLt]
      by_cases heq : vr.toNat = r
      · have hvr : vr = BitVec.ofNat 5 r := BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hr])
        subst hvr; simpa [heq] using hv
      · simp [heq]; exact hm.hvregs vr
  | spillQ off =>
      rcases hsl with ⟨hidx, hlo, hhi⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩, ?_, rfl⟩
      apply btree_ext_get; intro j hj
      simp only [writeSlot, BTree.get_map]
      rw [BTree.get_set _ _ _ hidx j hj]
      by_cases h1 : j = (off - cfg.offA) / 8 + 1
      · subst h1; simpa using hhi.symm
      · simp only [h1, ↓reduceIte]; rw [BTree.get_set _ _ _ (by omega) j hj]
        by_cases h0 : j = (off - cfg.offA) / 8
        · subst h0; simpa using hlo.symm
        · simp only [h0, ↓reduceIte]; rw [← htA, BTree.get_map]

private theorem mkSegEnv04_var_ge110 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {rho : List (BitVec 8)} {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64}
    {s : State} {tA tB : BTree (BitVec 64) 9} {id : Nat} (hid : 110 ≤ id) :
    (mkSegEnv04 sp fpVal row rho k0 k1 k2 k2Hi s tA tB).vars id =
      if id < 174 then
        let k := id - 110
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 := by
  simp only [mkSegEnv04, show ¬(id < 25) by omega, show ¬(id < 50) by omega,
    show ¬(id < 75) by omega, show ¬(id < 100) by omega,
    beq_false_of_ne (show id ≠ 100 by omega), beq_false_of_ne (show id ≠ 101 by omega),
    beq_false_of_ne (show id ≠ 102 by omega), beq_false_of_ne (show id ≠ 103 by omega),
    beq_false_of_ne (show id ≠ 104 by omega), beq_false_of_ne (show id ≠ 105 by omega),
    beq_false_of_ne (show id ≠ 106 by omega), Bool.false_eq_true, ↓reduceIte]

private theorem mkSegBaseState04_matches [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {rho : List (BitVec 8)} {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64}
    {s : State} {tA tB : BTree (BitVec 64) 9} {hasConsts : Bool}
    (hreg : Seg5RegInv sp fpVal s) (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row)
    (htA : hasConsts = true → Seg5ConstWordsInv sp rho tA) :
    let env := mkSegEnv04 sp fpVal row rho k0 k1 k2 k2Hi s tA tB
    KStateMatches env (mkSegBaseState04 hasConsts) s ∧
      (mkSegBaseState04 hasConsts).memA.map (evalKExpr env) = tA ∧
      (mkSegBaseState04 hasConsts).memB.map (evalKExpr env) = tB := by
  intro env
  rcases hreg with ⟨hsp, hspA, hfp, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  refine ⟨⟨hsp, hspA, ?_, ?_, fun _ _ h => nomatch h⟩, ?_, ?_⟩
  · intro vr
    simp only [mkSegBaseState04]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
    have hlt := vr.isLt
    simp only [evalKExpr, env, mkSegEnv04_var_ge110 (show 110 ≤ 110 + 2 * vr.toNat by omega),
      mkSegEnv04_var_ge110 (show 110 ≤ 110 + 2 * vr.toNat + 1 by omega),
      show 110 + 2 * vr.toNat < 174 by omega, show 110 + 2 * vr.toNat + 1 < 174 by omega,
      ↓reduceIte, show (110 + 2 * vr.toNat - 110) / 2 = vr.toNat by omega,
      show ((110 + 2 * vr.toNat - 110) % 2 == 0) = true from beq_iff_eq.mpr (by omega),
      show (110 + 2 * vr.toNat + 1 - 110) / 2 = vr.toNat by omega,
      show ((110 + 2 * vr.toNat + 1 - 110) % 2 == 0) = false from beq_false_of_ne (by omega),
      Bool.false_eq_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g hg31
    simp only [mkSegBaseState04]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
    have hlt := g.isLt
    by_cases h8 : g = 8#5; · subst h8; rfl
    by_cases h19 : g = 19#5; · subst h19; exact hx19
    by_cases h20 : g = 20#5; · subst h20; exact hx20
    by_cases h21 : g = 21#5; · subst h21; exact hx21
    by_cases h22 : g = 22#5; · subst h22; simpa [segGprExpr04, evalKExpr, env, mkSegEnv04] using hx22
    by_cases h23 : g = 23#5; · subst h23; exact hx23
    by_cases h24 : g = 24#5; · subst h24; exact hx24
    by_cases h25 : g = 25#5; · subst h25; exact hx25
    by_cases h26 : g = 26#5; · subst h26; exact hx26
    by_cases h27 : g = 27#5; · subst h27; exact hx27
    by_cases h28 : g = 28#5; · subst h28; exact hx28
    by_cases h29 : g = 29#5; · subst h29; exact hfp
    have hne : ∀ c : Fin 32, g ≠ BitVec.ofNat 5 c.1 → (g.toNat == c.1) = false := fun c hc =>
      beq_false_of_ne fun he => hc (BitVec.eq_of_toNat_eq (by simp [he]))
    simp only [segGprExpr04, hne ⟨8, by decide⟩ h8, hne ⟨19, by decide⟩ h19,
      hne ⟨20, by decide⟩ h20, hne ⟨21, by decide⟩ h21, hne ⟨22, by decide⟩ h22,
      hne ⟨23, by decide⟩ h23, hne ⟨24, by decide⟩ h24, hne ⟨25, by decide⟩ h25,
      hne ⟨26, by decide⟩ h26, hne ⟨27, by decide⟩ h27, hne ⟨28, by decide⟩ h28,
      hne ⟨29, by decide⟩ h29, Bool.false_eq_true, ↓reduceIte,
      evalKExpr, env, mkSegEnv04_var_ge110 (show 110 ≤ 200 + g.toNat by omega),
      show ¬(200 + g.toNat < 174) by omega, show 200 + g.toNat < 232 by omega,
      show 200 + g.toNat - 200 = g.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · apply btree_ext_get; intro j hj
    simp only [BTree.get_map, mkSegBaseState04]; rw [BTree.get_ofFn 9 _ j hj]
    cases hasConsts with
    | false =>
        simp [evalKExpr, env, mkSegEnv04_var_ge110 (show 110 ≤ 300 + j by omega),
          show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
          show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
    | true =>
        rcases htA rfl with ⟨c0, c1, c2, c3, c5, c6, c7, c38, c39, c40, c41,
          c42, c43, c44, c45, c46, c47⟩
        by_cases hj8 : j < 8
        · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [constMemAExpr04, evalKExpr, env, mkSegEnv04, c0, c1, c2, c3, c5, c6, c7]
        · by_cases hj38 : 38 ≤ j ∧ j < 48
          · rcases (show j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 by omega) with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [constMemAExpr04, evalKExpr, env, mkSegEnv04, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47]
          · have hne : ∀ c, c ≠ j → (j == c) = false := fun _ hc => beq_false_of_ne hc.symm
            simp only [↓reduceIte, constMemAExpr04, hne 0 (by omega), hne 1 (by omega),
              hne 2 (by omega), hne 3 (by omega), hne 5 (by omega), hne 6 (by omega),
              hne 7 (by omega), hne 38 (by omega), hne 39 (by omega), hne 40 (by omega),
              hne 41 (by omega), hne 42 (by omega), hne 43 (by omega), hne 44 (by omega),
              hne 45 (by omega), hne 46 (by omega), hne 47 (by omega), Bool.false_or,
              Bool.false_eq_true, evalKExpr, env,
              mkSegEnv04_var_ge110 (show 110 ≤ 300 + j by omega),
              show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
              show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
  · apply btree_ext_get; intro j hj
    simp only [BTree.get_map, mkSegBaseState04]; rw [BTree.get_ofFn 9 _ j hj]
    simp [evalKExpr, env, mkSegEnv04_var_ge110 (show 110 ≤ 900 + j by omega),
      show ¬(900 + j < 174) by omega, show ¬(900 + j < 232) by omega,
      show ¬(900 + j < 812) by omega, show 900 + j < 1412 by omega, show 900 + j - 900 = j by omega]

private theorem writeSlotsPair_matches {cfg : KCfg} {env : KEnv} {offLo offHi : Nat}
    {fLo fHi : Nat → BitVec 64} {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hvLo : ∀ k, k < 25 → evalKExpr env (.var (offLo + k)) = fLo k)
    (hvHi : ∀ k, k < 25 → evalKExpr env (.var (offHi + k)) = fHi k)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length ≤ 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (fLo (k + j)) (fHi (k + j))) →
      KStateMatches env st s → st.memA.map (evalKExpr env) = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsPair cfg offLo offHi k rem st) s ∧
        (writeSlotsPair cfg offLo offHi k rem st).memA.map (evalKExpr env) = tA ∧
        (writeSlotsPair cfg offLo offHi k rem st).memB = mB0 := by
  induction rem with
  | nil => intro _ _ _ _ hm htA hmB; exact ⟨hm, htA, hmB⟩
  | cons sl rest ih =>
      intro k st hsum hsl hm htA hmB
      have hk : k < 25 := by simp only [List.length_cons] at hsum; omega
      have hsl0 : slotHolds cfg s tA sl
          (evalKExpr env (.var (offLo + k))) (evalKExpr env (.var (offHi + k))) := by
        rw [hvLo k hk, hvHi k hk]
        simpa only [List.getD_cons_zero, Nat.add_zero] using hsl 0 (by simp)
      rcases writeSlot_preserves (p := (.var (offLo + k), .var (offHi + k))) hm htA hsl0
        with ⟨hm1, htA1, hmB1⟩
      exact ih (k + 1) _ (by simp only [List.length_cons] at hsum; omega)
        (fun j hj => by
          have hj1 := hsl (j + 1) (by simp only [List.length_cons]; omega)
          rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega] at hj1
          exact hj1)
        hm1 htA1 (hmB1.trans hmB)

theorem mkSegState04_matches [MlKemPlacement] {cfg : KCfg} {hasConsts : Bool}
    {slots01 slots2 : List KSlot} {sp fpVal : BitVec 64} {row : Nat} {rho : List (BitVec 8)}
    {k0 k1 k2 : KeccakState} {k2Hi : Nat → BitVec 64} {s : State} {tA tB : BTree (BitVec 64) 9}
    (hl01 : slots01.length ≤ 25) (hl2 : slots2.length ≤ 25)
    (hreg : Seg5RegInv sp fpVal s) (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row)
    (htA : hasConsts = true → Seg5ConstWordsInv sp rho tA)
    (hs01 : ∀ idx, idx < slots01.length →
      slotHolds cfg s tA (slots01.getD idx (.vreg 0)) (k0.getD idx 0#64) (k1.getD idx 0#64))
    (hs2 : ∀ idx, idx < slots2.length →
      slotHolds cfg s tA (slots2.getD idx (.vreg 0)) (k2.getD idx 0#64) (k2Hi idx)) :
    let env := mkSegEnv04 sp fpVal row rho k0 k1 k2 k2Hi s tA tB
    let st := mkSegState04 cfg hasConsts slots01 slots2
    KStateMatches env st s ∧ st.memA.map (evalKExpr env) = tA ∧ st.memB.map (evalKExpr env) = tB := by
  intro env st
  rcases mkSegBaseState04_matches (k0 := k0) (k1 := k1) (k2 := k2) (k2Hi := k2Hi)
    (tA := tA) (tB := tB) hreg hx19 htA with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 → evalKExpr env (.var (0 + k)) = k0.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, env, mkSegEnv04, hk]
  have hv1 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = k1.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv04, show ¬(25 + k < 25) by omega,
      show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  have hv2 : ∀ k, k < 25 → evalKExpr env (.var (50 + k)) = k2.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv04, show ¬(50 + k < 25) by omega,
      show ¬(50 + k < 50) by omega, show 50 + k < 75 by omega, show 50 + k - 50 = k by omega]
  have hv2Hi : ∀ k, k < 25 → evalKExpr env (.var (75 + k)) = k2Hi k := fun k hk => by
    simp [evalKExpr, env, mkSegEnv04, show ¬(75 + k < 25) by omega,
      show ¬(75 + k < 50) by omega, show ¬(75 + k < 75) by omega,
      show 75 + k < 100 by omega, show 75 + k - 75 = k by omega]
  rcases writeSlotsPair_matches (cfg := cfg) hv0 hv1 slots01 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs01 j hj) hm0 htA0 rfl with ⟨hm1, htA1, hmB1⟩
  rcases writeSlotsPair_matches (cfg := cfg) hv2 hv2Hi slots2 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs2 j hj) hm1 htA1 rfl with ⟨hm2, htA2, hmB2⟩
  exact ⟨hm2, htA2, by dsimp only [st, mkSegState04]; rw [hmB2, hmB1, htB0]⟩

/-! ## 3. Clamp Post-State Checker & `finish_clamp_branch04` -/

@[expose] def checkSegRegGprs04 (st : KState) (eX8 : KExpr) : Bool :=
  (st.gprs.get 8).beq eX8 &&
  (st.gprs.get 19).beq (.var 100) &&
  (st.gprs.get 20).beq (.spAdd 23704#64) &&
  (st.gprs.get 21).beq (.const64 544#64) &&
  (st.gprs.get 22).beq (.rcAdd 0#64) &&
  (st.gprs.get 23).beq (.spAdd 19168#64) &&
  (st.gprs.get 24).beq (.spAdd 20715#64) &&
  (st.gprs.get 25).beq (.const64 256#64) &&
  (st.gprs.get 26).beq (.spAdd 20704#64) &&
  (st.gprs.get 27).beq (.spAdd 5680#64) &&
  (st.gprs.get 28).beq (.spAdd 20968#64) &&
  (st.gprs.get 29).beq (.var 102)

@[expose] def checkConstWordsMemA04 (st : KState) : Bool :=
  constMemAIdxs04.all fun i => (st.memA.get i).beq (constMemAExpr04 i)

@[expose] def checkClampEnd04 (st : KState) (checkInvSlots : Bool) : Bool :=
  checkSegRegGprs04 st (.var 101) &&
  checkConstWordsMemA04 st &&
  (st.memB.get 0).beq (.selHi255 (.var 900) (.const64 256#64) (.var 900)) &&
  (st.memB.get 1).beq (.selHi255 (.var 901) (.const64 256#64) (.var 901)) &&
  (st.memB.get 2).beq (.selHi255 (.var 902) (.const64 256#64) (.var 902)) &&
  (!checkInvSlots ||
    (((List.range 25).all fun idx =>
        let sl := inv01Slots.getD idx (.vreg 0)
        slotValid cfgClamp04 sl &&
          (readSlot cfgClamp04 st sl).1.beq (.var idx) &&
          (readSlot cfgClamp04 st sl).2.beq (.var (25 + idx))) &&
     ((List.range 25).all fun idx =>
        let sl := inv2Slots.getD idx (.vreg 0)
        slotValid cfgClamp04 sl &&
          (readSlot cfgClamp04 st sl).1.beq (.var (50 + idx)))))

theorem with_frozen_env04 [MlKemPlacement] {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf =>
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem → post sf Pf)) :
    SepWP prog tgt s P post :=
  SepWP.mono_frozen (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
    ⟨hcl, hro⟩ h (fun _ _ _ _ ⟨hc, hr⟩ hp => hp hc hr)

theorem extract_segRegInv04 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat} {eX8 : KExpr}
    {env : KEnv} {st : KState} {sf : State}
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv100 : env.vars 100 = BitVec.ofNat 64 row) (hv102 : env.vars 102 = fpVal)
    (hchk : checkSegRegGprs04 st eX8 = true) :
    Seg5RegInv sp fpVal sf ∧ sf.readReg64 .x8 = evalKExpr env eX8 ∧
      sf.readReg64 .x19 = BitVec.ofNat 64 row := by
  simp only [checkSegRegGprs04, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g8, g19⟩, g20⟩, g21⟩, g22⟩, g23⟩, g24⟩, g25⟩, g26⟩, g27⟩, g28⟩, g29⟩
  have rg : ∀ (g : Fin 32), g.1 ≠ 31 → ∀ {e : KExpr}, (st.gprs.get g.1).beq e = true →
      sf.readReg64 (.gpr (BitVec.ofNat 5 g.1)) = evalKExpr env e := by
    intro g hg e hb
    have r := hm.hgprs (BitVec.ofNat 5 g.1) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt g.2]; have := g.2; omega)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt g.2, KExpr.beq_eq_true hb] at r
    exact r
  refine ⟨⟨hm.hsp.trans hsp, hm.hsp_al, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rg ⟨8, by decide⟩ (by decide) g8, ?_⟩
  · simpa [evalKExpr, hv102] using rg ⟨29, by decide⟩ (by decide) g29
  · simpa [evalKExpr, hsp] using rg ⟨20, by decide⟩ (by decide) g20
  · simpa [evalKExpr] using rg ⟨21, by decide⟩ (by decide) g21
  · simpa [evalKExpr, hrc] using rg ⟨22, by decide⟩ (by decide) g22
  · simpa [evalKExpr, hsp] using rg ⟨23, by decide⟩ (by decide) g23
  · simpa [evalKExpr, hsp] using rg ⟨24, by decide⟩ (by decide) g24
  · simpa [evalKExpr] using rg ⟨25, by decide⟩ (by decide) g25
  · simpa [evalKExpr, hsp] using rg ⟨26, by decide⟩ (by decide) g26
  · simpa [evalKExpr, hsp] using rg ⟨27, by decide⟩ (by decide) g27
  · simpa [evalKExpr, hsp] using rg ⟨28, by decide⟩ (by decide) g28
  · simpa [evalKExpr, hv100] using rg ⟨19, by decide⟩ (by decide) g19

theorem extract_constWords04 {sp : BitVec 64} {rho : List (BitVec 8)} {env : KEnv} {st : KState}
    (hsp : env.sp = sp)
    (hv103 : env.vars 103 = rhoW rho 0) (hv104 : env.vars 104 = rhoW rho 1)
    (hv105 : env.vars 105 = rhoW rho 2) (hv106 : env.vars 106 = rhoW rho 3)
    (hchk : checkConstWordsMemA04 st = true) :
    Seg5ConstWordsInv sp rho (st.memA.map (evalKExpr env)) := by
  have hc : ∀ (i : Nat), i ∈ constMemAIdxs04 →
      (st.memA.map (evalKExpr env)).get i = evalKExpr env (constMemAExpr04 i) := fun i hi => by
    have hb := (List.all_eq_true.mp hchk) i hi
    rw [BTree.get_map, KExpr.beq_eq_true hb]
  exact ⟨hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
    (hc 5 (by decide)).trans (by simp [constMemAExpr04, evalKExpr, hsp]),
    (hc 6 (by decide)).trans (by simp [constMemAExpr04, evalKExpr, hsp]),
    (hc 7 (by decide)).trans (by simp [constMemAExpr04, evalKExpr, hsp]),
    hc 38 (by decide), hc 39 (by decide),
    (hc 40 (by decide)).trans hv106, (hc 41 (by decide)).trans hv106,
    (hc 42 (by decide)).trans hv105, (hc 43 (by decide)).trans hv105,
    (hc 44 (by decide)).trans hv104, (hc 45 (by decide)).trans hv104,
    (hc 46 (by decide)).trans hv103, (hc 47 (by decide)).trans hv103⟩

theorem finish_clamp_branch04 [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row extra : Nat} {F : SepProp}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    {env : KEnv} {st : KState} {sf : State}
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) extra sampled hws)
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv100 : env.vars 100 = BitVec.ofNat 64 row)
    (hv101 : env.vars 101 = BitVec.ofNat 64 (row + 1))
    (hv102 : env.vars 102 = fpVal)
    (hv103 : env.vars 103 = rhoW rho 0) (hv104 : env.vars 104 = rhoW rho 1)
    (hv105 : env.vars 105 = rhoW rho 2) (hv106 : env.vars 106 = rhoW rho 3)
    (hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64)
    (hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64)
    (hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64)
    (hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0))
    (hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1))
    (hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2))
    (isExit : Bool) (hdone : allLanesDone 3 (rowSeeds rho row) extra = isExit)
    (hpc : sf.pc = if isExit then b + BitVec.ofNat 64 (4 * 4150) else b + BitVec.ofNat 64 (4 * 6390))
    (hrun : sf.status = .Running)
    (hchk : checkClampEnd04 st (!isExit) = true) :
    let FF := memRegion (sp + 22400#64) 1512 ∗
      MultiLaneSlots (sp + 5680#64) 544 3 hws ∗ memRegion (sp + 20704#64) 504 ∗ F
    SepWP (blkPC04.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) extra
       then b + BitVec.ofNat 64 (4 * 4150) else b + BitVec.ofNat 64 (4 * 6390))
      sf (KSpatial cfgClamp04 env st FF)
      (fun sOut POut => mlkemMultiLib.CodeLoaded mlkemMpl sOut.mem → MlKemRoOk mlkemMpl sOut.mem →
        if allLanesDone 3 (rowSeeds rho row) extra then Seg5RowDone b sp fpVal rho row F sOut POut
        else Seg5LoopState b sp fpVal rho row F extra sOut POut) := by
  intro FF; rw [hdone]
  simp only [checkClampEnd04, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hregC, hconstC⟩, hm0⟩, hm1⟩, hm2⟩, hslotsC⟩
  rcases extract_segRegInv04 hm hsp hrc hv100 hv102 hregC with ⟨hreg, hx8, hx19⟩
  rw [evalKExpr, hv101] at hx8
  have htA := extract_constWords04 hsp hv103 hv104 hv105 hv106 hconstC
  have hclamp : MultiLaneXofInv 3 (rowSeeds rho row) extra (fun i => clampSampled (sampled i)) hws :=
    hraw.clamp
  have htB : ∀ i, i < 3 →
      (st.memB.map (evalKExpr env)).get i = BitVec.ofNat 64 (clampSampled (sampled i)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [BTree.get_map, KExpr.beq_eq_true hm0, evalKExpr, evalKExpr, evalKExpr, hb0]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [BTree.get_map, KExpr.beq_eq_true hm1, evalKExpr, evalKExpr, evalKExpr, hb1]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [BTree.get_map, KExpr.beq_eq_true hm2, evalKExpr, evalKExpr, evalKExpr, hb2]
      exact selHi255_of_le271 (raw_sampled_le271 hraw (by decide))
  have hsampMem : TreeMem (sp + 19168#64) 3 (st.memB.map (evalKExpr env)) =
      MultiLaneSampled (sp + 19168#64) 3 (fun i => clampSampled (sampled i)) :=
    (multiLaneSampled3_eq_treeMem04 sp _ _
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide))).symm
  apply sepWP_drop_left
  cases isExit with
  | true =>
      simp only [↓reduceIte] at hpc ⊢
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx8, hx19, extra,
        st.memA.map (evalKExpr env), fun i => clampSampled (sampled i), hws, hdone, hclamp, htA, ?_⟩
      dsimp only [cfgClamp04, FF]
      rw [hsp, show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
        show sp + BitVec.ofNat 64 19168 = sp + 19168#64 from rfl]
      exact Entails.trans (by sep_frame : _ ⊢ TreeMem (sp + 19168#64) 3 (st.memB.map (evalKExpr env)) ∗
          (TreeMem (sp + 144#64) 264 (st.memA.map (evalKExpr env)) ∗
            memRegion (sp + 22400#64) 1512 ∗ MultiLaneSlots (sp + 5680#64) 544 3 hws ∗
            memRegion (sp + 20704#64) 504 ∗ F))
        (Entails.trans (sepConj_mono_left
          (treeMem_entails_memRegion (ptr := sp + 19168#64) (len := 3) (st.memB.map (evalKExpr env)) (by decide)))
          (by sep_frame))
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
      simp only [Bool.not_false, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hslotsC
      rcases hslotsC with ⟨hs01, hs2⟩
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx8, hx19,
        st.memA.map (evalKExpr env), fun i => clampSampled (sampled i), hws, htA, ?_, ?_, hclamp, ?_⟩
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs01) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        have hsl := eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1.1 _ _ hi.1.2 hi.2 rfl rfl
        simpa [evalKExpr, hv0 idx hidx, hv1 idx hidx] using hsl
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs2) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        refine ⟨evalKExpr env (readSlot cfgClamp04 st (inv2Slots.getD idx (.vreg 0))).2, ?_⟩
        have hsl := eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1 (.var (50 + idx))
          (readSlot cfgClamp04 st (inv2Slots.getD idx (.vreg 0))).2
          hi.2 (kexprBeq_refl _) rfl (exprVarsOk_true _)
        simpa [evalKExpr, hv2 idx hidx] using hsl
      · dsimp only [cfgClamp04, FF]
        rw [hsp, show sp + BitVec.ofNat 64 144 = sp + 144#64 from rfl,
          show sp + BitVec.ofNat 64 19168 = sp + 19168#64 from rfl, hsampMem]
        sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp
