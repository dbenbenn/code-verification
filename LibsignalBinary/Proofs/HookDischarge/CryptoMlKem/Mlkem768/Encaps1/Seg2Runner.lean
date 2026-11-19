/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step

/-!
# `encapsulate1_serialized` (`B03`) — Multi-Step Symbolic Keccak Runner Soundness (`Seg2Runner`)

Soundness of `runAndCheckKProg` (`sepWP_of_runAndCheckKProg`) and structural `KExpr.beq` extractors
(`eval_checked_*`, `checked_Seg2RegInv`, `checked_seedMemA`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (Seg2RegInv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KPFlag KSlot KState evalKExpr runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (seedConstsWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KStateMatches KSpatial evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  readSlot slotHolds slotValid truncate64_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  evalSlotsHi evalSlotsLo kpflagOptBeq kpflagOptBeq_eq_true sepWP_of_stepKLoop stepKLoopSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  KProgStep evalExprList25 evalKExpr_congr_ok exprVarsOk extendLoopVars progBases
  progBasesAux runAndCheckKProg runKProgSteps specEnvSteps validSpecVar)

attribute [local irreducible] keccakF1600 blkPC03

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

private theorem sepWP_of_runKProgSteps [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {wLo wHi initBnd : Nat}
    (hmin : 330 ≤ wLo) (hmax : wHi ≤ 3237)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (steps : List KProgStep) (wCur wFinal : Nat) (bases finalBases : List Nat)
      (st stEnd : KState) (env envSpec : KEnv) (s0 : State),
      runKProgSteps cfg wLo wHi initBnd wCur bases steps st = some (wFinal, finalBases, stEnd) →
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
        SepWP (blkPC03.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env st F) post oom
  | [], wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, _, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun_p
      rcases hrun_p with ⟨rfl, rfl, rfl⟩
      exact hnext s0 env hpc0 hrun0 rfl hsp hrc hrl hvars hm0
  | .range w count :: rest, wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨hcur, hlo⟩, hhi⟩
        subst wCur
        cases hrng : runKRange cfg w count st with
        | none => simp [hrng] at hrun_p
        | some st' =>
            simp only [hrng] at hrun_p
            exact sepWP_runKRange_seg2b hv hrLoop (by omega) (by omega) hpc0 hrun0 hm0 hrng
              (fun sf1 hpc1 hrun1 hm1 =>
                sepWP_of_runKProgSteps hv hmin hmax rest (w + count) wFinal bases finalBases
                  st' stEnd env envSpec sf1 hrun_p hrLoop hsp hrc hrl hvars hm1 hpc1 hrun1 hnext)
      · contradiction
  | .loop isPair wHead nBody rCnt slots expLo expHi baseOut :: rest, wCur, wFinal, bases, finalBases,
      st, stEnd, env, envSpec, s0, hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0,
      hnext => by
      simp only [runKProgSteps] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨⟨hcur, hinit⟩, hbases⟩, hinp⟩
        subst wCur
        cases hstep : stepKLoopSym cfg isPair wHead nBody rCnt slots baseOut st with
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
            refine sepWP_of_stepKLoop hv hstep hm0 hpc0 hrun0 ?_
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
            exact sepWP_of_runKProgSteps hv hmin hmax rest (wHead + nBody + 1) wFinal
              (baseOut :: bases) finalBases st' stEnd envPost envSpec' sf1 hrun_p
              (hrlP ▸ hrLoop) (hspP.trans hsp) (hrcP.trans hrc) (hrlP.trans hrl)
              hvars' hm1 hpc1 hrun1 hnext
      · contradiction

theorem sepWP_of_runAndCheckKProg [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {env0 : KEnv} (hrLoop : env0.rLoop < 24)
    {wLo wHi wStart wEnd initBnd : Nat} {steps : List KProgStep} {st0 : KState}
    {chk : (Nat → Bool) → KState → Bool}
    (hcert : runAndCheckKProg cfg wLo wHi wStart wEnd initBnd steps st0 chk = true)
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
      SepWP (blkPC03.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 st0 F) post oom := by
  simp only [runAndCheckKProg, Bool.and_eq_true, Nat.ble_eq] at hcert
  rcases hcert with ⟨⟨hmin, hmax⟩, hrest⟩
  cases hrun_p : runKProgSteps cfg wLo wHi initBnd wStart [] steps st0 with
  | none => simp [hrun_p] at hrest
  | some triple =>
      rcases triple with ⟨wFinal, finalBases, stEnd⟩
      simp only [hrun_p, Bool.and_eq_true, Nat.beq_eq] at hrest
      rcases hrest with ⟨rfl, hchk⟩
      refine sepWP_of_runKProgSteps hv hmin hmax steps wStart wFinal [] finalBases
        st0 stEnd env0 env0 s0 hrun_p hrLoop rfl rfl rfl (fun _ _ => rfl) hm0 hpc0 hrun0 ?_
      intro sf envFinal hpcF hrunF hfbEq hspF hrcF hrlF hvarsF hmF
      subst hfbEq
      have hspecEq : (specEnvSteps env0 steps).sp = env0.sp ∧
          (specEnvSteps env0 steps).rcBase = env0.rcBase ∧
          (specEnvSteps env0 steps).rLoop = env0.rLoop := by
        have aux : ∀ (es : List KProgStep) (e : KEnv),
            (specEnvSteps e es).sp = e.sp ∧ (specEnvSteps e es).rcBase = e.rcBase ∧
            (specEnvSteps e es).rLoop = e.rLoop := by
          intro es; induction es with
          | nil => intro e; exact ⟨rfl, rfl, rfl⟩
          | cons s tl ih => intro e; cases s <;> exact ih _
        exact aux steps env0
      exact hnext sf envFinal stEnd hpcF hrunF hspF hrcF hrlF
        (fun e hok => evalKExpr_congr_ok
          (hspF.trans hspecEq.1.symm) (hrcF.trans hspecEq.2.1.symm) (hrlF.trans hspecEq.2.2.symm)
          hvarsF e hok) hmF hchk

/-! ## Checked-State Extractors (`KExpr.beq`) -/

theorem eval_checked_gpr {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (r : BitVec 5) (hr : r ≠ 31#5) (eExp : KExpr)
    (heq : (stEnd.gprs.get r.toNat).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    sf.readReg64 (.gpr r) = evalKExpr envSpec eExp := by
  rw [hm.hgprs r hr, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_memA {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (idx : Nat) (eExp : KExpr)
    (heq : (stEnd.memA.get idx).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    (evalMemTree envFinal stEnd.memA).get idx = evalKExpr envSpec eExp := by
  rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_memB {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (idx : Nat) (eExp : KExpr)
    (heq : (stEnd.memB.get idx).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    (evalMemTree envFinal stEnd.memB).get idx = evalKExpr envSpec eExp := by
  rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_slot {cfg : KCfg} {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (sl : KSlot) (hsl : slotValid cfg sl = true) (eLo eHi : KExpr)
    (heqLo : (readSlot cfg stEnd sl).1.beq eLo = true)
    (heqHi : (readSlot cfg stEnd sl).2.beq eHi = true)
    (hokLo : exprVarsOk ok eLo = true) (hokHi : exprVarsOk ok eHi = true) :
    slotHolds cfg sf (evalMemTree envFinal stEnd.memA) sl
      (evalKExpr envSpec eLo) (evalKExpr envSpec eHi) := by
  have hLo : (readSlot cfg stEnd sl).1 = eLo := KExpr.beq_eq_true heqLo
  have hHi : (readSlot cfg stEnd sl).2 = eHi := KExpr.beq_eq_true heqHi
  cases sl with
  | vreg r =>
      have hr : r < 32 := by simpa [slotValid, Nat.blt_eq] using hsl
      simp only [readSlot] at hLo hHi
      have hv := hm.hvregs (BitVec.ofNat 5 r)
      rw [BitVec.toNat_ofNat, show r % 2 ^ 5 = r by omega, hLo, hHi,
        heval eLo hokLo, heval eHi hokHi] at hv
      exact ⟨hr, hv⟩
  | spillQ off =>
      simp only [slotValid, Bool.and_eq_true, Nat.ble_eq] at hsl
      simp only [readSlot] at hLo hHi
      refine ⟨by omega, ?_, ?_⟩
      · rw [evalMemTree, BTree.get_map, hLo, heval eLo hokLo]
      · rw [evalMemTree, BTree.get_map, hHi, heval eHi hokHi]
  | vregLo r =>
      have hr : r < 32 := by simpa [slotValid, Nat.blt_eq] using hsl
      simp only [readSlot] at hLo
      have hv := hm.hvregs (BitVec.ofNat 5 r)
      rw [BitVec.toNat_ofNat, show r % 2 ^ 5 = r by omega, hLo, heval eLo hokLo] at hv
      refine ⟨hr, ?_⟩
      rw [hv, truncate64_append]
  | spillD off =>
      simp only [slotValid, Bool.and_eq_true, Nat.ble_eq] at hsl
      simp only [readSlot] at hLo
      refine ⟨by omega, ?_⟩
      rw [evalMemTree, BTree.get_map, hLo, heval eLo hokLo]

theorem eval_checked_pstate {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (eL : KExpr) (rhs : BitVec 64)
    (heq : kpflagOptBeq stEnd.pstateFlag (some (.subs64 eL rhs)) = true)
    (hokL : exprVarsOk ok eL = true) :
    sf.pstate = subsPState64 (evalKExpr envSpec eL) rhs := by
  have hp := hm.hpflag
  rw [kpflagOptBeq_eq_true heq] at hp
  simpa [Seg2SymBridge.KPFlagMatches, heval eL hokL] using hp

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner
