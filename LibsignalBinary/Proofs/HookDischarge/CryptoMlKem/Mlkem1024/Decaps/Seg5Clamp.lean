/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 Post-Site Shuffle/Clamp Stepper

Instantiates `runClampRange06`, `sepWP_of_runClampRange06`, branch helpers (`step_b_seg5`,
`step_bCond_seg5`), and slot/register preservation extractors shared by `Seg5Init` and `Seg5Extra`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (KeccakState keccakAbsorb keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (MultiLaneSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (fetchWordTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  blk06NoRelocInRange fetch_blk06_range)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KCfgValid KSpatial KStateMatches evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval (setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get readSlot readSlot_holds slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  evalKExpr_congr_ok eval_checked_gpr exprVarsOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB (slotHolds_inj)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp (
  ClampEnvValid ClampMatches ClampState btreeMem4_eq_multiLaneSampled4 clampSelect_of_le271
  sepWP_of_stepClampInst slotHolds_congr_cfg stepClampInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowCalleeGprs06 cfgC06 cfgClamp06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA (
  calleeGprExpr06 checkCalleeGprsPreserved06 checkHeaderPreserved06 checked_calleeGprs06
  checked_headerOk06 envInitA06 eval_headerMemAExpr06 headerMemAExpr06 stInitA06 stInitA06_matches)

attribute [local irreducible] blkPC06 keccakF1600 keccakAbsorb BTreeMem

/-! ## 1. Branch Helpers & Symbolic Shuffle/Clamp Range Runner on `B06` -/

theorem step_b_seg5 [MlKemPlacement] {b tgt : BitVec 64} {wLo wHi w : Nat} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ w) (hhi : w < wHi) (hfw : fetchWordTree06 w = some (.b disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : SepWP (blkPC06.rebase b (fun _ => none)) tgt
      (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s P post oom := by
  refine SepWP.step_pure hpc hrun (fetch_blk06_range hnr hmax hlo hhi hfw)
    (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl hnext
  rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hpc]

theorem step_bCond_seg5 [MlKemPlacement] {b tgt : BitVec 64} {wLo wHi w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ w) (hhi : w < wHi) (hfw : fetchWordTree06 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk06_range hnr hmax hlo hhi hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk06_range hnr hmax hlo hhi hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]

@[expose] def runClampRange06 (cfg : KCfg) (w : Nat) : Nat → ClampState → Option ClampState
  | 0, cs => some cs
  | n + 1, cs =>
      match fetchWordTree06 w with
      | none => none
      | some inst =>
          match stepClampInst cfg inst cs with
          | none => none
          | some cs' => runClampRange06 cfg (w + 1) n cs'

theorem sepWP_of_runClampRange06 [MlKemPlacement] {b tgt : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (henv : ClampEnvValid env)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {cs csEnd : ClampState} {s : State}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runClampRange06 cfg w count cs = some csEnd)
    (hm : ClampMatches env cs s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → ClampMatches env csEnd sf →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt sf (KSpatial cfg env csEnd.st F) post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s (KSpatial cfg env cs.st F) post oom := by
  induction count generalizing w cs s with
  | zero =>
    simp only [runClampRange06, Option.some.injEq] at hrun_sym; subst hrun_sym
    exact hnext s (by simpa using hpc) hrun hm
  | succ n ih =>
    unfold runClampRange06 at hrun_sym
    cases hfw : fetchWordTree06 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepClampInst cfg inst cs with
      | none => simp [hst] at hrun_sym
      | some cs1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk06_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepClampInst hv henv hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          bv_omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hnext sf (by rwa [hend_eq]) h2 h3)

/-! ## 2. Clamp Initial State, Environment, & Post-Clamp State Extractors (`B06`) -/

@[expose] def stRawClamp06 : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs  := BTree.ofFn 5 calleeGprExpr06
    memA  := BTree.ofFn 9 headerMemAExpr06
    memB  := BTree.ofFn 9 (fun i => if i < 4 then .var (800 + i) else .const64 0#64)
    zFlag := none }

@[expose] def csInitClamp06 : ClampState := { st := stRawClamp06, cmpOpt := none }

@[expose] def envClamp06 (sp rcBase fpVal : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (s : State) (tA : BTree (BitVec 64) 9) (sampled' : Nat → Nat) : KEnv :=
  { (envInitA06 sp rcBase fpVal rho row s tA) with
    vars := fun id =>
      if id < 800 then (envInitA06 sp rcBase fpVal rho row s tA).vars id
      else if id < 804 then BitVec.ofNat 64 (sampled' (id - 800))
      else if 810 ≤ id && id < 814 then BitVec.ofNat 64 (clampSampled (sampled' (id - 810)))
      else 0#64 }

theorem envClamp06_valid {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    (hsamp : ∀ c, c < 4 → sampled' c ≤ 271) :
    ClampEnvValid (envClamp06 sp rcBase fpVal rho row s tA sampled') := by
  intro c hc
  have h1 : ¬(800 + c < 800) := by omega
  have h2 : 800 + c < 804 := by omega
  have h3 : ¬(810 + c < 800) := by omega
  have h4 : ¬(810 + c < 804) := by omega
  have h5 : (810 ≤ 810 + c && 810 + c < 814) = true := by simp; omega
  simp only [envClamp06, h1, h2, h3, h4, h5, ↓reduceIte,
    show 800 + c - 800 = c by omega, show 810 + c - 810 = c by omega]
  exact clampSelect_of_le271 (hsamp c hc)

private theorem calleeGprExpr06_lt800 :
    ∀ k : Fin 32, exprVarsOk (fun id => decide (id < 800)) (calleeGprExpr06 k.val) = true := by
  decide

private theorem headerMemAExpr06_lt800 :
    ∀ i : Fin 512, exprVarsOk (fun id => decide (id < 800)) (headerMemAExpr06 i.val) = true := by
  decide +kernel

theorem stRawClamp06_matches {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA) (F : SepProp) :
    let env := envClamp06 sp rcBase fpVal rho row s tA sampled'
    ClampMatches env csInitClamp06 s ∧
      KSpatial cfgClamp06 env csInitClamp06.st F =
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗
            (MultiLaneSampled (sp + 26320#64) 4 sampled' ∗ F))) := by
  have hsub : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (envClamp06 sp rcBase fpVal rho row s tA sampled') e =
        evalKExpr (envInitA06 sp rcBase fpVal rho row s tA) e :=
    evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid; simp [envClamp06, hid]
  have hmA0 := (stInitA06_matches hsp hspA hgprs hhdr).1
  refine ⟨⟨⟨hsp, hspA, ?_, ?_, trivial⟩, rfl, trivial⟩, ?_⟩
  · intro vr
    have hlt := vr.isLt
    have hv := hmA0.hvregs vr
    simp only [stInitA06, BTree.get_ofFn 5 _ vr.toNat hlt] at hv
    simp only [csInitClamp06, stRawClamp06, BTree.get_ofFn 5 _ vr.toNat hlt]
    rw [hsub _ (by simp [exprVarsOk]; omega), hsub _ (by simp [exprVarsOk]; omega)]
    exact hv
  · intro g hg31
    have hlt := g.isLt
    have hg := hmA0.hgprs g hg31
    simp only [stInitA06, BTree.get_ofFn 5 _ g.toNat hlt] at hg
    simp only [csInitClamp06, stRawClamp06, BTree.get_ofFn 5 _ g.toNat hlt]
    rwa [hsub _ (calleeGprExpr06_lt800 ⟨g.toNat, hlt⟩)]
  · have htA : evalMemTree (envClamp06 sp rcBase fpVal rho row s tA sampled') stRawClamp06.memA = tA := by
      apply btree_ext_get; intro i hi
      simp only [evalMemTree, stRawClamp06, BTree.get_map, BTree.get_ofFn 9 _ i hi]
      rw [hsub _ (headerMemAExpr06_lt800 ⟨i, hi⟩)]; exact eval_headerMemAExpr06 hhdr i hi
    let env := envClamp06 sp rcBase fpVal rho row s tA sampled'
    have hB (c : Nat) (hc : c < 4) :
        (evalMemTree env stRawClamp06.memB).get c = BitVec.ofNat 64 (sampled' c) := by
      simp [evalMemTree, stRawClamp06, BTree.get_map, BTree.get_ofFn 9 _ c (by omega),
        hc, evalKExpr, env, envClamp06, show ¬(800 + c < 800) by omega,
        show 800 + c < 804 by omega, show 800 + c - 800 = c by omega]
    dsimp only [KSpatial, csInitClamp06, cfgClamp06]
    rw [htA, btreeMem4_eq_multiLaneSampled4 _ (hB 0 (by decide)) (hB 1 (by decide))
      (hB 2 (by decide)) (hB 3 (by decide))]
    rfl

@[expose] def checkClampCommon06 (stEnd : KState) : Bool :=
  checkHeaderPreserved06 (fun _ => true) stEnd &&
  checkCalleeGprsPreserved06 (fun _ => true) stEnd &&
  (stEnd.gprs.get 1).beq (.var 66) &&
  (List.range 4).all fun c => (stEnd.memB.get c).beq (.var (810 + c))

@[expose] def checkSlotsMoved06 (slotsIn slotsOut : List KSlot) (stEnd : KState) : Bool :=
  (List.range 25).all fun idx =>
    let pOut := readSlot cfgClamp06 stEnd (slotsOut.getD idx (.vreg 0))
    let pIn  := readSlot cfgClamp06 stRawClamp06 (slotsIn.getD idx (.vreg 0))
    pOut.1.beq pIn.1 && pOut.2.beq pIn.2

theorem extract_clamp_common06 {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s sf : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat} {stEnd : KState} {F : SepProp}
    (hm : KStateMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') stEnd sf)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hchk : checkClampCommon06 stEnd = true) :
    let env := envClamp06 sp rcBase fpVal rho row s tA sampled'
    MemAHeaderOk06 sp rho (evalMemTree env stEnd.memA) ∧
    RowCalleeGprs06 sp rcBase fpVal row sf ∧
    sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
    KSpatial cfgClamp06 env stEnd F =
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗
        (BTreeMem (sp + 144#64) 286 (evalMemTree env stEnd.memA) ∗
          (MultiLaneSampled (sp + 26320#64) 4 (fun c => clampSampled (sampled' c)) ∗ F))) := by
  simp only [checkClampCommon06, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hhdrC, hgprC⟩, hx1C⟩, hmemBC⟩
  let env := envClamp06 sp rcBase fpVal rho row s tA sampled'
  have hokTrue : ∀ e, exprVarsOk (fun _ => true) e = true := by
    intro e; induction e <;> simp_all [exprVarsOk]
  have hhdr' : MemAHeaderOk06 sp rho (evalMemTree env stEnd.memA) :=
    checked_headerOk06 (envFinal := env) (envSpec := env) (fun _ _ => rfl) rfl
      (by simp [env, envClamp06, envInitA06]) (by simp [env, envClamp06, envInitA06])
      (by simp [env, envClamp06, envInitA06]) (by simp [env, envClamp06, envInitA06]) hhdrC
  have hgpr' : RowCalleeGprs06 sp rcBase fpVal row sf :=
    checked_calleeGprs06 (envFinal := env) (envSpec := env) hm (fun _ _ => rfl) rfl rfl
      (by simp [env, envClamp06, envInitA06]) (by simp [env, envClamp06, envInitA06]) hgprC
  have hx1' : sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) := by
    have hg1 := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 1#5 (by decide)
      (.var 66) hx1C (hokTrue _)
    simpa [Reg.x1, evalKExpr, env, envClamp06, envInitA06] using hg1.trans hx1
  have hB (c : Nat) (hc : c < 4) :
      (evalMemTree env stEnd.memB).get c = BitVec.ofNat 64 (clampSampled (sampled' c)) := by
    have heq := KExpr.beq_eq_true (List.all_eq_true.mp hmemBC c (List.mem_range.mpr hc))
    simp [evalMemTree, BTree.get_map, heq, evalKExpr, env, envClamp06,
      show ¬(810 + c < 800) by omega, show ¬(810 + c < 804) by omega,
      show 810 ≤ 810 + c by omega, show 810 + c < 814 by omega, show 810 + c - 810 = c by omega]
  refine ⟨hhdr', hgpr', hx1', ?_⟩
  dsimp only [KSpatial, cfgClamp06]
  rw [btreeMem4_eq_multiLaneSampled4 (f := fun c => clampSampled (sampled' c)) _
    (hB 0 (by decide)) (hB 1 (by decide)) (hB 2 (by decide)) (hB 3 (by decide))]
  rfl

theorem extract_slots_moved06 {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s sf : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    {slotsIn slotsOut : List KSlot} {stEnd : KState} {sLo sHi : KeccakState}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA)
    (hmEnd : KStateMatches (envClamp06 sp rcBase fpVal rho row s tA sampled') stEnd sf)
    (hvIn : slotsIn.all (slotValid cfgClamp06) = true) (hlenIn : slotsIn.length = 25)
    (hvOut : slotsOut.all (slotValid cfgClamp06) = true) (hlenOut : slotsOut.length = 25)
    (hholdsIn : ∀ idx, idx < 25 →
      slotHolds cfgC06 s tA (slotsIn.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64))
    (hchk : checkSlotsMoved06 slotsIn slotsOut stEnd = true) :
    ∀ idx, idx < 25 →
      slotHolds cfgC06 sf (evalMemTree (envClamp06 sp rcBase fpVal rho row s tA sampled') stEnd.memA)
        (slotsOut.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64) := by
  let env := envClamp06 sp rcBase fpVal rho row s tA sampled'
  have hm0 : KStateMatches env stRawClamp06 s :=
    (stRawClamp06_matches (sampled' := sampled') hsp hspA hgprs hhdr emp).1.1
  have hmE : KStateMatches env stEnd sf := hmEnd
  have htA0 : evalMemTree env stRawClamp06.memA = tA := by
    apply btree_ext_get; intro i hi
    have hsub : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
        evalKExpr env e = evalKExpr (envInitA06 sp rcBase fpVal rho row s tA) e :=
      evalKExpr_congr_ok rfl rfl rfl fun id hid => by
        simp only [decide_eq_true_eq] at hid; simp [env, envClamp06, hid]
    simp only [evalMemTree, stRawClamp06, BTree.get_map, BTree.get_ofFn 9 _ i hi]
    rw [hsub _ (headerMemAExpr06_lt800 ⟨i, hi⟩)]; exact eval_headerMemAExpr06 hhdr i hi
  intro idx hidx
  have hall := List.all_eq_true.mp hchk idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true] at hall
  have hmemIn : slotsIn.getD idx (.vreg 0) ∈ slotsIn := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hmemOut : slotsOut.getD idx (.vreg 0) ∈ slotsOut := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hrIn := readSlot_holds (List.all_eq_true.mp hvIn _ hmemIn) hm0
  rw [htA0, slotHolds_congr_cfg (cfg1 := cfgClamp06) (cfg2 := cfgC06) rfl] at hrIn
  rcases slotHolds_inj hrIn (hholdsIn idx hidx) with ⟨heLo, heHi⟩
  have hrOut := readSlot_holds (List.all_eq_true.mp hvOut _ hmemOut) hmE
  rw [KExpr.beq_eq_true hall.1, KExpr.beq_eq_true hall.2, heLo, heHi,
    slotHolds_congr_cfg (cfg1 := cfgClamp06) (cfg2 := cfgC06) rfl] at hrOut
  exact hrOut

theorem sitePreserved_row06 {cfg : RejSiteConfig} {sp rcBase fpVal pc : BitVec 64} {row : Nat}
    {s0 sF : State} {cfgS : KCfg} {tA : BTree (BitVec 64) 9}
    (hp : SitePreserved cfg s0 sF)
    (hsp : s0.sp = sp) (hspA : s0.spAligned = true)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s0)
    (hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp],
      r ∉ cfg.siteClobberedRegs) :
    let s1 := sF.setPC pc
    s1.status = .Running ∧
    s1.sp = sp ∧
    s1.spAligned = true ∧
    RowCalleeGprs06 sp rcBase fpVal row s1 ∧
    s1.readReg64 .x1 = s0.readReg64 .x1 ∧
    ∀ sl vLo vHi, slotHolds cfgS s0 tA sl vLo vHi → slotHolds cfgS s1 tA sl vLo vHi := by
  rcases hp with ⟨hrun, hspF, hvF, hgprF⟩
  rcases hgprs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h28, hfp⟩
  have hsp1 : (sF.setPC pc).sp = sp := hspF.trans hsp
  have hspA1 : (sF.setPC pc).spAligned = true := by
    unfold State.spAligned at hspA ⊢
    rwa [hsp1, ← hsp]
  have hgr (r : Reg) (hm : r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28, .fp]) :
      (sF.setPC pc).readReg64 r = s0.readReg64 r :=
    (by cases sF; cases r <;> rfl : (sF.setPC pc).readReg64 r = sF.readReg64 r).trans (hgprF r (hclob r hm))
  refine ⟨hrun, hsp1, hspA1,
    ⟨(hgr .x19 (by simp)).trans h19, (hgr .x20 (by simp)).trans h20,
     (hgr .x21 (by simp)).trans h21, (hgr .x22 (by simp)).trans h22,
     (hgr .x23 (by simp)).trans h23, (hgr .x24 (by simp)).trans h24,
     (hgr .x25 (by simp)).trans h25, (hgr .x26 (by simp)).trans h26,
     (hgr .x28 (by simp)).trans h28, (hgr .fp (by simp)).trans hfp⟩,
    hgr .x1 (by simp), fun sl vLo vHi hs => ?_⟩
  cases sl with
  | spillQ _ => exact hs
  | vreg vr =>
      have hv1 : (sF.setPC pc).readVReg128 (BitVec.ofNat 5 vr) = s0.readVReg128 (BitVec.ofNat 5 vr) := by
        cases sF; cases s0; simp [State.setPC, State.readVReg128] at hvF ⊢; rw [hvF]
      simpa [slotHolds, hv1] using hs

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Clamp
