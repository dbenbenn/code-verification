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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym

/-!
# `kyber_decapsulate` (`B06`) — Fast Symbolic 24-Round Keccak Runner

Instantiates the kernel-transparent symbolic NEON Keccak stepper and 24-round loop
verifier for `B06` (`rcBase` in `x28`, `13,979` words).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakF1600 keccakF1600Round)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600Round_getD keccakF1600Round_size keccakRunFrom keccakRunFrom_24
  keccakRunFrom_step keccakRunFrom_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  fetchWordTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  blk06NoRelocInRange fetch_blk06_range)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf (
  anf_eq_keccakRoundLane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr stepKInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KCfgValid KSpatial KStateMatches KZMatches evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval (setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym (sepWP_of_stepKInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  anfMatchesSpec btree_ext_get mkRoundEnv readSlot readSlot_holds slotHolds slotValid
  truncate64_append ushr64_truncate64_append vreg128_repack writeSlot writeSlot_preserves_matches
  writeSlotsFrom)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  btreeAll_get evalKExpr_congr_vars evalMemTree_congr_vars evalSlotsHi evalSlotsHi_getD
  evalSlotsHi_size evalSlotsLo evalSlotsLo_getD evalSlotsLo_size findSpecLane findSpecLane_sound
  mapBodyExpr mkPostLoopEnv stateVarsLt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast (
  btreeKExprBeq btreeKExprBeq_eq_true kexprPairBeq kexprPairBeq_eq optKZFlagBeq optKZFlagBeq_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep checkLoopInputs evalExprList25 evalKExpr_congr_ok exprVarsOk extendLoopVars
  progBases progBasesAux specEnvSteps validSpecVar)

/-! ## 1. Multi-Instruction Range Stepper on `B06` (`runKRange06`) -/

@[expose] def runKRange06 (cfg : KCfg) : Nat → Nat → KState → Option KState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree06 w with
      | some inst =>
          match stepKInst cfg inst st with
          | some st' => runKRange06 cfg (w + 1) n st'
          | none => none
      | none => none

theorem sepWP_of_runKRange06 [MlKemPlacement] {b tgt : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (hrLoop : env.rLoop < 24)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {st stEnd : KState} {s : State}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runKRange06 cfg w count st = some stEnd)
    (hm : KStateMatches env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → KStateMatches env stEnd sf →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt sf (KSpatial cfg env stEnd F) post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s (KSpatial cfg env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runKRange06, Option.some.injEq] at hrun_sym; subst hrun_sym
    exact hnext s (by simpa using hpc) hrun hm
  | succ n ih =>
    unfold runKRange06 at hrun_sym
    cases hfw : fetchWordTree06 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepKInst cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk06_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepKInst hv hrLoop hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          bv_omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hnext sf (by rwa [hend_eq]) h2 h3)

/-! ## 2. Round-Init Symbolic State for `B06` (`rcBase` in `x28`) -/

@[expose] def mkBaseState06 (rCnt : BitVec 5) : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)))
    gprs := ((BTree.ofFn 5 (fun g => .var (200 + g))).set 28 (.rcAdd 0#64)).set rCnt.toNat .rcLoopOff
    memA := BTree.ofFn 9 (fun i => .var (300 + i))
    memB := BTree.ofFn 9 (fun i => .var (900 + i))
    zFlag := none }

@[expose] def mkLoopInitState06 (cfg : KCfg) (rCnt : BitVec 5) (slots : List KSlot) : KState :=
  writeSlotsFrom cfg 0 slots (mkBaseState06 rCnt)

theorem mkBaseState06_matches {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s : State} {tA tB : BTree (BitVec 64) 9} {rCnt : BitVec 5}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 28#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r)) :
    let env := mkRoundEnv sp rcBase r sA sB s tA tB
    KStateMatches env (mkBaseState06 rCnt) s ∧
      evalMemTree env (mkBaseState06 rCnt).memA = tA ∧
      evalMemTree env (mkBaseState06 rCnt).memB = tB := by
  intro env
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_, ?_⟩
  · intro vr
    simp only [mkBaseState06]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
    have hlt := vr.isLt
    have h1 : ¬(100 + 2 * vr.toNat < 25) ∧ ¬(100 + 2 * vr.toNat < 50) ∧ 100 + 2 * vr.toNat < 164 :=
      ⟨by omega, by omega, by omega⟩
    have h2 : ¬(100 + 2 * vr.toNat + 1 < 25) ∧ ¬(100 + 2 * vr.toNat + 1 < 50) ∧
        100 + 2 * vr.toNat + 1 < 164 := ⟨by omega, by omega, by omega⟩
    have hd0 : (100 + 2 * vr.toNat - 100) / 2 = vr.toNat := by omega
    have hm0 : ((100 + 2 * vr.toNat - 100) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
    have hd1 : (100 + 2 * vr.toNat + 1 - 100) / 2 = vr.toNat := by omega
    have hm1 : ((100 + 2 * vr.toNat + 1 - 100) % 2 == 0) = false := beq_false_of_ne (by omega)
    simp only [evalKExpr, env, mkRoundEnv, h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte,
      hd0, hm0, hd1, hm1, Bool.false_eq_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g _hg31
    simp only [mkBaseState06]; rw [BTree.get_set _ rCnt.toNat _ rCnt.isLt g.toNat g.isLt]
    by_cases hgc : g.toNat = rCnt.toNat
    · have heq := BitVec.eq_of_toNat_eq hgc; subst heq; simp [evalKExpr, env, mkRoundEnv, hcnt]
    · simp only [hgc, ↓reduceIte]; rw [BTree.get_set _ 28 _ (by decide) g.toNat g.isLt]
      by_cases hg28 : g.toNat = 28
      · have heq : g = 28#5 := BitVec.eq_of_toNat_eq hg28
        subst heq; simp [evalKExpr, env, mkRoundEnv, hrc]
      · simp only [hg28, ↓reduceIte]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
        have hlt := g.isLt
        have hb : ¬(200 + g.toNat < 25) ∧ ¬(200 + g.toNat < 50) ∧ ¬(200 + g.toNat < 164) ∧
            200 + g.toNat < 232 ∧ 200 + g.toNat - 200 = g.toNat :=
          ⟨by omega, by omega, by omega, by omega, by omega⟩
        simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [evalMemTree, mkBaseState06]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
        300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [evalMemTree, mkBaseState06]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(900 + i < 25) ∧ ¬(900 + i < 50) ∧ ¬(900 + i < 164) ∧ ¬(900 + i < 232) ∧
        ¬(900 + i < 812) ∧ 900 + i < 1412 ∧ 900 + i - 900 = i :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2.1, hb.2.2.2.2.2.2]

private theorem writeSlotsFrom06_matches {cfg : KCfg} {env : KEnv}
    {sA sB : KeccakState} {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hv0 : ∀ k, k < 25 → evalKExpr env (.var k) = sA.getD k 0#64)
    (hv25 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = sB.getD k 0#64)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length = 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (sA.getD (k + j) 0#64) (sB.getD (k + j) 0#64)) →
      KStateMatches env st s → evalMemTree env st.memA = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsFrom cfg k rem st) s ∧
        evalMemTree env (writeSlotsFrom cfg k rem st).memA = tA ∧
        (writeSlotsFrom cfg k rem st).memB = mB0 := by
  induction rem with
  | nil => intro _ _ _ _ hm htA hmB; exact ⟨hm, htA, hmB⟩
  | cons sl rest ih =>
      intro k st hsum hsl hm htA hmB
      have hk25 : k < 25 := by simp at hsum; omega
      have hsl0 : slotHolds cfg s tA sl (evalKExpr env (.var k)) (evalKExpr env (.var (25 + k))) := by
        rw [hv0 k hk25, hv25 k hk25]; simpa using hsl 0 (by simp)
      rcases writeSlot_preserves_matches (p := (.var k, .var (25 + k))) hm htA hsl0
        with ⟨hm1, htA1, hmB1⟩
      simp only [writeSlotsFrom]
      exact ih (k + 1) (writeSlot cfg st sl (.var k, .var (25 + k))) (by simp at hsum ⊢; omega)
        (fun j hj => by
          have hj' := hsl (j + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj')
        hm1 htA1 (hmB1.trans hmB)

theorem mkLoopInitState06_matches {cfg : KCfg} {sp rcBase : BitVec 64} {r : Nat}
    {sA sB : KeccakState} {s : State} {tA tB : BTree (BitVec 64) 9}
    {rCnt : BitVec 5} {slots : List KSlot}
    (hlen : slots.length = 25) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 28#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r))
    (hslots : ∀ idx, idx < 25 →
      slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) :
    KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState06 cfg rCnt slots) s ∧
      evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState06 cfg rCnt slots).memA = tA ∧
      evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState06 cfg rCnt slots).memB = tB ∧
      (mkLoopInitState06 cfg rCnt slots).memB = (mkBaseState06 rCnt).memB := by
  rcases mkBaseState06_matches (sA := sA) (sB := sB) (tA := tA) (tB := tB)
    hsp hspA hrc hcnt with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var k) = sA.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, mkRoundEnv, hk]
  have hv25 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var (25 + k)) = sB.getD k 0#64 :=
    fun k hk => by
      simp [evalKExpr, mkRoundEnv, show ¬(25 + k < 25) by omega,
        show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  rcases writeSlotsFrom06_matches (cfg := cfg) hv0 hv25 slots 0 (mkBaseState06 rCnt) (by omega)
    (fun j hj => by simpa using hslots j (by omega)) hm0 htA0 rfl with ⟨hmF, htAF, hmBF⟩
  unfold mkLoopInitState06
  exact ⟨hmF, htAF, by rw [hmBF, htB0], hmBF⟩

/-! ## 3. Fast 24-Round Loop Verifier (`checkKeccakLoop06`) & Soundness -/

private theorem roundEnv_preserved_gpr06 {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s sm : State} {tA tB : BTree (BitVec 64) 9} {stB : KState}
    (hmB : KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) stB sm)
    {g : BitVec 5} (hg31 : g ≠ 31#5) (hgVar : stB.gprs.get g.toNat = .var (200 + g.toNat)) :
    sm.readReg64 (.gpr g) = s.readReg64 (.gpr g) := by
  have h := hmB.hgprs g hg31; rw [hgVar] at h; have hlt := g.isLt
  have hb : ¬(200 + g.toNat < 25) ∧ ¬(200 + g.toNat < 50) ∧ ¬(200 + g.toNat < 164) ∧
      200 + g.toNat < 232 ∧ 200 + g.toNat - 200 = g.toNat :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  simpa [evalKExpr, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2] using h

private theorem roundEnv_preserved_vreg06 {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s sm : State} {tA tB : BTree (BitVec 64) 9} {stB : KState}
    (hmB : KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) stB sm) {vr : BitVec 5}
    (hvrVar : stB.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1))) :
    sm.readVReg128 vr = s.readVReg128 vr := by
  have h := hmB.hvregs vr; rw [hvrVar] at h; have hlt := vr.isLt
  have h1 : ¬(100 + 2 * vr.toNat < 25) ∧ ¬(100 + 2 * vr.toNat < 50) ∧ 100 + 2 * vr.toNat < 164 :=
    ⟨by omega, by omega, by omega⟩
  have h2 : ¬(100 + 2 * vr.toNat + 1 < 25) ∧ ¬(100 + 2 * vr.toNat + 1 < 50) ∧
      100 + 2 * vr.toNat + 1 < 164 := ⟨by omega, by omega, by omega⟩
  have hd0 : (100 + 2 * vr.toNat - 100) / 2 = vr.toNat := by omega
  have hm0 : ((100 + 2 * vr.toNat - 100) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
  have hd1 : (100 + 2 * vr.toNat + 1 - 100) / 2 = vr.toNat := by omega
  have hm1 : ((100 + 2 * vr.toNat + 1 - 100) % 2 == 0) = false := beq_false_of_ne (by omega)
  simp only [evalKExpr, mkRoundEnv, h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte,
    hd0, hm0, hd1, hm1, Bool.false_eq_true, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h.trans (vreg128_repack (s.readVReg128 vr))

private theorem roundEnv_preserved_memA06 (sp rcBase : BitVec 64) (r : Nat) (sA sB : KeccakState)
    (s : State) (tA tB : BTree (BitVec 64) 9) {stB : KState} {i : Nat} (hi : i < 512)
    (hmemVar : stB.memA.get i = .var (300 + i)) :
    (evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) stB.memA).get i = tA.get i := by
  rw [evalMemTree, BTree.get_map, hmemVar]
  have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
      300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp [evalKExpr, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]

@[expose] def checkKeccakLoop06 (cfg : KCfg) (wHead nBody : Nat)
    (rCnt : BitVec 5) (slots : List KSlot) : Option KState :=
  if Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 28#5) && (rCnt != 31#5) &&
     blk06NoRelocInRange wHead (wHead + nBody + 1) &&
     Nat.ble (wHead + nBody + 1) 13979 then
    match fetchWordTree06 (wHead + nBody) with
    | some (.bCond cond disp) =>
        if cond == .NE && disp == 0#64 - BitVec.ofNat 64 (4 * nBody) then
          match runKRange06 cfg wHead nBody (mkLoopInitState06 cfg rCnt slots) with
          | none => none
          | some stBody =>
              if optKZFlagBeq stBody.zFlag (some .loopDone) &&
                 (stBody.gprs.get rCnt.toNat).beq .rcLoopNext &&
                 (stBody.gprs.get 28).beq (.rcAdd 0#64) &&
                 btreeKExprBeq stBody.memB (mkBaseState06 rCnt).memB &&
                 (List.range 25).all (fun idx =>
                   let (eLo, eHi) := readSlot cfg stBody (slots.getD idx (.vreg 0))
                   anfMatchesSpec eLo 0 idx && anfMatchesSpec eHi 25 idx)
              then some stBody
              else none
        else none
    | _ => none
  else none

private theorem loop_done_false_of_lt23 {r : Nat} (hr : r < 23) :
    (BitVec.ofNat 64 (8 * r) + 8#64 == 192#64) = false := by
  apply beq_false_of_ne
  intro h
  have h1 : (BitVec.ofNat 64 (8 * r) + 8#64).toNat = (192#64 : BitVec 64).toNat :=
    congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private theorem loop_done_true_23 :
    (BitVec.ofNat 64 (8 * 23) + 8#64 == 192#64) = true := by decide

theorem sepWP_of_keccakLoop24_06 [MlKemPlacement] {b tgt sp rcBase : BitVec 64}
    {cfg : KCfg} (hv : KCfgValid cfg)
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {stBody : KState}
    (hchk : checkKeccakLoop06 cfg wHead nBody rCnt slots = some stBody)
    {sA0 sB0 : KeccakState} (hsA0 : sA0.size = 25) (hsB0 : sB0.size = 25)
    {s0 : State} {tA0 tB0 : BTree (BitVec 64) 9} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wHead)) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hrc0 : s0.readReg64 (.gpr 28#5) = rcBase)
    (hcnt0 : s0.readReg64 (.gpr rCnt) = 0#64)
    (hslots0 : ∀ idx, idx < 25 →
      slotHolds cfg s0 tA0 (slots.getD idx (.vreg 0)) (sA0.getD idx 0#64) (sB0.getD idx 0#64))
    (hnext : ∀ (sf : State) (env23 : KEnv),
      sf.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) →
      sf.status = .Running →
      sf.sp = sp → sf.spAligned = true →
      sf.readReg64 (.gpr 28#5) = rcBase →
      sf.readReg64 (.gpr rCnt) = 192#64 →
      ConditionHolds .EQ sf.pstate = true →
      ConditionHolds .NE sf.pstate = false →
      (∀ g : BitVec 5, g ≠ 31#5 → stBody.gprs.get g.toNat = .var (200 + g.toNat) →
        sf.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
      (∀ vr : BitVec 5,
        stBody.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) →
        sf.readVReg128 vr = s0.readVReg128 vr) →
      (∀ i, i < 512 → stBody.memA.get i = .var (300 + i) →
        (evalMemTree env23 stBody.memA).get i = tA0.get i) →
      (∀ e idx, idx < 25 → anfMatchesSpec e 0 idx = true →
        evalKExpr env23 e = (keccakF1600 sA0).getD idx 0#64) →
      (∀ e idx, idx < 25 → anfMatchesSpec e 25 idx = true →
        evalKExpr env23 e = (keccakF1600 sB0).getD idx 0#64) →
      KStateMatches env23 stBody sf →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt sf
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env23 stBody.memA) ∗
            (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗
        (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA0 ∗
          (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) post oom := by
  unfold checkKeccakLoop06 at hchk
  split at hchk
  case isFalse => cases hchk
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨hlen, hslVal⟩, _hne28⟩, hne31⟩, hnr⟩, hmax⟩
  cases hfw : fetchWordTree06 (wHead + nBody) with
  | none => simp [hfw] at hchk
  | some inst =>
      simp only [hfw] at hchk
      cases inst <;> dsimp only at hchk <;> try cases hchk
      rename_i cond disp
      split at hchk
      case isFalse => cases hchk
      case isTrue hbr =>
      simp only [Bool.and_eq_true] at hbr
      rcases hbr with ⟨hcondB, hdispB⟩
      cases cond <;> try cases hcondB
      have hdisp : disp = 0#64 - BitVec.ofNat 64 (4 * nBody) := beq_iff_eq.mp hdispB
      cases hrunB : runKRange06 cfg wHead nBody (mkLoopInitState06 cfg rCnt slots) with
      | none => simp [hrunB] at hchk
      | some stB =>
          simp only [hrunB] at hchk
          split at hchk
          case isFalse => cases hchk
          case isTrue hpost =>
          simp only [Option.some.injEq] at hchk; subst hchk
          simp only [Bool.and_eq_true] at hpost
          rcases hpost with ⟨⟨⟨⟨hzfB, hcntB⟩, hrcB⟩, hmemBB⟩, hanfB⟩
          have hzf : stB.zFlag = some .loopDone := beq_iff_eq.mp (optKZFlagBeq_eq _ _ ▸ hzfB)
          have hcntNext : stB.gprs.get rCnt.toNat = .rcLoopNext := KExpr.beq_eq_true hcntB
          have hrcNext : stB.gprs.get 28 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
          have hmemBEq : stB.memB = (mkBaseState06 rCnt).memB := btreeKExprBeq_eq_true hmemBB
          have hslValIdx : ∀ idx, idx < 25 →
              slotValid cfg (slots.getD idx (.vreg 0)) = true := fun idx hidx => by
            have hlt : idx < slots.length := by omega
            simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
            exact List.all_eq_true.mp hslVal _ (List.getElem_mem hlt)
          have hanfIdx : ∀ idx, idx < 25 →
              anfMatchesSpec (readSlot cfg stB (slots.getD idx (.vreg 0))).1 0 idx = true ∧
                anfMatchesSpec (readSlot cfg stB (slots.getD idx (.vreg 0))).2 25 idx = true :=
            fun idx hidx => by
              simpa [Bool.and_eq_true] using List.all_eq_true.mp hanfB idx (List.mem_range.mpr hidx)
          suffices ∀ (rem r : Nat) (sA sB : KeccakState) (s : State) (tA : BTree (BitVec 64) 9),
              r + (rem + 1) = 24 → sA.size = 25 → sB.size = 25 →
              keccakRunFrom r sA = keccakF1600 sA0 → keccakRunFrom r sB = keccakF1600 sB0 →
              s.pc = b + BitVec.ofNat 64 (4 * wHead) → s.status = .Running →
              s.sp = sp → s.spAligned = true →
              s.readReg64 (.gpr 28#5) = rcBase →
              s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r) →
              (∀ idx, idx < 25 →
                slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) →
              (∀ g : BitVec 5, g ≠ 31#5 → stB.gprs.get g.toNat = .var (200 + g.toNat) →
                s.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
              (∀ vr : BitVec 5,
                stB.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) →
                s.readVReg128 vr = s0.readVReg128 vr) →
              (∀ i, i < 512 → stB.memA.get i = .var (300 + i) → tA.get i = tA0.get i) →
              SepWP (blkPC06.rebase b (fun _ => none)) tgt s
                ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                  (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                    (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) post oom by
            exact this 23 0 sA0 sB0 s0 tA0 rfl hsA0 hsB0 (keccakRunFrom_zero sA0)
              (keccakRunFrom_zero sB0) hpc0 hrun0 hsp0 hspA0 hrc0 hcnt0 hslots0
              (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
          intro rem
          induction rem with
          | zero =>
              intro r sA sB s tA hrSum _hsA _hsB hrunA hrunB_st hpc hrun hsp hspA hrc hcnt
                hslots hgprP hvregP hmemAP
              have hr23 : r = 23 := by omega
              subst hr23
              let env23 := mkRoundEnv sp rcBase 23 sA sB s tA tB0
              rcases mkLoopInitState06_matches (tB := tB0) hlen hsp hspA hrc hcnt hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg env23 (mkLoopInitState06 cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                    (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                      (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [env23, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_of_runKRange06 hv (by simp [env23, mkRoundEnv]) nBody wHead hnr hmax
                (Nat.le_refl _) (by omega) hrunB hmI hpc hrun ?_
              intro sm hmpc hmrun hmB
              have htBB : evalMemTree env23 stB.memB = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk06_range (b := b) hnr hmax (by omega) (by omega) hfw
              have hzEq : ConditionHolds .EQ sm.pstate = true ∧
                  ConditionHolds .NE sm.pstate = false := by
                have hz := hmB.hzflag; rw [hzf] at hz
                simpa [KZMatches, env23, mkRoundEnv, loop_done_true_23] using hz
              refine SepWP.step_pure hmpc hmrun hfetchBr (s' := sm.advancePC) ?_ rfl ?_
              · rw [setPC_self hmpc]; simp [Program.evalInst, execInstWithSvc, hzEq.2]
              · have hpcEnd : sm.advancePC.pc =
                    b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) := by
                  simp only [State.advancePC, hmpc]; bv_omega
                have hspEnd : KSpatial cfg env23 stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                      (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env23 stB.memA) ∗
                        (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [env23, mkRoundEnv]
                rw [hspEnd]
                have hA23 : keccakF1600Round sA (keccakRcAt 23) = keccakF1600 sA0 := by
                  rwa [keccakRunFrom_step 23 (by decide) sA, keccakRunFrom_24] at hrunA
                have hB23 : keccakF1600Round sB (keccakRcAt 23) = keccakF1600 sB0 := by
                  rwa [keccakRunFrom_step 23 (by decide) sB, keccakRunFrom_24] at hrunB_st
                refine hnext sm.advancePC env23 hpcEnd hmrun hmB.hsp hmB.hsp_al ?_ ?_
                  hzEq.1 hzEq.2
                  (fun g hg31 hgv => (roundEnv_preserved_gpr06 hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg06 hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv =>
                    (roundEnv_preserved_memA06 sp rcBase 23 sA sB s tA tB0 hi hmv).trans (hmemAP i hi hmv))
                  ?_ ?_ ⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hzflag⟩
                · have h := hmB.hgprs 28#5 (by decide)
                  change _ = evalKExpr env23 (stB.gprs.get 28) at h
                  rw [hrcNext] at h; simpa [evalKExpr, env23, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hne31
                  rw [hcntNext] at h; simpa [evalKExpr, env23, mkRoundEnv] using h
                · intro e idx hidx hanfE
                  have hv0 : ∀ j, j < 25 → env23.vars (0 + j) = sA.getD j 0#64 :=
                    fun j hj => by simp [env23, mkRoundEnv, hj]
                  rw [anf_eq_keccakRoundLane hv0 hanfE, ← hA23]
                  exact (keccakF1600Round_getD sA (keccakRcAt 23) hidx).symm
                · intro e idx hidx hanfE
                  have hv25 : ∀ j, j < 25 → env23.vars (25 + j) = sB.getD j 0#64 := fun j hj => by
                    simp [env23, mkRoundEnv, show ¬(25 + j < 25) by omega,
                      show 25 + j < 50 by omega, show 25 + j - 25 = j by omega]
                  rw [anf_eq_keccakRoundLane hv25 hanfE, ← hB23]
                  exact (keccakF1600Round_getD sB (keccakRcAt 23) hidx).symm
          | succ rem' ih =>
              intro r sA sB s tA hrSum _hsA _hsB hrunA hrunB_st hpc hrun hsp hspA hrc hcnt
                hslots hgprP hvregP hmemAP
              have hrLt23 : r < 23 := by omega
              let envR := mkRoundEnv sp rcBase r sA sB s tA tB0
              rcases mkLoopInitState06_matches (tB := tB0) hlen hsp hspA hrc hcnt hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg envR (mkLoopInitState06 cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                    (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                      (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [envR, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_of_runKRange06 hv (by simp [envR, mkRoundEnv]; omega) nBody wHead hnr hmax
                (Nat.le_refl _) (by omega) hrunB hmI hpc hrun ?_
              intro sm hmpc hmrun hmB
              have htBB : evalMemTree envR stB.memB = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk06_range (b := b) hnr hmax (by omega) (by omega) hfw
              have hzNe : ConditionHolds .NE sm.pstate = true := by
                have hz := hmB.hzflag; rw [hzf] at hz
                simpa [KZMatches, envR, mkRoundEnv, loop_done_false_of_lt23 hrLt23] using hz.2
              have hpcBack : sm.pc + disp = b + BitVec.ofNat 64 (4 * wHead) := by
                rw [hmpc, hdisp]; bv_omega
              refine SepWP.step_pure hmpc hmrun hfetchBr
                (s' := sm.setPC (b + BitVec.ofNat 64 (4 * wHead))) ?_ rfl ?_
              · rw [setPC_self hmpc]
                simp only [Program.evalInst, execInstWithSvc, hzNe, ↓reduceIte]
                rw [hpcBack]
              · have hspNext : KSpatial cfg envR stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                      (BTreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree envR stB.memA) ∗
                        (BTreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F))) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [envR, mkRoundEnv]
                rw [hspNext]
                let sA' := keccakF1600Round sA (keccakRcAt r)
                let sB' := keccakF1600Round sB (keccakRcAt r)
                refine ih (r + 1) sA' sB' (sm.setPC (b + BitVec.ofNat 64 (4 * wHead)))
                  (evalMemTree envR stB.memA) (by omega)
                  (keccakF1600Round_size sA _) (keccakF1600Round_size sB _)
                  (by rwa [keccakRunFrom_step r (by omega) sA] at hrunA)
                  (by rwa [keccakRunFrom_step r (by omega) sB] at hrunB_st)
                  rfl hmrun hmB.hsp hmB.hsp_al ?_ ?_ ?_
                  (fun g hg31 hgv => (roundEnv_preserved_gpr06 hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg06 hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv =>
                    (roundEnv_preserved_memA06 sp rcBase r sA sB s tA tB0 hi hmv).trans (hmemAP i hi hmv))
                · have h := hmB.hgprs 28#5 (by decide)
                  change _ = evalKExpr envR (stB.gprs.get 28) at h
                  rw [hrcNext] at h; simpa [evalKExpr, envR, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hne31
                  rw [hcntNext] at h
                  change sm.readReg64 (.gpr rCnt) = _
                  rw [h]; simp only [evalKExpr, envR, mkRoundEnv]; bv_omega
                · intro idx hidx
                  have hsl := readSlot_holds (hslValIdx idx hidx)
                    (⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hzflag⟩ :
                      KStateMatches envR stB (sm.setPC (b + BitVec.ofNat 64 (4 * wHead))))
                  rcases hanfIdx idx hidx with ⟨hLoAnf, hHiAnf⟩
                  have hv0 : ∀ j, j < 25 → envR.vars (0 + j) = sA.getD j 0#64 :=
                    fun j hj => by simp [envR, mkRoundEnv, hj]
                  have hv25 : ∀ j, j < 25 → envR.vars (25 + j) = sB.getD j 0#64 := fun j hj => by
                    simp [envR, mkRoundEnv, show ¬(25 + j < 25) by omega,
                      show 25 + j < 50 by omega, show 25 + j - 25 = j by omega]
                  have hLoEq : evalKExpr envR (readSlot cfg stB (slots.getD idx (.vreg 0))).1 =
                      sA'.getD idx 0#64 := by
                    rw [anf_eq_keccakRoundLane hv0 hLoAnf]
                    exact (keccakF1600Round_getD sA (keccakRcAt r) hidx).symm
                  have hHiEq : evalKExpr envR (readSlot cfg stB (slots.getD idx (.vreg 0))).2 =
                      sB'.getD idx 0#64 := by
                    rw [anf_eq_keccakRoundLane hv25 hHiAnf]
                    exact (keccakF1600Round_getD sB (keccakRcAt r) hidx).symm
                  rwa [hLoEq, hHiEq] at hsl

/-! ## 4. Post-Loop Transition (`stepKLoopSym06`) & Multi-Step Runner (`runAndCheckKProg06`) -/

@[expose] def buildPostLoopState06 (baseOut : Nat) (rCnt : BitVec 5) (stPre stBody : KState) : KState :=
  { vregs := BTree.ofFn 5 (fun vr =>
      let pB := stBody.vregs.get vr
      if kexprPairBeq pB (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)) then stPre.vregs.get vr
      else
        (mapBodyExpr baseOut (baseOut + 50 + 2 * vr) pB.1,
         mapBodyExpr baseOut (baseOut + 50 + 2 * vr + 1) pB.2))
    gprs := BTree.ofFn 5 (fun g =>
      if Nat.beq g 28 then .rcAdd 0#64
      else if Nat.beq g rCnt.toNat then .const64 192#64
      else if (stBody.gprs.get g).beq (.var (200 + g)) then stPre.gprs.get g
      else .var (baseOut + 114 + g))
    memA := BTree.ofFn 9 (fun i =>
      let eB := stBody.memA.get i
      if eB.beq (.var (300 + i)) then stPre.memA.get i
      else mapBodyExpr baseOut (baseOut + 146 + i) eB)
    memB := stPre.memB
    zFlag := some (.constBool true) }

@[expose] def stepKLoopSym06 (cfg : KCfg) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) : Option KState :=
  if Nat.ble 100 baseOut && stateVarsLt baseOut stPre &&
     Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 31#5) &&
     (stPre.gprs.get 28).beq (.rcAdd 0#64) &&
     (stPre.gprs.get rCnt.toNat).beq (.const64 0#64) then
    match checkKeccakLoop06 cfg wHead nBody rCnt slots with
    | none => none
    | some stBody => some (buildPostLoopState06 baseOut rCnt stPre stBody)
  else none

private theorem eval_mapBodyExpr06 {env0 env23 : KEnv} {baseOut fallbackId : Nat}
    {sA sB : KeccakState} {sf : State} {tA : BTree (BitVec 64) 9} {e : KExpr}
    (hA : ∀ idx, idx < 25 → anfMatchesSpec e 0 idx = true → evalKExpr env23 e = sA.getD idx 0#64)
    (hB : ∀ idx, idx < 25 → anfMatchesSpec e 25 idx = true → evalKExpr env23 e = sB.getD idx 0#64)
    (hfb : (mkPostLoopEnv env0 baseOut sA sB sf tA).vars fallbackId = evalKExpr env23 e) :
    evalKExpr (mkPostLoopEnv env0 baseOut sA sB sf tA) (mapBodyExpr baseOut fallbackId e) =
      evalKExpr env23 e := by
  unfold mapBodyExpr
  cases h0 : findSpecLane e 0 with
  | some idx =>
      rcases findSpecLane_sound h0 with ⟨hi, hm⟩
      rw [hA idx hi hm]
      simp [evalKExpr, mkPostLoopEnv, show ¬(baseOut + idx < baseOut) by omega,
        show baseOut + idx < baseOut + 25 by omega, show baseOut + idx - baseOut = idx by omega]
  | none =>
      cases h25 : findSpecLane e 25 with
      | some idx =>
          rcases findSpecLane_sound h25 with ⟨hi, hm⟩
          rw [hB idx hi hm]
          simp [evalKExpr, mkPostLoopEnv, show ¬(baseOut + 25 + idx < baseOut) by omega,
            show ¬(baseOut + 25 + idx < baseOut + 25) by omega,
            show baseOut + 25 + idx < baseOut + 50 by omega,
            show baseOut + 25 + idx - (baseOut + 25) = idx by omega]
      | none => exact hfb

theorem sepWP_of_stepKLoop06 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgValid cfg) {env0 : KEnv}
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {baseOut : Nat}
    {stPre stPost : KState}
    (hstep : stepKLoopSym06 cfg wHead nBody rCnt slots baseOut stPre = some stPost)
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hm0 : KStateMatches env0 stPre s0)
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wHead)) (hrun0 : s0.status = .Running)
    (hnext : ∀ (sf : State) (envPost : KEnv),
      sf.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) →
      sf.status = .Running →
      envPost.sp = env0.sp → envPost.rcBase = env0.rcBase → envPost.rLoop = env0.rLoop →
      (∀ id, id < baseOut → envPost.vars id = env0.vars id) →
      (∀ idx, idx < 25 →
        envPost.vars (baseOut + idx) = (keccakF1600 (evalSlotsLo cfg env0 stPre slots)).getD idx 0#64) →
      (∀ idx, idx < 25 →
        envPost.vars (baseOut + 25 + idx) =
          (keccakF1600 (evalSlotsHi cfg env0 stPre slots)).getD idx 0#64) →
      KStateMatches envPost stPost sf →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt sf (KSpatial cfg envPost stPost F) post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 stPre F) post oom := by
  unfold stepKLoopSym06 at hstep
  split at hstep
  case isFalse => cases hstep
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨⟨_hb100, hsvPre⟩, hlen⟩, hslVal⟩, hne31⟩, hrcB⟩, hcntB⟩
  have hrcExpr : stPre.gprs.get 28 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
  have hcntExpr : stPre.gprs.get rCnt.toNat = .const64 0#64 := KExpr.beq_eq_true hcntB
  simp only [stateVarsLt, Bool.and_eq_true] at hsvPre
  rcases hsvPre with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hchk : checkKeccakLoop06 cfg wHead nBody rCnt slots with
  | none => simp [hchk] at hstep
  | some stBody =>
      simp only [hchk, Option.some.injEq] at hstep; subst hstep
      let sA0 := evalSlotsLo cfg env0 stPre slots
      let sB0 := evalSlotsHi cfg env0 stPre slots
      have hrc0 : s0.readReg64 (.gpr 28#5) = env0.rcBase := by
        have h := hm0.hgprs 28#5 (by decide)
        change _ = evalKExpr env0 (stPre.gprs.get 28) at h
        rw [hrcExpr] at h; simpa [evalKExpr] using h
      have hcnt0 : s0.readReg64 (.gpr rCnt) = 0#64 := by
        have h := hm0.hgprs rCnt hne31
        rw [hcntExpr] at h; simpa [evalKExpr] using h
      have hslots0 : ∀ idx, idx < 25 →
          slotHolds cfg s0 (evalMemTree env0 stPre.memA) (slots.getD idx (.vreg 0))
            (sA0.getD idx 0#64) (sB0.getD idx 0#64) := fun idx hidx => by
        have hlt : idx < slots.length := by omega
        have hsv : slotValid cfg (slots.getD idx (.vreg 0)) = true := by
          simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          exact List.all_eq_true.mp hslVal _ (List.getElem_mem hlt)
        rw [evalSlotsLo_getD _ _ _ _ hidx, evalSlotsHi_getD _ _ _ _ hidx]
        exact readSlot_holds hsv hm0
      dsimp only [KSpatial]
      refine sepWP_of_keccakLoop24_06 (sA0 := sA0) (sB0 := sB0)
        (tA0 := evalMemTree env0 stPre.memA) (tB0 := evalMemTree env0 stPre.memB)
        hv hchk (evalSlotsLo_size _ _ _ _) (evalSlotsHi_size _ _ _ _)
        hpc0 hrun0 hm0.hsp hm0.hsp_al hrc0 hcnt0 hslots0 ?_
      intro sf env23 hpcf hrunf hspf hspAf hrcf hcntf hzfEq hzfNe
        hgprP hvregP hmemAP hA23 hB23 hm23
      let tAPost := evalMemTree env23 stBody.memA
      let envP := mkPostLoopEnv env0 baseOut (keccakF1600 sA0) (keccakF1600 sB0) sf tAPost
      have hvarsP : ∀ id, id < baseOut → envP.vars id = env0.vars id :=
        fun id hid => by simp [envP, mkPostLoopEnv, hid]
      have htAPEq : evalMemTree envP
          (BTree.ofFn 9 fun i =>
            let eB := stBody.memA.get i
            if eB.beq (.var (300 + i)) then stPre.memA.get i
            else mapBodyExpr baseOut (baseOut + 146 + i) eB) = tAPost := by
        apply btree_ext_get; intro i hi
        simp only [evalMemTree, BTree.get_map]
        rw [BTree.get_ofFn 9 _ i hi]
        by_cases heq : (stBody.memA.get i).beq (.var (300 + i)) = true
        · simp only [heq, ↓reduceIte]
          have hv := hmemAP i hi (KExpr.beq_eq_true heq)
          have hcongr := evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP
            (stPre.memA.get i) (btreeAll_get _ stPre.memA hmAPre i hi)
          rw [hcongr]; simpa [tAPost, evalMemTree, BTree.get_map] using hv.symm
        · have heqF : (stBody.memA.get i).beq (.var (300 + i)) = false := Bool.eq_false_iff.mpr heq
          simp only [heqF, Bool.false_eq_true, ↓reduceIte]
          have hfb : envP.vars (baseOut + 146 + i) = evalKExpr env23 (stBody.memA.get i) := by
            change i < 512 at hi
            simp [envP, mkPostLoopEnv, tAPost, evalMemTree, BTree.get_map,
              show ¬(baseOut + 146 + i < baseOut) by omega,
              show ¬(baseOut + 146 + i < baseOut + 25) by omega,
              show ¬(baseOut + 146 + i < baseOut + 50) by omega,
              show ¬(baseOut + 146 + i < baseOut + 114) by omega,
              show ¬(baseOut + 146 + i < baseOut + 146) by omega,
              show baseOut + 146 + i < baseOut + 658 by omega,
              show baseOut + 146 + i - (baseOut + 146) = i by omega]
          exact (eval_mapBodyExpr06 (fun idx hi hm => hA23 _ idx hi hm)
            (fun idx hi hm => hB23 _ idx hi hm) hfb).trans
            (BTree.get_map (evalKExpr env23) stBody.memA i).symm
      have htBPEq : evalMemTree envP stPre.memB = evalMemTree env0 stPre.memB :=
        evalMemTree_congr_vars hmBPre rfl rfl rfl hvarsP
      have hmP : KStateMatches envP (buildPostLoopState06 baseOut rCnt stPre stBody) sf := by
        refine ⟨hspf, hspAf, ?_, ?_, ⟨hzfEq, by simp [hzfNe]⟩⟩
        · intro vr
          have hlt := vr.isLt
          dsimp only [buildPostLoopState06]
          rw [BTree.get_ofFn 5 _ vr.toNat hlt]
          by_cases heq : kexprPairBeq (stBody.vregs.get vr.toNat)
              (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) = true
          · simp only [heq, ↓reduceIte]
            have heq' : stBody.vregs.get vr.toNat =
                (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) :=
              beq_iff_eq.mp (kexprPairBeq_eq _ _ ▸ heq)
            rw [hvregP vr heq', hm0.hvregs vr]
            have hpv := btreeAll_get _ stPre.vregs hvPre vr.toNat hlt
            simp only [Bool.and_eq_true] at hpv
            rw [evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _ hpv.2,
              evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _ hpv.1]
          · have heqF := Bool.eq_false_iff.mpr heq
            simp only [heqF, Bool.false_eq_true, ↓reduceIte]
            have hv23 := hm23.hvregs vr
            have hfbLo : envP.vars (baseOut + 50 + 2 * vr.toNat) =
                evalKExpr env23 (stBody.vregs.get vr.toNat).1 := by
              have hpar : (2 * vr.toNat % 2 == 0) = true := beq_iff_eq.mpr (by omega)
              simp only [envP, mkPostLoopEnv, show ¬(baseOut + 50 + 2 * vr.toNat < baseOut) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat < baseOut + 25) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat < baseOut + 50) by omega,
                show baseOut + 50 + 2 * vr.toNat < baseOut + 114 by omega, ↓reduceIte,
                show baseOut + 50 + 2 * vr.toNat - (baseOut + 50) = 2 * vr.toNat by omega,
                show 2 * vr.toNat / 2 = vr.toNat by omega, hpar, BitVec.ofNat_toNat,
                BitVec.setWidth_eq]
              rw [hv23, truncate64_append]
            have hfbHi : envP.vars (baseOut + 50 + 2 * vr.toNat + 1) =
                evalKExpr env23 (stBody.vregs.get vr.toNat).2 := by
              have hpar : ((2 * vr.toNat + 1) % 2 == 0) = false := beq_false_of_ne (by omega)
              simp only [envP, mkPostLoopEnv,
                show ¬(baseOut + 50 + 2 * vr.toNat + 1 < baseOut) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat + 1 < baseOut + 25) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat + 1 < baseOut + 50) by omega,
                show baseOut + 50 + 2 * vr.toNat + 1 < baseOut + 114 by omega, ↓reduceIte,
                show baseOut + 50 + 2 * vr.toNat + 1 - (baseOut + 50) = 2 * vr.toNat + 1 by omega,
                show (2 * vr.toNat + 1) / 2 = vr.toNat by omega, hpar, Bool.false_eq_true,
                BitVec.ofNat_toNat, BitVec.setWidth_eq]
              rw [hv23, ushr64_truncate64_append]
            rw [eval_mapBodyExpr06 (fun idx hi hm => hA23 _ idx hi hm)
              (fun idx hi hm => hB23 _ idx hi hm) hfbHi,
              eval_mapBodyExpr06 (fun idx hi hm => hA23 _ idx hi hm)
                (fun idx hi hm => hB23 _ idx hi hm) hfbLo, ← hv23]
        · intro g hg31
          have hlt := g.isLt
          dsimp only [buildPostLoopState06]
          rw [BTree.get_ofFn 5 _ g.toNat hlt]
          by_cases hg28 : Nat.beq g.toNat 28 = true
          · simp only [hg28, ↓reduceIte, evalKExpr, envP, mkPostLoopEnv]
            have hgEq : g = 28#5 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hg28)
            subst hgEq; simpa using hrcf
          · have hg28F := Bool.eq_false_iff.mpr hg28
            simp only [hg28F, Bool.false_eq_true, ↓reduceIte]
            by_cases hgc : Nat.beq g.toNat rCnt.toNat = true
            · simp only [hgc, ↓reduceIte, evalKExpr]
              have hgEq : g = rCnt := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hgc)
              subst hgEq; exact hcntf
            · have hgcF := Bool.eq_false_iff.mpr hgc
              simp only [hgcF, Bool.false_eq_true, ↓reduceIte]
              by_cases hgVar : (stBody.gprs.get g.toNat).beq (.var (200 + g.toNat)) = true
              · simp only [hgVar, ↓reduceIte]
                rw [hgprP g hg31 (KExpr.beq_eq_true hgVar), hm0.hgprs g hg31]
                exact (evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _
                  (btreeAll_get _ stPre.gprs hgPre g.toNat hlt)).symm
              · have hgVarF := Bool.eq_false_iff.mpr hgVar
                simp only [hgVarF, Bool.false_eq_true, ↓reduceIte]
                simp [evalKExpr, envP, mkPostLoopEnv,
                  show ¬(baseOut + 114 + g.toNat < baseOut) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 25) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 50) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 114) by omega,
                  show baseOut + 114 + g.toNat < baseOut + 146 by omega,
                  show baseOut + 114 + g.toNat - (baseOut + 114) = g.toNat by omega]
      have hspOut : KSpatial cfg envP (buildPostLoopState06 baseOut rCnt stPre stBody) F =
          ((env0.rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (env0.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tAPost ∗
              (BTreeMem (env0.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB
                (evalMemTree env0 stPre.memB) ∗ F))) := by
        dsimp only [KSpatial, buildPostLoopState06]; rw [htAPEq, htBPEq]; simp [envP, mkPostLoopEnv]
      rw [← hspOut]
      refine hnext sf envP hpcf hrunf rfl rfl rfl hvarsP ?_ ?_ hmP
      · intro idx hidx
        simp [envP, mkPostLoopEnv, sA0, show ¬(baseOut + idx < baseOut) by omega,
          show baseOut + idx < baseOut + 25 by omega, show baseOut + idx - baseOut = idx by omega]
      · intro idx hidx
        simp [envP, mkPostLoopEnv, sB0, show ¬(baseOut + 25 + idx < baseOut) by omega,
          show ¬(baseOut + 25 + idx < baseOut + 25) by omega,
          show baseOut + 25 + idx < baseOut + 50 by omega,
          show baseOut + 25 + idx - (baseOut + 25) = idx by omega]

@[expose] def runKProgSteps06 (cfg : KCfg) (wLo wHi initBnd : Nat) :
    Nat → List Nat → List KProgStep → KState → Option (Nat × List Nat × KState)
  | wCur, bases, [], st => some (wCur, bases, st)
  | wCur, bases, .range w count :: rest, st =>
      if Nat.beq wCur w && Nat.ble wLo w && Nat.ble (w + count) wHi then
        match runKRange06 cfg w count st with
        | none => none
        | some st' => runKProgSteps06 cfg wLo wHi initBnd (w + count) bases rest st'
      else none
  | wCur, bases, .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, st =>
      if Nat.beq wCur wHead && Nat.ble initBnd baseOut &&
         bases.all (fun b => Nat.ble (b + 658) baseOut) &&
         checkLoopInputs cfg (validSpecVar initBnd bases) st slots expLo expHi then
        match stepKLoopSym06 cfg wHead nBody rCnt slots baseOut st with
        | none => none
        | some st' =>
            runKProgSteps06 cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      else none

@[expose] def runAndCheckKProg06 (cfg : KCfg) (wLo wHi wStart wEnd initBnd : Nat)
    (steps : List KProgStep) (st0 : KState)
    (chk : (Nat → Bool) → KState → Bool) : Bool :=
  blk06NoRelocInRange wLo wHi && Nat.ble wHi 13979 &&
  match runKProgSteps06 cfg wLo wHi initBnd wStart [] steps st0 with
  | none => false
  | some (wFinal, finalBases, stEnd) =>
      Nat.beq wFinal wEnd && chk (validSpecVar initBnd finalBases) stEnd

private theorem validSpecVar_lt_baseOut06 {initBnd baseOut id : Nat} {bases : List Nat}
    (hinit : initBnd ≤ baseOut) (hbases : bases.all (fun b => Nat.ble (b + 658) baseOut) = true)
    (hv : validSpecVar initBnd bases id = true) : id < baseOut := by
  simp only [validSpecVar, Bool.or_eq_true, Nat.blt_eq, List.any_eq_true, Bool.and_eq_true,
    Nat.ble_eq] at hv
  rcases hv with hlt | ⟨b, hbmem, _, hlt50⟩
  · omega
  · have hb658 : b + 658 ≤ baseOut := by
      have hall := List.all_eq_true.mp hbases b hbmem
      simpa [Nat.ble_eq] using hall
    omega

private theorem sepWP_of_runKProgSteps06 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgValid cfg) {wLo wHi initBnd : Nat}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (steps : List KProgStep) (wCur wFinal : Nat) (bases finalBases : List Nat)
      (st stEnd : KState) (env envSpec : KEnv) (s0 : State),
      runKProgSteps06 cfg wLo wHi initBnd wCur bases steps st = some (wFinal, finalBases, stEnd) →
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
        SepWP (blkPC06.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) →
      SepWP (blkPC06.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env st F) post oom
  | [], wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, _, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps06, Option.some.injEq, Prod.mk.injEq] at hrun_p
      rcases hrun_p with ⟨rfl, rfl, rfl⟩
      exact hnext s0 env hpc0 hrun0 rfl hsp hrc hrl hvars hm0
  | .range w count :: rest, wCur, wFinal, bases, finalBases, st, stEnd, env, envSpec, s0,
      hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0, hnext => by
      simp only [runKProgSteps06] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨hcur, hlo⟩, hhi⟩
        subst wCur
        cases hrng : runKRange06 cfg w count st with
        | none => simp [hrng] at hrun_p
        | some st' =>
            simp only [hrng] at hrun_p
            exact sepWP_of_runKRange06 hv hrLoop count w hnr hmax hlo hhi hrng hm0 hpc0 hrun0
              (fun sf1 hpc1 hrun1 hm1 =>
                sepWP_of_runKProgSteps06 hv hnr hmax rest (w + count) wFinal bases finalBases
                  st' stEnd env envSpec sf1 hrun_p hrLoop hsp hrc hrl hvars hm1 hpc1 hrun1 hnext)
      · contradiction
  | .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, wCur, wFinal, bases, finalBases,
      st, stEnd, env, envSpec, s0, hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0,
      hnext => by
      simp only [runKProgSteps06] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨⟨hcur, hinit⟩, hbases⟩, hinp⟩
        subst wCur
        cases hstep : stepKLoopSym06 cfg wHead nBody rCnt slots baseOut st with
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
                simp only [evalSlotsLo, evalExprList25, Array.getElem_ofFn,
                  KExpr.beq_eq_true heqLo]
                exact evalKExpr_congr_ok hsp hrc hrl hvars _ hokLo
            have hslotsHi : evalSlotsHi cfg env st slots = evalExprList25 envSpec expHi := by
              apply Array.ext
              · simp [evalSlotsHi, evalExprList25]
              · intro idx h1 _
                have hidx : idx < 25 := by simpa [evalSlotsHi] using h1
                have hinpIdx := List.all_eq_true.mp hinp idx (List.mem_range.mpr hidx)
                simp only [Bool.and_eq_true] at hinpIdx
                rcases hinpIdx with ⟨⟨⟨_, heqHi⟩, _⟩, hokHi⟩
                simp only [evalSlotsHi, evalExprList25, Array.getElem_ofFn,
                  KExpr.beq_eq_true heqHi]
                exact evalKExpr_congr_ok hsp hrc hrl hvars _ hokHi
            refine sepWP_of_stepKLoop06 hv hstep hm0 hpc0 hrun0 ?_
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
                    exact absurd (validSpecVar_lt_baseOut06 hinit hbases hvOld) hltB
            exact sepWP_of_runKProgSteps06 hv hnr hmax rest (wHead + nBody + 1) wFinal
              (baseOut :: bases) finalBases st' stEnd envPost envSpec' sf1 hrun_p
              (hrlP ▸ hrLoop) (hspP.trans hsp) (hrcP.trans hrc) (hrlP.trans hrl)
              hvars' hm1 hpc1 hrun1 hnext
      · contradiction

theorem sepWP_of_runAndCheckKProg06 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgValid cfg) {env0 : KEnv} (hrLoop : env0.rLoop < 24)
    {wLo wHi wStart wEnd initBnd : Nat} {steps : List KProgStep} {st0 : KState}
    {chk : (Nat → Bool) → KState → Bool}
    (hcert : runAndCheckKProg06 cfg wLo wHi wStart wEnd initBnd steps st0 chk = true)
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
      SepWP (blkPC06.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) :
    SepWP (blkPC06.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 st0 F) post oom := by
  simp only [runAndCheckKProg06, Bool.and_eq_true, Nat.ble_eq] at hcert
  rcases hcert with ⟨⟨hnr, hmax⟩, hrest⟩
  cases hrun_p : runKProgSteps06 cfg wLo wHi initBnd wStart [] steps st0 with
  | none => simp [hrun_p] at hrest
  | some triple =>
      rcases triple with ⟨wFinal, finalBases, stEnd⟩
      simp only [hrun_p, Bool.and_eq_true, Nat.beq_eq] at hrest
      rcases hrest with ⟨rfl, hchk⟩
      refine sepWP_of_runKProgSteps06 hv hnr hmax steps wStart wFinal [] finalBases
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

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06
