/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep

/-!
# `decapsulate_compressed_key` (`B04`) — `Seg5` Keccak Loop & Symbolic Engine (`Seg5Loop`)

Adapts `FromSeed` symbolic Keccak infrastructure (`stepKInst`, `TreeMem`, `anf_eq_keccakRoundLane`)
to `B04` `Seg5` (`+0x40d8..+0x4368` and `+0x4390..+0x710c`, `rcBase` in `x22`) and records the
14 concrete `KSlot` tables.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakF1600 keccakF1600Round)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600Round_getD keccakF1600Round_size keccakRunFrom keccakRunFrom_24
  keccakRunFrom_step keccakRunFrom_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (fetchWordTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf (
  anf_eq_keccakRoundLane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr stepKInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (TreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf KSpatial KStateMatches condHolds_NE_sub lt31_of_beq_false setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep (
  sepWP_of_stepKInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  anfMatchesSpec btreeExprBeq btreeExprBeq_eq_true btree_ext_get kpairBeq kpairBeq_eq_true
  mkRoundEnv pstateBeq pstateBeq_eq_true readSlot readSlot_holds slotHolds slotValid
  truncate64_append ushr64_truncate64_append vreg128_repack writeSlot
  writeSlot_preserves_matches writeSlotsFrom)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  btreeAll_get btreeAll_mono btreeAll_ofFn evalKExpr_congr_vars evalMemTree_congr_vars
  evalSlotsHi evalSlotsHi_getD evalSlotsHi_size evalSlotsLo evalSlotsLo_getD evalSlotsLo_size
  exprVarsLt exprVarsLt_mapBodyExpr exprVarsLt_mono findSpecLane findSpecLane_sound mapBodyExpr
  mkPostLoopEnv stateVarsLt)

/-! ## 1. Relocation-Free Fetch Across `Seg5` Core (`w ∈ [4150..4315) ∪ [4324..7236)`) -/

@[expose] def InSeg5Word04 (j : Nat) : Prop :=
  (4150 ≤ j ∧ j < 4315) ∨ (4324 ≤ j ∧ j < 7236)

private theorem blk04_relocs_outside_seg5 :
    blkLib04.text.relocs.all (fun r => decide (
      !(16600 ≤ r.off && r.off < 17260) &&
      !(17296 ≤ r.off && r.off < 28944))) = true := by
  decide +kernel

private theorem blk04_relocAt?_seg5 {j : Nat} (hj : InSeg5Word04 j) :
    (blkLib04.text.relocAt? (4 * j)).isNone = true := by
  cases hr : blkLib04.text.relocAt? (4 * j) with
  | none => rfl
  | some r =>
      have hmem := CodeBlock.relocAt?_mem hr
      have hoff := CodeBlock.relocAt?_off hr
      have hall := (List.all_eq_true.mp blk04_relocs_outside_seg5) r hmem
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not] at hall
      unfold InSeg5Word04 at hj
      omega

theorem fetch_blk04_seg5 [MlKemPlacement] {b : BitVec 64} {j : Nat} {inst : Instr}
    (hj : InSeg5Word04 j) (hfw : fetchWordTree04 j = some inst) :
    (blkPC04.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hj_lt : j < 13411 := by unfold InSeg5Word04 at hj; omega
  have hdec : blkTree04.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    rw [show 4 * j / 4 = j from by omega]
    unfold fetchWordTree04 at hfw
    cases hq : blkTree04.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
        rcases q with ⟨b0, b1, b2, b3⟩
        simp [hq] at hfw ⊢
        exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl04) (b := b)
    (X := fun _ => none) blk04_code_eq blk04_tree_size blkPlaceable04 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk04_code_eq blk04_tree_size
    (by omega) (by omega) (by omega) hdec (blk04_relocAt?_seg5 hj) hnh

@[expose] def checkInstrsAt04 (w0 : Nat) : List Instr → Bool
  | [] => true
  | i :: is => (fetchWordTree04 w0 == some i) && checkInstrsAt04 (w0 + 1) is

theorem fetchesInstrsAt_blk04_seg5 [MlKemPlacement] {b pcBase : BitVec 64}
    {w0 idx : Nat} {instrs : List Instr}
    (hlo : 4324 ≤ w0) (hhi : w0 + instrs.length ≤ 7236)
    (hbase : pcBase + BitVec.ofNat 64 (4 * idx) = b + BitVec.ofNat 64 (4 * w0))
    (hchk : checkInstrsAt04 w0 instrs = true) :
    FetchesInstrsAt (blkPC04.rebase b (fun _ => none)) pcBase idx instrs := by
  induction instrs generalizing w0 idx with
  | nil => intro _ _ hget; simp at hget
  | cons i is ih =>
      simp only [checkInstrsAt04, Bool.and_eq_true, beq_iff_eq] at hchk
      simp only [List.length_cons] at hhi
      intro k inst hget
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget
          have npc : pcAt pcBase (idx + 0) = b + BitVec.ofNat 64 (4 * w0) := by
            unfold pcAt; simpa using hbase
          rw [npc]; exact fetch_blk04_seg5 (Or.inr ⟨hlo, by omega⟩) hchk.1
      | succ k' =>
          simp only [List.getElem?_cons_succ] at hget
          have hadj : pcBase + BitVec.ofNat 64 (4 * (idx + 1)) =
              b + BitVec.ofNat 64 (4 * (w0 + 1)) := by
            have h1 : BitVec.ofNat 64 (4 * (idx + 1)) = BitVec.ofNat 64 (4 * idx) + 4#64 := by
              rw [← BitVec.ofNat_add]; rfl
            have h2 : BitVec.ofNat 64 (4 * (w0 + 1)) = BitVec.ofNat 64 (4 * w0) + 4#64 := by
              rw [← BitVec.ofNat_add]; rfl
            rw [h1, h2, ← BitVec.add_assoc, hbase, BitVec.add_assoc]
          have hstep := ih (w0 := w0 + 1) (idx := idx + 1) (by omega) (by omega) hadj hchk.2 k' inst hget
          have hpc_eq : pcAt pcBase (idx + (k' + 1)) = pcAt pcBase ((idx + 1) + k') := by
            unfold pcAt; congr 2; omega
          simpa [hpc_eq] using hstep

attribute [local irreducible] keccakF1600 blkPC04

/-! ## 2. `runKRange04` & `mkLoopInitState04` (`rcBase` in `x22`) -/

@[expose] def runKRange04 (cfg : KCfg) (startWord : Nat) : Nat → KState → Option KState
  | 0, st => some st
  | n + 1, st =>
      match fetchWordTree04 startWord with
      | some inst =>
          match stepKInst cfg inst st with
          | some st' => runKRange04 cfg (startWord + 1) n st'
          | none => none
      | none => none

theorem sepWP_of_runKRange04 [MlKemPlacement] {b target_pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {w count : Nat} {st st' : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcfg : KCfgWf cfg) (hrloop : env.rLoop < 24)
    (hin : ∀ k, k < count → InSeg5Word04 (w + k))
    (hrun_k : runKRange04 cfg w count st = some st')
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * (w + count)) → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP (blkPC04.rebase b (fun _ => none)) target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) target_pc s (KSpatial cfg env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
      simp only [runKRange04, Option.some.injEq] at hrun_k
      subst hrun_k
      exact hnext s (by simpa [Nat.add_zero] using hpc) hrun hm
  | succ n ih =>
      simp only [runKRange04] at hrun_k
      cases hfw : fetchWordTree04 w with
      | none => simp [hfw] at hrun_k
      | some inst =>
          simp only [hfw] at hrun_k
          cases hst : stepKInst cfg inst st with
          | none => simp [hst] at hrun_k
          | some stm =>
              simp only [hst] at hrun_k
              have hfetch := fetch_blk04_seg5 (b := b) (by simpa using hin 0 (by omega)) hfw
              refine sepWP_of_stepKInst hcfg hrloop hpc hrun hfetch hst hm ?_
              intro s1 hpc1 hrun1 hm1
              have hpc1' : s1.pc = b + BitVec.ofNat 64 (4 * (w + 1)) := by
                rw [hpc1, BitVec.add_assoc]; congr 1
                have hmul : 4 * (w + 1) = 4 * w + 4 := by omega
                rw [hmul, BitVec.ofNat_add]
              exact ih (fun k hk => by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hin (k + 1) (by omega))
                hrun_k hpc1' hrun1 hm1 (fun s2 hpc2 hrun2 hm2 =>
                  hnext s2 (by simpa [Nat.add_right_comm, Nat.add_assoc] using hpc2) hrun2 hm2)

@[expose] def mkBaseState04 (rCnt : BitVec 5) : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)))
    gprs := ((BTree.ofFn 5 (fun g => .var (200 + g))).set 22 (.rcAdd 0#64)).set rCnt.toNat .rcLoopOff
    memA := BTree.ofFn 9 (fun i => .var (300 + i))
    memB := BTree.ofFn 9 (fun i => .var (900 + i))
    pstate := none }

@[expose] def mkLoopInitState04 (cfg : KCfg) (rCnt : BitVec 5) (slots : List KSlot) : KState :=
  writeSlotsFrom cfg 0 slots (mkBaseState04 rCnt)

theorem mkBaseState04_matches {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s : State} {tA tB : BTree (BitVec 64) 9} {rCnt : BitVec 5}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 22#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r)) :
    let env := mkRoundEnv sp rcBase r sA sB s tA tB
    KStateMatches env (mkBaseState04 rCnt) s ∧
      (mkBaseState04 rCnt).memA.map (evalKExpr env) = tA ∧
      (mkBaseState04 rCnt).memB.map (evalKExpr env) = tB := by
  intro env
  refine ⟨⟨hsp, hspA, ?_, ?_, fun _ _ h => by simp [mkBaseState04] at h⟩, ?_, ?_⟩
  · intro vr
    simp only [mkBaseState04]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
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
    simp only [mkBaseState04]; rw [BTree.get_set _ rCnt.toNat _ rCnt.isLt g.toNat g.isLt]
    by_cases hgc : g.toNat = rCnt.toNat
    · have heq := BitVec.eq_of_toNat_eq hgc; subst heq; simp [evalKExpr, env, mkRoundEnv, hcnt]
    · simp only [hgc, ↓reduceIte]; rw [BTree.get_set _ 22 _ (by decide) g.toNat g.isLt]
      by_cases hg22 : g.toNat = 22
      · have heq : g = 22#5 := BitVec.eq_of_toNat_eq hg22
        subst heq; simp [evalKExpr, env, mkRoundEnv, hrc]
      · simp only [hg22, ↓reduceIte]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
        have hlt := g.isLt
        have hb : ¬(200 + g.toNat < 25) ∧ ¬(200 + g.toNat < 50) ∧ ¬(200 + g.toNat < 164) ∧
            200 + g.toNat < 232 ∧ 200 + g.toNat - 200 = g.toNat :=
          ⟨by omega, by omega, by omega, by omega, by omega⟩
        simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [mkBaseState04]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
        300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [mkBaseState04]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(900 + i < 25) ∧ ¬(900 + i < 50) ∧ ¬(900 + i < 164) ∧ ¬(900 + i < 232) ∧
        ¬(900 + i < 812) ∧ 900 + i < 1412 ∧ 900 + i - 900 = i :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2.1, hb.2.2.2.2.2.2]

private theorem writeSlotsFrom04_matches {cfg : KCfg} {env : KEnv}
    {sA sB : KeccakState} {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hv0 : ∀ k, k < 25 → evalKExpr env (.var k) = sA.getD k 0#64)
    (hv25 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = sB.getD k 0#64)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length = 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (sA.getD (k + j) 0#64) (sB.getD (k + j) 0#64)) →
      KStateMatches env st s → st.memA.map (evalKExpr env) = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsFrom cfg k rem st) s ∧
        (writeSlotsFrom cfg k rem st).memA.map (evalKExpr env) = tA ∧
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

theorem mkLoopInitState04_matches {cfg : KCfg} {sp rcBase : BitVec 64} {r : Nat}
    {sA sB : KeccakState} {s : State} {tA tB : BTree (BitVec 64) 9}
    {rCnt : BitVec 5} {slots : List KSlot}
    (hlen : slots.length = 25) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 22#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r))
    (hslots : ∀ idx, idx < 25 →
      slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) :
    KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState04 cfg rCnt slots) s ∧
      (mkLoopInitState04 cfg rCnt slots).memA.map (evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB)) = tA ∧
      (mkLoopInitState04 cfg rCnt slots).memB.map (evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB)) = tB ∧
      (mkLoopInitState04 cfg rCnt slots).memB = (mkBaseState04 rCnt).memB := by
  rcases mkBaseState04_matches (sA := sA) (sB := sB) (tA := tA) (tB := tB)
    hsp hspA hrc hcnt with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var k) = sA.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, mkRoundEnv, hk]
  have hv25 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var (25 + k)) = sB.getD k 0#64 :=
    fun k hk => by
      simp [evalKExpr, mkRoundEnv, show ¬(25 + k < 25) by omega,
        show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  rcases writeSlotsFrom04_matches (cfg := cfg) hv0 hv25 slots 0 (mkBaseState04 rCnt) (by omega)
    (fun j hj => by simpa using hslots j (by omega)) hm0 htA0 rfl with ⟨hmF, htAF, hmBF⟩
  unfold mkLoopInitState04
  exact ⟨hmF, htAF, by rw [hmBF, htB0], hmBF⟩

/-! ## 3. 24-Round Symbolic `Keccak-f[1600]` Loop Verifier (`checkKeccakLoop04`) -/

private theorem roundEnv_preserved_gpr {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s sm : State} {tA tB : BTree (BitVec 64) 9} {stB : KState}
    (hmB : KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) stB sm)
    {g : BitVec 5} (hg31 : g.toNat < 31) (hgVar : stB.gprs.get g.toNat = .var (200 + g.toNat)) :
    sm.readReg64 (.gpr g) = s.readReg64 (.gpr g) := by
  have h := hmB.hgprs g hg31; rw [hgVar] at h; have hlt := g.isLt
  have hb : ¬(200 + g.toNat < 25) ∧ ¬(200 + g.toNat < 50) ∧ ¬(200 + g.toNat < 164) ∧
      200 + g.toNat < 232 ∧ 200 + g.toNat - 200 = g.toNat :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  simpa [evalKExpr, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2] using h

private theorem roundEnv_preserved_vreg {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
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

private theorem roundEnv_preserved_memA (sp rcBase : BitVec 64) (r : Nat) (sA sB : KeccakState)
    (s : State) (tA tB : BTree (BitVec 64) 9) {stB : KState} {i : Nat} (hi : i < 512)
    (hmemVar : stB.memA.get i = .var (300 + i)) :
    (stB.memA.map (evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB))).get i = tA.get i := by
  rw [BTree.get_map, hmemVar]
  have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
      300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp [evalKExpr, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]

@[expose] def checkKeccakLoop04 (cfg : KCfg) (wHead nBody : Nat)
    (rCnt : BitVec 5) (slots : List KSlot) : Option KState :=
  if Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 22#5) && (rCnt != 31#5) &&
     Nat.ble 4324 wHead && Nat.ble (wHead + nBody + 1) 7236 then
    match fetchWordTree04 (wHead + nBody) with
    | some (.bCond cond disp) =>
        if cond == .NE && disp == 0#64 - BitVec.ofNat 64 (4 * nBody) then
          match runKRange04 cfg wHead nBody (mkLoopInitState04 cfg rCnt slots) with
          | none => none
          | some stBody =>
              if pstateBeq stBody.pstate (some (.rcLoopNext, .const64 192#64)) &&
                 (stBody.gprs.get rCnt.toNat).beq .rcLoopNext &&
                 (stBody.gprs.get 22).beq (.rcAdd 0#64) &&
                 btreeExprBeq stBody.memB (mkBaseState04 rCnt).memB &&
                 (List.range 25).all (fun idx =>
                   let (eLo, eHi) := readSlot cfg stBody (slots.getD idx (.vreg 0))
                   anfMatchesSpec eLo 0 idx && anfMatchesSpec eHi 25 idx)
              then some stBody
              else none
        else none
    | _ => none
  else none

private theorem loop_done_ne_of_lt23 {r : Nat} (hr : r < 23) :
    BitVec.ofNat 64 (8 * r) + 8#64 ≠ 192#64 := by
  intro h; have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1; omega

theorem sepWP_of_keccakLoop24_04 [MlKemPlacement] {b tgt sp rcBase : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg)
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {stBody : KState}
    (hchk : checkKeccakLoop04 cfg wHead nBody rCnt slots = some stBody)
    {sA0 sB0 : KeccakState} (hsA0 : sA0.size = 25) (hsB0 : sB0.size = 25)
    {s0 : State} {tA0 tB0 : BTree (BitVec 64) 9} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wHead)) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hrc0 : s0.readReg64 (.gpr 22#5) = rcBase)
    (hcnt0 : s0.readReg64 (.gpr rCnt) = 0#64)
    (hslots0 : ∀ idx, idx < 25 →
      slotHolds cfg s0 tA0 (slots.getD idx (.vreg 0)) (sA0.getD idx 0#64) (sB0.getD idx 0#64))
    (hnext : ∀ (sf : State) (env23 : KEnv),
      sf.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) →
      sf.status = .Running →
      sf.sp = sp → sf.spAligned = true →
      sf.readReg64 (.gpr 22#5) = rcBase →
      sf.readReg64 (.gpr rCnt) = 192#64 →
      sf.pstate = (AddWithCarry64 192#64 (~~~192#64) true).2 →
      (∀ g : BitVec 5, g.toNat < 31 → stBody.gprs.get g.toNat = .var (200 + g.toNat) →
        sf.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
      (∀ vr : BitVec 5,
        stBody.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) →
        sf.readVReg128 vr = s0.readVReg128 vr) →
      (∀ i, i < 512 → stBody.memA.get i = .var (300 + i) →
        (stBody.memA.map (evalKExpr env23)).get i = tA0.get i) →
      (∀ e idx, idx < 25 → anfMatchesSpec e 0 idx = true →
        evalKExpr env23 e = (keccakF1600 sA0).getD idx 0#64) →
      (∀ e idx, idx < 25 → anfMatchesSpec e 25 idx = true →
        evalKExpr env23 e = (keccakF1600 sB0).getD idx 0#64) →
      KStateMatches env23 stBody sf →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt sf
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (stBody.memA.map (evalKExpr env23)) ∗
          TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗
        TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA0 ∗
        TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) post oom := by
  unfold checkKeccakLoop04 at hchk
  split at hchk; case isFalse => cases hchk
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨hlen, hslVal⟩, _hne22⟩, hne31⟩, hwLo⟩, hwHi⟩
  have hcntLt31 : rCnt.toNat < 31 := lt31_of_beq_false (beq_false_of_ne hne31)
  cases hfw : fetchWordTree04 (wHead + nBody) with
  | none => simp [hfw] at hchk
  | some inst =>
      simp only [hfw] at hchk
      cases inst <;> dsimp only at hchk <;> try cases hchk
      rename_i cond disp
      split at hchk; case isFalse => cases hchk
      case isTrue hbr =>
      simp only [Bool.and_eq_true] at hbr; rcases hbr with ⟨hcondB, hdispB⟩
      cases cond <;> try cases hcondB
      have hdisp : disp = 0#64 - BitVec.ofNat 64 (4 * nBody) := beq_iff_eq.mp hdispB
      cases hrunB : runKRange04 cfg wHead nBody (mkLoopInitState04 cfg rCnt slots) with
      | none => simp [hrunB] at hchk
      | some stB =>
          simp only [hrunB] at hchk
          split at hchk; case isFalse => cases hchk
          case isTrue hpost =>
          simp only [Option.some.injEq] at hchk; subst hchk
          simp only [Bool.and_eq_true] at hpost
          rcases hpost with ⟨⟨⟨⟨hpstB, hcntB⟩, hrcB⟩, hmemBB⟩, hanfB⟩
          have hpst : stB.pstate = some (.rcLoopNext, .const64 192#64) := pstateBeq_eq_true hpstB
          have hcntNext : stB.gprs.get rCnt.toNat = .rcLoopNext := KExpr.beq_eq_true hcntB
          have hrcNext : stB.gprs.get 22 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
          have hmemBEq : stB.memB = (mkBaseState04 rCnt).memB := btreeExprBeq_eq_true hmemBB
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
          have hinB : ∀ k, k < nBody → InSeg5Word04 (wHead + k) := fun k hk => Or.inr ⟨by omega, by omega⟩
          suffices ∀ (rem r : Nat) (sA sB : KeccakState) (s : State) (tA : BTree (BitVec 64) 9),
              r + (rem + 1) = 24 → sA.size = 25 → sB.size = 25 →
              keccakRunFrom r sA = keccakF1600 sA0 → keccakRunFrom r sB = keccakF1600 sB0 →
              s.pc = b + BitVec.ofNat 64 (4 * wHead) → s.status = .Running →
              s.sp = sp → s.spAligned = true →
              s.readReg64 (.gpr 22#5) = rcBase →
              s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r) →
              (∀ idx, idx < 25 →
                slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) →
              (∀ g : BitVec 5, g.toNat < 31 → stB.gprs.get g.toNat = .var (200 + g.toNat) →
                s.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
              (∀ vr : BitVec 5,
                stB.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) →
                s.readVReg128 vr = s0.readVReg128 vr) →
              (∀ i, i < 512 → stB.memA.get i = .var (300 + i) → tA.get i = tA0.get i) →
              SepWP (blkPC04.rebase b (fun _ => none)) tgt s
                ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                  TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                  TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) post oom by
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
              rcases mkLoopInitState04_matches (tB := tB0) hlen hsp hspA hrc hcnt hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg env23 (mkLoopInitState04 cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                    TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                    TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [env23, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_of_runKRange04 hv (by simp [env23, mkRoundEnv]) hinB
                hrunB hpc hrun hmI ?_
              intro sm hmpc hmrun hmB
              have htBB : stB.memB.map (evalKExpr env23) = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk04_seg5 (b := b) (Or.inr ⟨by omega, by omega⟩) hfw
              have hps23 : sm.pstate = (AddWithCarry64 192#64 (~~~192#64) true).2 := by
                have hp := hmB.hpstate _ _ hpst
                have hl : evalKExpr env23 .rcLoopNext = 192#64 := rfl
                have hr : evalKExpr env23 (.const64 192#64) = 192#64 := rfl
                rwa [hl, hr] at hp
              have hzNe : ConditionHolds .NE sm.pstate = false := by
                rw [hps23, condHolds_NE_sub]; decide
              refine SepWP.step_pure hmpc hmrun hfetchBr (s' := sm.advancePC) ?_ rfl ?_
              · rw [setPC_self hmpc]; simp only [Program.evalInst, execInstWithSvc, hzNe, Bool.false_eq_true, ↓reduceIte]
              · have hpcEnd : sm.advancePC.pc =
                    b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) := by
                  simp only [State.advancePC, hmpc]; bv_omega
                have hspEnd : KSpatial cfg env23 stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                      TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA
                        (stB.memA.map (evalKExpr env23)) ∗
                      TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [env23, mkRoundEnv]
                rw [hspEnd]
                have hA23 : keccakF1600Round sA (keccakRcAt 23) = keccakF1600 sA0 := by
                  rwa [keccakRunFrom_step 23 (by decide) sA, keccakRunFrom_24] at hrunA
                have hB23 : keccakF1600Round sB (keccakRcAt 23) = keccakF1600 sB0 := by
                  rwa [keccakRunFrom_step 23 (by decide) sB, keccakRunFrom_24] at hrunB_st
                refine hnext sm.advancePC env23 hpcEnd hmrun hmB.hsp hmB.hsp_al ?_ ?_ hps23
                  (fun g hg31 hgv => (roundEnv_preserved_gpr hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv =>
                    (roundEnv_preserved_memA sp rcBase 23 sA sB s tA tB0 hi hmv).trans (hmemAP i hi hmv))
                  ?_ ?_ ⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hpstate⟩
                · have h := hmB.hgprs 22#5 (by decide)
                  change _ = evalKExpr env23 (stB.gprs.get 22) at h
                  rw [hrcNext] at h; simpa [evalKExpr, env23, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hcntLt31
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
              rcases mkLoopInitState04_matches (tB := tB0) hlen hsp hspA hrc hcnt hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg envR (mkLoopInitState04 cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                    TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                    TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [envR, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_of_runKRange04 hv (by simp [envR, mkRoundEnv]; omega) hinB
                hrunB hpc hrun hmI ?_
              intro sm hmpc hmrun hmB
              have htBB : stB.memB.map (evalKExpr envR) = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk04_seg5 (b := b) (Or.inr ⟨by omega, by omega⟩) hfw
              have hzNe : ConditionHolds .NE sm.pstate = true := by
                have hp := hmB.hpstate _ _ hpst
                have hl : evalKExpr envR .rcLoopNext = BitVec.ofNat 64 (8 * r) + 8#64 := rfl
                have hr : evalKExpr envR (.const64 192#64) = 192#64 := rfl
                rw [hp, hl, hr, condHolds_NE_sub, decide_eq_true_eq]
                exact loop_done_ne_of_lt23 hrLt23
              have hpcBack : sm.pc + disp = b + BitVec.ofNat 64 (4 * wHead) := by
                rw [hmpc, hdisp]; bv_omega
              refine SepWP.step_pure hmpc hmrun hfetchBr
                (s' := sm.setPC (b + BitVec.ofNat 64 (4 * wHead))) ?_ rfl ?_
              · rw [setPC_self hmpc]
                simp only [Program.evalInst, execInstWithSvc, hzNe, ↓reduceIte]
                rw [hpcBack]
              · have hspNext : KSpatial cfg envR stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗
                      TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA
                        (stB.memA.map (evalKExpr envR)) ∗
                      TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [envR, mkRoundEnv]
                rw [hspNext]
                let sA' := keccakF1600Round sA (keccakRcAt r)
                let sB' := keccakF1600Round sB (keccakRcAt r)
                refine ih (r + 1) sA' sB' (sm.setPC (b + BitVec.ofNat 64 (4 * wHead)))
                  (stB.memA.map (evalKExpr envR)) (by omega)
                  (keccakF1600Round_size sA _) (keccakF1600Round_size sB _)
                  (by rwa [keccakRunFrom_step r (by omega) sA] at hrunA)
                  (by rwa [keccakRunFrom_step r (by omega) sB] at hrunB_st)
                  rfl hmrun hmB.hsp hmB.hsp_al ?_ ?_ ?_
                  (fun g hg31 hgv => (roundEnv_preserved_gpr hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv =>
                    (roundEnv_preserved_memA sp rcBase r sA sB s tA tB0 hi hmv).trans (hmemAP i hi hmv))
                · have h := hmB.hgprs 22#5 (by decide)
                  change _ = evalKExpr envR (stB.gprs.get 22) at h
                  rw [hrcNext] at h; simpa [evalKExpr, envR, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hcntLt31
                  rw [hcntNext] at h
                  change sm.readReg64 (.gpr rCnt) = _
                  rw [h]; simp only [evalKExpr, envR, mkRoundEnv]; bv_omega
                · intro idx hidx
                  have hsl := readSlot_holds (hslValIdx idx hidx)
                    (⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hpstate⟩ :
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

/-! ## 4. Post-Loop Transition (`stepKLoopSym04`, `sepWP_of_stepKLoop04`) & 14 `KSlot` Tables -/

@[expose] def buildPostLoopState04 (baseOut : Nat) (rCnt : BitVec 5)
    (stPre stBody : KState) : KState :=
  { vregs := BTree.ofFn 5 (fun vr =>
      let pB := stBody.vregs.get vr
      if kpairBeq pB (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)) then stPre.vregs.get vr
      else
        (mapBodyExpr baseOut (baseOut + 50 + 2 * vr) pB.1,
         mapBodyExpr baseOut (baseOut + 50 + 2 * vr + 1) pB.2))
    gprs := BTree.ofFn 5 (fun g =>
      if Nat.beq g 22 then .rcAdd 0#64
      else if Nat.beq g rCnt.toNat then .const64 192#64
      else if (stBody.gprs.get g).beq (.var (200 + g)) then stPre.gprs.get g
      else .var (baseOut + 114 + g))
    memA := BTree.ofFn 9 (fun i =>
      let eB := stBody.memA.get i
      if eB.beq (.var (300 + i)) then stPre.memA.get i
      else mapBodyExpr baseOut (baseOut + 146 + i) eB)
    memB := stPre.memB
    pstate := some (.const64 192#64, .const64 192#64) }

@[expose] def stepKLoopSym04 (cfg : KCfg) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) : Option KState :=
  if Nat.ble 100 baseOut && stateVarsLt baseOut stPre &&
     Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 31#5) &&
     (stPre.gprs.get 22).beq (.rcAdd 0#64) &&
     (stPre.gprs.get rCnt.toNat).beq (.const64 0#64) then
    match checkKeccakLoop04 cfg wHead nBody rCnt slots with
    | none => none
    | some stBody => some (buildPostLoopState04 baseOut rCnt stPre stBody)
  else none

theorem stateVarsLt_stepKLoopSym04 {cfg : KCfg} {wHead nBody : Nat} {rCnt : BitVec 5}
    {slots : List KSlot} {baseOut : Nat} {stPre stPost : KState}
    (h : stepKLoopSym04 cfg wHead nBody rCnt slots baseOut stPre = some stPost) :
    stateVarsLt (baseOut + 658) stPost = true := by
  unfold stepKLoopSym04 at h
  split at h; case isFalse => cases h
  case isTrue hhdr =>
  simp only [Bool.and_eq_true] at hhdr
  have hsv : stateVarsLt baseOut stPre = true := hhdr.1.1.1.1.1.2
  simp only [stateVarsLt, Bool.and_eq_true] at hsv
  rcases hsv with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hc : checkKeccakLoop04 cfg wHead nBody rCnt slots with
  | none => simp [hc] at h
  | some stBody =>
      simp only [hc, Option.some.injEq] at h; subst h
      simp only [stateVarsLt, buildPostLoopState04, Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · apply btreeAll_ofFn; intro vr hvr
        split
        · have hp := btreeAll_get _ stPre.vregs hvPre vr hvr
          simp only [Bool.and_eq_true] at hp ⊢
          exact ⟨exprVarsLt_mono (by omega) _ hp.1, exprVarsLt_mono (by omega) _ hp.2⟩
        · simp only [Bool.and_eq_true]
          exact ⟨exprVarsLt_mapBodyExpr (by omega) (by change vr < 32 at hvr; omega) _,
            exprVarsLt_mapBodyExpr (by omega) (by change vr < 32 at hvr; omega) _⟩
      · apply btreeAll_ofFn; intro g hg
        split
        · rfl
        · split
          · rfl
          · split
            · exact exprVarsLt_mono (by omega) _ (btreeAll_get _ stPre.gprs hgPre g hg)
            · simp only [exprVarsLt, Nat.blt_eq]; change g < 32 at hg; omega
      · apply btreeAll_ofFn; intro i hi
        split
        · exact exprVarsLt_mono (by omega) _ (btreeAll_get _ stPre.memA hmAPre i hi)
        · exact exprVarsLt_mapBodyExpr (by omega) (by change i < 512 at hi; omega) _
      · exact btreeAll_mono (exprVarsLt_mono (by omega)) stPre.memB hmBPre

private theorem eval_mapBodyExpr04 {env0 env23 : KEnv} {baseOut fallbackId : Nat}
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

theorem sepWP_of_stepKLoop04 [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {env0 : KEnv}
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {baseOut : Nat}
    {stPre stPost : KState}
    (hstep : stepKLoopSym04 cfg wHead nBody rCnt slots baseOut stPre = some stPost)
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hm0 : KStateMatches env0 stPre s0)
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wHead)) (hrun0 : s0.status = .Running)
    (hnext : ∀ (sf : State) (envPost : KEnv),
      sf.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) →
      sf.status = .Running →
      envPost.sp = env0.sp → envPost.rcBase = env0.rcBase → envPost.rLoop = env0.rLoop →
      (∀ id, id < baseOut → envPost.vars id = env0.vars id) →
      (∀ idx, idx < 25 →
        envPost.vars (baseOut + idx) =
          (keccakF1600 (evalSlotsLo cfg env0 stPre slots)).getD idx 0#64) →
      (∀ idx, idx < 25 →
        envPost.vars (baseOut + 25 + idx) =
          (keccakF1600 (evalSlotsHi cfg env0 stPre slots)).getD idx 0#64) →
      KStateMatches envPost stPost sf →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt sf (KSpatial cfg envPost stPost F) post oom) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 stPre F) post oom := by
  unfold stepKLoopSym04 at hstep
  split at hstep; case isFalse => cases hstep
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨⟨_hb100, hsvPre⟩, hlen⟩, hslVal⟩, hne31⟩, hrcB⟩, hcntB⟩
  have hrcExpr : stPre.gprs.get 22 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
  have hcntExpr : stPre.gprs.get rCnt.toNat = .const64 0#64 := KExpr.beq_eq_true hcntB
  simp only [stateVarsLt, Bool.and_eq_true] at hsvPre
  rcases hsvPre with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hchk : checkKeccakLoop04 cfg wHead nBody rCnt slots with
  | none => simp [hchk] at hstep
  | some stBody =>
      simp only [hchk, Option.some.injEq] at hstep; subst hstep
      let sA0 := evalSlotsLo cfg env0 stPre slots
      let sB0 := evalSlotsHi cfg env0 stPre slots
      have hrc0 : s0.readReg64 (.gpr 22#5) = env0.rcBase := by
        have h := hm0.hgprs 22#5 (by decide)
        change _ = evalKExpr env0 (stPre.gprs.get 22) at h
        rw [hrcExpr] at h; simpa [evalKExpr] using h
      have hcnt0 : s0.readReg64 (.gpr rCnt) = 0#64 := by
        have h := hm0.hgprs rCnt (Nat.lt_of_le_of_ne (by have := rCnt.isLt; omega)
          (fun he => hne31 (BitVec.eq_of_toNat_eq he)))
        rw [hcntExpr] at h; simpa [evalKExpr] using h
      have hslots0 : ∀ idx, idx < 25 →
          slotHolds cfg s0 (stPre.memA.map (evalKExpr env0)) (slots.getD idx (.vreg 0))
            (sA0.getD idx 0#64) (sB0.getD idx 0#64) := fun idx hidx => by
        have hlt : idx < slots.length := by omega
        have hsv : slotValid cfg (slots.getD idx (.vreg 0)) = true := by
          simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          exact List.all_eq_true.mp hslVal _ (List.getElem_mem hlt)
        rw [evalSlotsLo_getD _ _ _ _ hidx, evalSlotsHi_getD _ _ _ _ hidx]
        exact readSlot_holds hsv hm0
      dsimp only [KSpatial]
      refine sepWP_of_keccakLoop24_04 (sA0 := sA0) (sB0 := sB0)
        (tA0 := stPre.memA.map (evalKExpr env0)) (tB0 := stPre.memB.map (evalKExpr env0))
        hv hchk (evalSlotsLo_size _ _ _ _) (evalSlotsHi_size _ _ _ _)
        hpc0 hrun0 hm0.hsp hm0.hsp_al hrc0 hcnt0 hslots0 ?_
      intro sf env23 hpcf hrunf hspf hspAf hrcf hcntf hps23
        hgprP hvregP hmemAP hA23 hB23 hm23
      let tAPost := stBody.memA.map (evalKExpr env23)
      let envP := mkPostLoopEnv env0 baseOut (keccakF1600 sA0) (keccakF1600 sB0) sf tAPost
      have hvarsP : ∀ id, id < baseOut → envP.vars id = env0.vars id :=
        fun id hid => by simp [envP, mkPostLoopEnv, hid]
      have htAPEq :
          (BTree.ofFn 9 fun i =>
            let eB := stBody.memA.get i
            if eB.beq (.var (300 + i)) then stPre.memA.get i
            else mapBodyExpr baseOut (baseOut + 146 + i) eB).map (evalKExpr envP) = tAPost := by
        apply btree_ext_get; intro i hi
        simp only [BTree.get_map]; rw [BTree.get_ofFn 9 _ i hi]
        by_cases heq : (stBody.memA.get i).beq (.var (300 + i)) = true
        · simp only [heq, ↓reduceIte]
          have hv0 := hmemAP i hi (KExpr.beq_eq_true heq)
          have hcongr := evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP
            (stPre.memA.get i) (btreeAll_get _ stPre.memA hmAPre i hi)
          rw [hcongr]; simpa [tAPost, BTree.get_map] using hv0.symm
        · simp only [Bool.eq_false_iff.mpr heq, Bool.false_eq_true, ↓reduceIte]
          have hfb : envP.vars (baseOut + 146 + i) = evalKExpr env23 (stBody.memA.get i) := by
            change i < 512 at hi
            simp [envP, mkPostLoopEnv, tAPost, BTree.get_map,
              show ¬(baseOut + 146 + i < baseOut) by omega,
              show ¬(baseOut + 146 + i < baseOut + 25) by omega,
              show ¬(baseOut + 146 + i < baseOut + 50) by omega,
              show ¬(baseOut + 146 + i < baseOut + 114) by omega,
              show ¬(baseOut + 146 + i < baseOut + 146) by omega,
              show baseOut + 146 + i < baseOut + 658 by omega,
              show baseOut + 146 + i - (baseOut + 146) = i by omega]
          exact (eval_mapBodyExpr04 (fun idx hi hm => hA23 _ idx hi hm)
            (fun idx hi hm => hB23 _ idx hi hm) hfb).trans
            (BTree.get_map (evalKExpr env23) stBody.memA i).symm
      have htBPEq : stPre.memB.map (evalKExpr envP) = stPre.memB.map (evalKExpr env0) :=
        evalMemTree_congr_vars hmBPre rfl rfl rfl hvarsP
      have hmP : KStateMatches envP (buildPostLoopState04 baseOut rCnt stPre stBody) sf := by
        refine ⟨hspf, hspAf, ?_, ?_, ?_⟩
        · intro vr
          have hlt := vr.isLt
          dsimp only [buildPostLoopState04]; rw [BTree.get_ofFn 5 _ vr.toNat hlt]
          by_cases heq :
              kpairBeq (stBody.vregs.get vr.toNat)
                (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) = true
          · simp only [heq, ↓reduceIte]
            rw [hvregP vr (kpairBeq_eq_true heq), hm0.hvregs vr]
            have hpv := btreeAll_get _ stPre.vregs hvPre vr.toNat hlt
            simp only [Bool.and_eq_true] at hpv
            rw [evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _ hpv.2,
              evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _ hpv.1]
          · simp only [Bool.eq_false_iff.mpr heq, Bool.false_eq_true, ↓reduceIte]
            have hv23 := hm23.hvregs vr
            have hfbLo : envP.vars (baseOut + 50 + 2 * vr.toNat) =
                evalKExpr env23 (stBody.vregs.get vr.toNat).1 := by
              have hpar : (2 * vr.toNat % 2 == 0) = true := beq_iff_eq.mpr (by omega)
              simp only [envP, mkPostLoopEnv, show ¬(baseOut + 50 + 2 * vr.toNat < baseOut) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat < baseOut + 25) by omega,
                show ¬(baseOut + 50 + 2 * vr.toNat < baseOut + 50) by omega,
                show baseOut + 50 + 2 * vr.toNat < baseOut + 114 by omega, ↓reduceIte,
                show baseOut + 50 + 2 * vr.toNat - (baseOut + 50) = 2 * vr.toNat by omega,
                show 2 * vr.toNat / 2 = vr.toNat by omega, hpar, BitVec.ofNat_toNat, BitVec.setWidth_eq]
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
            rw [eval_mapBodyExpr04 (fun idx hi hm => hA23 _ idx hi hm)
              (fun idx hi hm => hB23 _ idx hi hm) hfbHi,
              eval_mapBodyExpr04 (fun idx hi hm => hA23 _ idx hi hm)
                (fun idx hi hm => hB23 _ idx hi hm) hfbLo, ← hv23]
        · intro g hg31
          have hlt := g.isLt
          dsimp only [buildPostLoopState04]; rw [BTree.get_ofFn 5 _ g.toNat hlt]
          by_cases hg22 : Nat.beq g.toNat 22 = true
          · simp only [hg22, ↓reduceIte, evalKExpr, envP, mkPostLoopEnv]
            have hgEq : g = 22#5 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hg22)
            subst hgEq; simpa using hrcf
          · simp only [Bool.eq_false_iff.mpr hg22, Bool.false_eq_true, ↓reduceIte]
            by_cases hgc : Nat.beq g.toNat rCnt.toNat = true
            · simp only [hgc, ↓reduceIte, evalKExpr]
              have hgEq : g = rCnt := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hgc)
              subst hgEq; exact hcntf
            · simp only [Bool.eq_false_iff.mpr hgc, Bool.false_eq_true, ↓reduceIte]
              by_cases hgVar : (stBody.gprs.get g.toNat).beq (.var (200 + g.toNat)) = true
              · simp only [hgVar, ↓reduceIte]
                rw [hgprP g hg31 (KExpr.beq_eq_true hgVar), hm0.hgprs g hg31]
                exact (evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP _
                  (btreeAll_get _ stPre.gprs hgPre g.toNat hlt)).symm
              · simp only [Bool.eq_false_iff.mpr hgVar, Bool.false_eq_true, ↓reduceIte]
                simp [evalKExpr, envP, mkPostLoopEnv,
                  show ¬(baseOut + 114 + g.toNat < baseOut) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 25) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 50) by omega,
                  show ¬(baseOut + 114 + g.toNat < baseOut + 114) by omega,
                  show baseOut + 114 + g.toNat < baseOut + 146 by omega,
                  show baseOut + 114 + g.toNat - (baseOut + 114) = g.toNat by omega]
        · intro lhs rhs hp
          simp only [buildPostLoopState04, Option.some.injEq, Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩
          simpa [evalKExpr] using hps23
      have hspOut : KSpatial cfg envP (buildPostLoopState04 baseOut rCnt stPre stBody) F =
          ((env0.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env0.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tAPost ∗
            TreeMem (env0.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB
              (stPre.memB.map (evalKExpr env0)) ∗ F) := by
        dsimp only [KSpatial, buildPostLoopState04]; rw [htAPEq, htBPEq]; simp [envP, mkPostLoopEnv]
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

/-! ## 5. Concrete 25-Lane `KSlot` Tables for `B04` `Seg5` (`A1..EB`, Invariants, Clamps) -/

@[expose] def slotsA1 : List KSlot :=
  [.vreg 0, .vreg 28, .vreg 29, .vreg 8, .spillQ 2208, .vreg 19, .vreg 23, .spillQ 1744,
   .vreg 15, .spillQ 1856, .vreg 12, .vreg 26, .vreg 22, .vreg 11, .vreg 13, .vreg 30,
   .vreg 27, .vreg 5, .vreg 10, .vreg 7, .vreg 25, .vreg 24, .vreg 20, .vreg 17, .vreg 18]

@[expose] def slotsA2 : List KSlot :=
  [.vreg 7, .vreg 22, .vreg 28, .vreg 8, .spillQ 2224, .vreg 18, .vreg 2, .vreg 13,
   .vreg 10, .vreg 9, .vreg 14, .vreg 26, .vreg 11, .vreg 30, .vreg 15, .vreg 21,
   .vreg 12, .vreg 25, .vreg 4, .vreg 6, .vreg 24, .vreg 27, .vreg 31, .vreg 17, .vreg 19]

@[expose] def slotsA3 : List KSlot :=
  [.vreg 19, .vreg 3, .vreg 2, .spillQ 1728, .spillQ 1872, .vreg 18, .vreg 1, .spillQ 1712,
   .vreg 8, .vreg 9, .vreg 10, .vreg 11, .vreg 30, .vreg 26, .vreg 12, .vreg 31,
   .vreg 25, .vreg 4, .vreg 13, .vreg 6, .vreg 15, .vreg 23, .vreg 20, .vreg 16, .vreg 21]

@[expose] def slotsB1 : List KSlot :=
  [.vreg 19, .spillQ 1840, .spillQ 2016, .vreg 4, .vreg 17, .vreg 18, .vreg 8, .spillQ 1904,
   .vreg 14, .vreg 22, .vreg 15, .vreg 11, .vreg 30, .vreg 31, .vreg 26, .vreg 12,
   .vreg 25, .vreg 29, .vreg 27, .vreg 6, .vreg 28, .vreg 23, .vreg 20, .vreg 16, .vreg 21]

@[expose] def slotsB2 : List KSlot :=
  [.vreg 7, .vreg 26, .vreg 28, .spillQ 1520, .spillQ 1952, .vreg 22, .vreg 16, .vreg 10,
   .vreg 13, .vreg 15, .vreg 24, .vreg 27, .vreg 25, .vreg 21, .vreg 11, .vreg 9,
   .vreg 20, .vreg 4, .vreg 14, .vreg 2, .vreg 17, .vreg 29, .vreg 8, .vreg 31, .vreg 12]

@[expose] def slotsB3 : List KSlot :=
  [.vreg 9, .spillQ 1792, .spillQ 2000, .vreg 22, .spillQ 1936, .spillQ 2032, .spillQ 1808, .spillQ 1824,
   .spillQ 2048, .spillQ 2144, .vreg 21, .vreg 23, .vreg 11, .vreg 14, .vreg 19, .vreg 6,
   .vreg 17, .vreg 15, .vreg 18, .vreg 30, .vreg 25, .vreg 29, .vreg 13, .vreg 31, .vreg 12]

@[expose] def slotsEA : List KSlot :=
  [.vreg 19, .vreg 15, .spillQ 2016, .vreg 16, .spillQ 2240, .vreg 31, .vreg 24, .vreg 30,
   .vreg 11, .vreg 8, .vreg 9, .vreg 14, .vreg 23, .vreg 25, .vreg 22, .vreg 13,
   .vreg 20, .vreg 10, .vreg 27, .vreg 5, .vreg 12, .vreg 7, .vreg 29, .vreg 17, .vreg 21]

@[expose] def slotsEB : List KSlot :=
  [.vreg 19, .vreg 16, .spillQ 2000, .spillQ 2224, .vreg 13, .spillQ 2032, .vreg 7, .vreg 28,
   .vreg 10, .vreg 15, .vreg 11, .vreg 23, .vreg 9, .vreg 22, .vreg 12, .vreg 24,
   .vreg 30, .vreg 25, .vreg 27, .vreg 6, .vreg 17, .vreg 18, .vreg 31, .vreg 29, .vreg 20]

@[expose] def inv01Slots : List KSlot :=
  [.vreg 19, .vreg 15, .spillQ 2016, .vreg 12, .vreg 22, .vreg 31, .spillQ 1312, .vreg 30,
   .vreg 11, .vreg 13, .vreg 8, .vreg 14, .vreg 21, .vreg 25, .vreg 10, .spillQ 1296,
   .spillQ 1216, .spillQ 1232, .vreg 27, .vreg 28, .spillQ 1152, .vreg 6, .vreg 20, .vreg 17, .vreg 0]

@[expose] def inv2Slots : List KSlot :=
  [.vreg 7, .vreg 1, .spillQ 2000, .spillQ 2224, .spillQ 1936, .vreg 2, .spillQ 1808, .vreg 3,
   .spillQ 2048, .spillQ 2144, .spillQ 1520, .spillQ 1616, .vreg 9, .spillQ 1664, .spillQ 2064, .spillQ 1504,
   .spillQ 1600, .spillQ 1776, .vreg 5, .spillQ 1952, .vreg 24, .spillQ 1344, .spillQ 1360, .vreg 29, .spillQ 2128]

@[expose] def preClamp01Slots : List KSlot :=
  [.vreg 19, .vreg 15, .spillQ 2016, .vreg 12, .vreg 22, .vreg 31, .spillQ 1312, .vreg 30,
   .vreg 11, .vreg 13, .vreg 8, .vreg 14, .vreg 21, .vreg 25, .vreg 10, .spillQ 1296,
   .spillQ 1216, .spillQ 1232, .vreg 27, .vreg 28, .spillQ 1152, .spillQ 1328, .spillQ 1888, .spillQ 2176, .spillQ 2192]

@[expose] def preClamp2Slots : List KSlot :=
  [.vreg 7, .vreg 1, .spillQ 2000, .spillQ 2224, .spillQ 1936, .vreg 2, .spillQ 1808, .vreg 3,
   .spillQ 2048, .spillQ 2144, .spillQ 1520, .spillQ 1616, .vreg 9, .spillQ 1664, .spillQ 2064, .spillQ 1504,
   .spillQ 1600, .spillQ 1776, .vreg 5, .spillQ 1952, .vreg 24, .spillQ 1344, .spillQ 1360, .spillQ 2160, .spillQ 2128]

@[expose] def postExtra01Slots : List KSlot :=
  [.spillQ 1168, .spillQ 1840, .spillQ 2016, .spillQ 1920, .spillQ 2240, .spillQ 1200, .spillQ 1312, .spillQ 1904,
   .spillQ 1968, .spillQ 1984, .spillQ 1184, .spillQ 1248, .spillQ 1264, .spillQ 1280, .spillQ 2112, .spillQ 1296,
   .spillQ 1216, .spillQ 1232, .spillQ 2080, .spillQ 2096, .spillQ 1152, .spillQ 1328, .spillQ 1888, .spillQ 2176, .spillQ 2192]

@[expose] def postExtra2Slots : List KSlot :=
  [.vreg 19, .vreg 1, .spillQ 2000, .spillQ 2224, .vreg 13, .vreg 2, .vreg 10, .vreg 28,
   .vreg 15, .vreg 0, .spillQ 1520, .vreg 23, .vreg 9, .vreg 22, .vreg 12, .spillQ 1504,
   .vreg 30, .vreg 25, .vreg 27, .spillQ 1952, .vreg 17, .vreg 18, .vreg 31, .vreg 29, .vreg 20]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop
