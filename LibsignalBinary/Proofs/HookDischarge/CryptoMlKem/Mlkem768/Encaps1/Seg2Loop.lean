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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Anf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step

/-!
# `encapsulate1_serialized` (`B03`) — 24-Round 1-Lane & 2-Lane NEON Keccak Loop Verifier (`Seg2Loop`)

`BTree` extensionality (`btree_ext_get`), 4-constructor `KSlot` accessors (`vreg`, `spillQ`,
`vregLo`, `spillD`), round-init state (`mkLoopInitState_matches`), and unified 24-round symbolic
loop verifier (`checkKeccakLoop03`, `sepWP_of_keccakLoop24`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakF1600 keccakF1600Round)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600Round_getD keccakF1600Round_size keccakRunFrom keccakRunFrom_24
  keccakRunFrom_step keccakRunFrom_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Anf (
  anf_eq_keccakRoundLane checkAnfLane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KPFlag KSlot KState evalKExpr fetchWordTree03 runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem fetch_blk03_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KConstsLoOpt KPFlagMatches KSpatial KStateMatches evalMemTree setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2b)

/-! ## 1. `BTree` Extensionality & 4-Constructor `KSlot` Accessors -/

theorem btree_ext_get {α : Type} :
    ∀ {d : Nat} {t1 t2 : BTree α d}, (∀ i, i < 2 ^ d → t1.get i = t2.get i) → t1 = t2
  | 0, .leaf _, .leaf _, h => congrArg BTree.leaf (h 0 (by decide))
  | _ + 1, .node lo1 hi1, .node lo2 hi2, h => by
      have hlo : lo1 = lo2 := btree_ext_get fun j hj => by
        simpa [BTree.get, show (2 * j % 2 == 0) = true from beq_iff_eq.mpr (by omega),
          show 2 * j / 2 = j by omega] using h (2 * j) (by rw [Nat.pow_succ]; omega)
      have hhi : hi1 = hi2 := btree_ext_get fun j hj => by
        simpa [BTree.get, show ((2 * j + 1) % 2 == 0) = false from beq_false_of_ne (by omega),
          show (2 * j + 1) / 2 = j by omega] using h (2 * j + 1) (by rw [Nat.pow_succ]; omega)
      rw [hlo, hhi]

@[expose] def btreeKExprBeq : {d : Nat} → BTree KExpr d → BTree KExpr d → Bool
  | 0, .leaf a, .leaf b => a.beq b
  | _ + 1, .node l1 r1, .node l2 r2 => btreeKExprBeq l1 l2 && btreeKExprBeq r1 r2

theorem btreeKExprBeq_eq_true :
    ∀ {d : Nat} {t1 t2 : BTree KExpr d}, btreeKExprBeq t1 t2 = true → t1 = t2
  | 0, .leaf _, .leaf _, h => congrArg BTree.leaf (KExpr.beq_eq_true h)
  | _ + 1, .node _ _, .node _ _, h => by
      simp only [btreeKExprBeq, Bool.and_eq_true] at h
      rw [btreeKExprBeq_eq_true h.1, btreeKExprBeq_eq_true h.2]

@[expose] def slotValid (cfg : KCfg) : KSlot → Bool
  | .vreg r | .vregLo r => Nat.blt r 32
  | .spillQ off =>
      Nat.beq (off % 8) 0 && Nat.ble cfg.offA off &&
        Nat.ble (off + 16) (cfg.offA + 8 * cfg.lenA) && Nat.ble ((off - cfg.offA) / 8 + 2) 512
  | .spillD off =>
      Nat.beq (off % 8) 0 && Nat.ble cfg.offA off &&
        Nat.ble (off + 8) (cfg.offA + 8 * cfg.lenA) && Nat.ble ((off - cfg.offA) / 8 + 1) 512

@[expose] def slotModeOk (isPair : Bool) : KSlot → Bool
  | .vreg _ | .spillQ _ => isPair
  | .vregLo _ | .spillD _ => !isPair

@[expose] def readSlot (cfg : KCfg) (st : KState) : KSlot → KExpr × KExpr
  | .vreg r => st.vregs.get r
  | .spillQ off => let idx := (off - cfg.offA) / 8; (st.memA.get idx, st.memA.get (idx + 1))
  | .vregLo r => ((st.vregs.get r).1, .const64 0#64)
  | .spillD off => (st.memA.get ((off - cfg.offA) / 8), .const64 0#64)

@[expose] def writeSlot (cfg : KCfg) (st : KState) (sl : KSlot) (p : KExpr × KExpr) : KState :=
  match sl with
  | .vreg r => { st with vregs := st.vregs.set r p }
  | .spillQ off =>
      let idx := (off - cfg.offA) / 8
      { st with memA := (st.memA.set idx p.1).set (idx + 1) p.2 }
  | .vregLo r => { st with vregs := st.vregs.set r (p.1, (st.vregs.get r).2) }
  | .spillD off => { st with memA := st.memA.set ((off - cfg.offA) / 8) p.1 }

@[expose] def slotHolds (cfg : KCfg) (s : State) (tA : BTree (BitVec 64) 9)
    (sl : KSlot) (vLo vHi : BitVec 64) : Prop :=
  match sl with
  | .vreg r => r < 32 ∧ s.readVReg128 (BitVec.ofNat 5 r) = vHi ++ vLo
  | .spillQ off =>
      let idx := (off - cfg.offA) / 8
      idx + 1 < 512 ∧ tA.get idx = vLo ∧ tA.get (idx + 1) = vHi
  | .vregLo r => r < 32 ∧ (s.readVReg128 (BitVec.ofNat 5 r)).truncate 64 = vLo
  | .spillD off => let idx := (off - cfg.offA) / 8; idx < 512 ∧ tA.get idx = vLo

theorem slotHolds_of_not_pair {cfg : KCfg} {s : State} {tA : BTree (BitVec 64) 9}
    {sl : KSlot} {vLo v1 v2 : BitVec 64} (hm : slotModeOk false sl = true)
    (h : slotHolds cfg s tA sl vLo v1) : slotHolds cfg s tA sl vLo v2 := by
  cases sl <;> simp [slotModeOk] at hm <;> exact h

theorem vreg128_repack (v : BitVec 128) : ((v >>> 64).truncate 64) ++ v.truncate 64 = v := by bv_bits
theorem truncate64_append (hi lo : BitVec 64) : (hi ++ lo).truncate 64 = lo := by bv_bits
theorem ushr64_truncate64_append (hi lo : BitVec 64) : ((hi ++ lo) >>> 64).truncate 64 = hi := by bv_bits

/-! ## 2. Round-Init Symbolic State (`mkLoopInitState`) & Concrete Matching -/

@[expose] def mkBaseState (rCnt : BitVec 5) : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)))
    gprs := ((BTree.ofFn 5 (fun g => .var (200 + g))).set 19 (.rcAdd 0#64)).set rCnt.toNat .rcLoopOff
    memA := BTree.ofFn 9 (fun i => .var (300 + i))
    memB := BTree.ofFn 9 (fun i => .var (900 + i))
    pstateFlag := none }

@[expose] def writeSlotsFrom (cfg : KCfg) : Nat → List KSlot → KState → KState
  | _, [], st => st
  | idx, sl :: rest, st =>
      writeSlotsFrom cfg (idx + 1) rest (writeSlot cfg st sl (.var idx, .var (25 + idx)))

@[expose] def mkLoopInitState (cfg : KCfg) (rCnt : BitVec 5) (slots : List KSlot) : KState :=
  writeSlotsFrom cfg 0 slots (mkBaseState rCnt)

@[expose] def mkRoundEnv (sp rcBase : BitVec 64) (r : Nat) (sA sB : KeccakState)
    (s : State) (tA tB : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp, rcBase := rcBase, rLoop := r
    vars := fun id =>
      if id < 25 then sA.getD id 0#64
      else if id < 50 then sB.getD (id - 25) 0#64
      else if id < 164 then
        let k := id - 100
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 }

theorem mkBaseState_matches {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s : State} {tA tB : BTree (BitVec 64) 9} {rCnt : BitVec 5}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 19#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r))
    (hne19 : rCnt ≠ 19#5) :
    let env := mkRoundEnv sp rcBase r sA sB s tA tB
    KStateMatches env (mkBaseState rCnt) s ∧
      evalMemTree env (mkBaseState rCnt).memA = tA ∧
      evalMemTree env (mkBaseState rCnt).memB = tB := by
  intro env
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_, ?_⟩
  · intro vr
    simp only [mkBaseState]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
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
    simp only [mkBaseState]; rw [BTree.get_set _ rCnt.toNat _ rCnt.isLt g.toNat g.isLt]
    by_cases hgc : g.toNat = rCnt.toNat
    · have heq := BitVec.eq_of_toNat_eq hgc; subst heq; simp [evalKExpr, env, mkRoundEnv, hcnt]
    · simp only [hgc, ↓reduceIte]; rw [BTree.get_set _ 19 _ (by decide) g.toNat g.isLt]
      by_cases hg19 : g.toNat = 19
      · have heq : g = 19#5 := BitVec.eq_of_toNat_eq hg19
        subst heq; simp [evalKExpr, env, mkRoundEnv, hrc]
      · simp only [hg19, ↓reduceIte]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
        have hlt := g.isLt
        have hb : ¬(200 + g.toNat < 25) ∧ ¬(200 + g.toNat < 50) ∧ ¬(200 + g.toNat < 164) ∧
            200 + g.toNat < 232 ∧ 200 + g.toNat - 200 = g.toNat :=
          ⟨by omega, by omega, by omega, by omega, by omega⟩
        simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [evalMemTree, mkBaseState]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
        300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]
  · apply btree_ext_get; intro i hi
    simp only [evalMemTree, mkBaseState]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    have hb : ¬(900 + i < 25) ∧ ¬(900 + i < 50) ∧ ¬(900 + i < 164) ∧ ¬(900 + i < 232) ∧
        ¬(900 + i < 812) ∧ 900 + i < 1412 ∧ 900 + i - 900 = i :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    simp [evalKExpr, env, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2.1, hb.2.2.2.2.2.2]

theorem writeSlot_preserves_matches {cfg : KCfg} {env : KEnv} {st : KState}
    {s : State} {tA : BTree (BitVec 64) 9} {sl : KSlot} {p : KExpr × KExpr}
    (hm : KStateMatches env st s) (htA : evalMemTree env st.memA = tA)
    (hsl : slotHolds cfg s tA sl (evalKExpr env p.1) (evalKExpr env p.2)) :
    KStateMatches env (writeSlot cfg st sl p) s ∧
      evalMemTree env (writeSlot cfg st sl p).memA = tA ∧
      (writeSlot cfg st sl p).memB = st.memB := by
  cases sl with
  | vreg vr =>
      rcases hsl with ⟨hvr, hv⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpflag⟩, htA, rfl⟩
      intro r; simp only [writeSlot]
      rw [BTree.get_set st.vregs vr p (by change vr < 32; exact hvr) r.toNat r.isLt]
      by_cases heq : r.toNat = vr
      · simp only [heq, ↓reduceIte]
        have hr : r = BitVec.ofNat 5 vr :=
          BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hvr])
        rwa [hr]
      · simp only [heq, ↓reduceIte]; exact hm.hvregs r
  | spillQ off =>
      rcases hsl with ⟨hidx, hlo, hhi⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩, ?_, rfl⟩
      apply btree_ext_get; intro i hi
      let idx := (off - cfg.offA) / 8
      have hidx0 : idx < 2 ^ 9 := by change idx < 512; omega
      have hidx1 : idx + 1 < 2 ^ 9 := hidx
      simp only [writeSlot, evalMemTree]
      rw [BTree.get_map, BTree.get_set _ (idx + 1) p.2 hidx1 i hi]
      by_cases hi1 : i = idx + 1
      · subst hi1; simp only [↓reduceIte]; exact hhi.symm
      · simp only [hi1, ↓reduceIte]; rw [BTree.get_set _ idx p.1 hidx0 i hi]
        by_cases hi0 : i = idx
        · subst hi0; simp only [↓reduceIte]; exact hlo.symm
        · simp only [hi0, ↓reduceIte]; rw [← htA, evalMemTree, BTree.get_map]
  | vregLo vr =>
      rcases hsl with ⟨hvr, hv⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpflag⟩, htA, rfl⟩
      intro r; simp only [writeSlot]
      rw [BTree.get_set st.vregs vr (p.1, (st.vregs.get vr).2) (by change vr < 32; exact hvr)
          r.toNat r.isLt]
      by_cases heq : r.toNat = vr
      · simp only [heq, ↓reduceIte]
        have hr : r = BitVec.ofNat 5 vr :=
          BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hvr])
        have hhi : ((s.readVReg128 r) >>> 64).truncate 64 =
            evalKExpr env (st.vregs.get vr).2 := by
          rw [hm.hvregs r, heq, ushr64_truncate64_append]
        rw [← hhi, ← hv, ← hr, vreg128_repack]
      · simp only [heq, ↓reduceIte]; exact hm.hvregs r
  | spillD off =>
      rcases hsl with ⟨hidx, hlo⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩, ?_, rfl⟩
      apply btree_ext_get; intro i hi
      let idx := (off - cfg.offA) / 8
      simp only [writeSlot, evalMemTree]
      rw [BTree.get_map, BTree.get_set _ idx p.1 hidx i hi]
      by_cases hi0 : i = idx
      · subst hi0; simp only [↓reduceIte]; exact hlo.symm
      · simp only [hi0, ↓reduceIte]; rw [← htA, evalMemTree, BTree.get_map]

private theorem writeSlotsFrom_matches {cfg : KCfg} {env : KEnv}
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

theorem mkLoopInitState_matches {cfg : KCfg} {sp rcBase : BitVec 64} {r : Nat}
    {sA sB : KeccakState} {s : State} {tA tB : BTree (BitVec 64) 9}
    {rCnt : BitVec 5} {slots : List KSlot}
    (hlen : slots.length = 25) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hrc : s.readReg64 (.gpr 19#5) = rcBase)
    (hcnt : s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r))
    (hne19 : rCnt ≠ 19#5)
    (hslots : ∀ idx, idx < 25 →
      slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) :
    KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState cfg rCnt slots) s ∧
      evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState cfg rCnt slots).memA = tA ∧
      evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) (mkLoopInitState cfg rCnt slots).memB = tB ∧
      (mkLoopInitState cfg rCnt slots).memB = (mkBaseState rCnt).memB := by
  rcases mkBaseState_matches (sA := sA) (sB := sB) (tA := tA) (tB := tB)
    hsp hspA hrc hcnt hne19 with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var k) = sA.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, mkRoundEnv, hk]
  have hv25 : ∀ k, k < 25 →
      evalKExpr (mkRoundEnv sp rcBase r sA sB s tA tB) (.var (25 + k)) = sB.getD k 0#64 :=
    fun k hk => by
      simp [evalKExpr, mkRoundEnv, show ¬(25 + k < 25) by omega,
        show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  rcases writeSlotsFrom_matches (cfg := cfg) hv0 hv25 slots 0 (mkBaseState rCnt) (by omega)
    (fun j hj => by simpa using hslots j (by omega)) hm0 htA0 rfl with ⟨hmF, htAF, hmBF⟩
  unfold mkLoopInitState
  exact ⟨hmF, htAF, by rw [hmBF, htB0], hmBF⟩

/-! ## 3. 24-Round Symbolic `Keccak-f[1600]` Loop Verifier (`checkKeccakLoop03`) -/

theorem readSlot_holds {cfg : KCfg} {env : KEnv} {st : KState} {sf : State} {sl : KSlot}
    (hv : slotValid cfg sl = true) (hm : KStateMatches env st sf) :
    slotHolds cfg sf (evalMemTree env st.memA) sl
      (evalKExpr env (readSlot cfg st sl).1) (evalKExpr env (readSlot cfg st sl).2) := by
  cases sl with
  | vreg r =>
      simp only [slotValid, Nat.blt_eq] at hv
      have h := hm.hvregs (BitVec.ofNat 5 r)
      have hto : (BitVec.ofNat 5 r).toNat = r := Nat.mod_eq_of_lt hv
      exact ⟨hv, by simpa [readSlot, hto] using h⟩
  | spillQ off =>
      simp only [slotValid, Bool.and_eq_true, Nat.ble_eq] at hv
      exact ⟨by omega, by simp [readSlot, evalMemTree, BTree.get_map],
        by simp [readSlot, evalMemTree, BTree.get_map]⟩
  | vregLo r =>
      simp only [slotValid, Nat.blt_eq] at hv
      have h := hm.hvregs (BitVec.ofNat 5 r)
      have hto : (BitVec.ofNat 5 r).toNat = r := Nat.mod_eq_of_lt hv
      exact ⟨hv, by rw [h, hto, truncate64_append]; rfl⟩
  | spillD off =>
      simp only [slotValid, Bool.and_eq_true, Nat.ble_eq] at hv
      exact ⟨by omega, by simp [readSlot, evalMemTree, BTree.get_map]⟩

private theorem roundEnv_preserved_gpr {sp rcBase : BitVec 64} {r : Nat} {sA sB : KeccakState}
    {s sm : State} {tA tB : BTree (BitVec 64) 9} {stB : KState}
    (hmB : KStateMatches (mkRoundEnv sp rcBase r sA sB s tA tB) stB sm)
    {g : BitVec 5} (hg31 : g ≠ 31#5) (hgVar : stB.gprs.get g.toNat = .var (200 + g.toNat)) :
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
    (evalMemTree (mkRoundEnv sp rcBase r sA sB s tA tB) stB.memA).get i = tA.get i := by
  rw [evalMemTree, BTree.get_map, hmemVar]
  have hb : ¬(300 + i < 25) ∧ ¬(300 + i < 50) ∧ ¬(300 + i < 164) ∧ ¬(300 + i < 232) ∧
      300 + i < 812 ∧ 300 + i - 300 = i := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp [evalKExpr, mkRoundEnv, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]

@[expose] def isLoopDone : Option KPFlag → Bool
  | some .loopDone => true
  | _ => false

@[expose] def checkKeccakLoop03 (cfg : KCfg) (isPair : Bool) (wHead nBody : Nat)
    (rCnt : BitVec 5) (slots : List KSlot) : Option KState :=
  if Nat.beq slots.length 25 && slots.all (fun sl => slotValid cfg sl && slotModeOk isPair sl) &&
     (rCnt != 19#5) && (rCnt != 31#5) &&
     Nat.ble 330 wHead && Nat.ble (wHead + nBody + 1) 3237 then
    match fetchWordTree03 (wHead + nBody) with
    | some (.bCond .NE disp) =>
        if disp == 0#64 - BitVec.ofNat 64 (4 * nBody) then
          match runKRange cfg wHead nBody (mkLoopInitState cfg rCnt slots) with
          | none => none
          | some stBody =>
              if isLoopDone stBody.pstateFlag &&
                 (stBody.gprs.get rCnt.toNat).beq .rcLoopNext &&
                 (stBody.gprs.get 19).beq (.rcAdd 0#64) &&
                 btreeKExprBeq stBody.memB (mkBaseState rCnt).memB &&
                 (List.range 25).all (fun idx =>
                   let (eLo, eHi) := readSlot cfg stBody (slots.getD idx (.vreg 0))
                   checkAnfLane eLo 0 idx && (!isPair || checkAnfLane eHi 25 idx))
              then some stBody else none
        else none
    | _ => none
  else none

private theorem loop_done_ne_of_lt23 {r : Nat} (hr : r < 23) :
    BitVec.ofNat 64 (8 * r) + 8#64 ≠ 192#64 := by
  intro h; have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1; omega

theorem sepWP_of_keccakLoop24 [MlKemPlacement] {b tgt sp rcBase : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {isPair : Bool}
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {stBody : KState}
    (hchk : checkKeccakLoop03 cfg isPair wHead nBody rCnt slots = some stBody)
    {sA0 sB0 : KeccakState} (hsA0 : sA0.size = 25) (hsB0 : sB0.size = 25)
    {s0 : State} {tA0 tB0 : BTree (BitVec 64) 9} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * wHead)) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hrc0 : s0.readReg64 (.gpr 19#5) = rcBase) (hcnt0 : s0.readReg64 (.gpr rCnt) = 0#64)
    (hslots0 : ∀ idx, idx < 25 →
      slotHolds cfg s0 tA0 (slots.getD idx (.vreg 0)) (sA0.getD idx 0#64) (sB0.getD idx 0#64))
    (hnext : ∀ (sf : State) (env23 : KEnv),
      sf.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) → sf.status = .Running →
      sf.sp = sp → sf.spAligned = true → sf.readReg64 (.gpr 19#5) = rcBase →
      sf.readReg64 (.gpr rCnt) = 192#64 → sf.pstate = subsPState64 192#64 192#64 →
      (∀ g : BitVec 5, g ≠ 31#5 → stBody.gprs.get g.toNat = .var (200 + g.toNat) →
        sf.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
      (∀ vr : BitVec 5,
        stBody.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) →
        sf.readVReg128 vr = s0.readVReg128 vr) →
      (∀ i, i < 512 → stBody.memA.get i = .var (300 + i) →
        (evalMemTree env23 stBody.memA).get i = tA0.get i) →
      (∀ e idx, idx < 25 → checkAnfLane e 0 idx = true →
        evalKExpr env23 e = (keccakF1600 sA0).getD idx 0#64) →
      (isPair = true → ∀ e idx, idx < 25 → checkAnfLane e 25 idx = true →
        evalKExpr env23 e = (keccakF1600 sB0).getD idx 0#64) →
      KStateMatches env23 stBody sf →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt sf
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
          (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env23 stBody.memA) ∗
            (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
        (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA0 ∗
          (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) post oom := by
  unfold checkKeccakLoop03 at hchk
  split at hchk; case isFalse => cases hchk
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨hlen, hslVal⟩, hne19⟩, hne31⟩, hwLo⟩, hwHi⟩
  cases hfw : fetchWordTree03 (wHead + nBody) with
  | none => simp [hfw] at hchk
  | some inst =>
      simp only [hfw] at hchk
      cases inst <;> (try dsimp only at hchk) <;> try cases hchk
      rename_i cond disp
      cases cond <;> (try dsimp only at hchk) <;> try cases hchk
      split at hchk; case isFalse => cases hchk
      case isTrue hdispB =>
      have hdisp : disp = 0#64 - BitVec.ofNat 64 (4 * nBody) := beq_iff_eq.mp hdispB
      cases hrunB : runKRange cfg wHead nBody (mkLoopInitState cfg rCnt slots) with
      | none => simp [hrunB] at hchk
      | some stB =>
          simp only [hrunB] at hchk
          split at hchk; case isFalse => cases hchk
          case isTrue hpost =>
          simp only [Option.some.injEq] at hchk; subst hchk
          simp only [Bool.and_eq_true] at hpost
          rcases hpost with ⟨⟨⟨⟨hpfB, hcntB⟩, hrcB⟩, hmemBB⟩, hanfB⟩
          have hpf : stB.pstateFlag = some .loopDone := by
            cases hp : stB.pstateFlag with
            | none => simp [isLoopDone, hp] at hpfB
            | some pf => cases pf <;> simp [isLoopDone, hp] at hpfB ⊢
          have hcntNext : stB.gprs.get rCnt.toNat = .rcLoopNext := KExpr.beq_eq_true hcntB
          have hrcNext : stB.gprs.get 19 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
          have hmemBEq : stB.memB = (mkBaseState rCnt).memB := btreeKExprBeq_eq_true hmemBB
          have hslValIdx : ∀ idx, idx < 25 →
              slotValid cfg (slots.getD idx (.vreg 0)) = true ∧
                slotModeOk isPair (slots.getD idx (.vreg 0)) = true := fun idx hidx => by
            have hlt : idx < slots.length := by omega
            simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
            simpa [Bool.and_eq_true] using List.all_eq_true.mp hslVal _ (List.getElem_mem hlt)
          have hanfIdx : ∀ idx, idx < 25 →
              checkAnfLane (readSlot cfg stB (slots.getD idx (.vreg 0))).1 0 idx = true ∧
                (isPair = true → checkAnfLane (readSlot cfg stB (slots.getD idx (.vreg 0))).2 25 idx = true) :=
            fun idx hidx => by
              have h := List.all_eq_true.mp hanfB idx (List.mem_range.mpr hidx)
              simp only [Bool.and_eq_true] at h; exact ⟨h.1, fun hp => by simpa [hp] using h.2⟩
          suffices ∀ (rem r : Nat) (sA sB : KeccakState) (s : State) (tA : BTree (BitVec 64) 9),
              r + (rem + 1) = 24 → sA.size = 25 → sB.size = 25 →
              keccakRunFrom r sA = keccakF1600 sA0 → (isPair = true → keccakRunFrom r sB = keccakF1600 sB0) →
              s.pc = b + BitVec.ofNat 64 (4 * wHead) → s.status = .Running →
              s.sp = sp → s.spAligned = true → s.readReg64 (.gpr 19#5) = rcBase →
              s.readReg64 (.gpr rCnt) = BitVec.ofNat 64 (8 * r) →
              (∀ idx, idx < 25 → slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sA.getD idx 0#64) (sB.getD idx 0#64)) →
              (∀ g : BitVec 5, g ≠ 31#5 → stB.gprs.get g.toNat = .var (200 + g.toNat) → s.readReg64 (.gpr g) = s0.readReg64 (.gpr g)) →
              (∀ vr : BitVec 5, stB.vregs.get vr.toNat = (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1)) → s.readVReg128 vr = s0.readVReg128 vr) →
              (∀ i, i < 512 → stB.memA.get i = .var (300 + i) → tA.get i = tA0.get i) →
              SepWP (blkPC03.rebase b (fun _ => none)) tgt s
                ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
                  (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                    (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) post oom by
            exact this 23 0 sA0 sB0 s0 tA0 rfl hsA0 hsB0 (keccakRunFrom_zero sA0)
              (fun _ => keccakRunFrom_zero sB0) hpc0 hrun0 hsp0 hspA0 hrc0 hcnt0 hslots0
              (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
          intro rem
          induction rem with
          | zero =>
              intro r sA sB s tA hrSum _hsA _hsB hrunA hrunB_st hpc hrun hsp hspA hrc hcnt
                hslots hgprP hvregP hmemAP
              have hr23 : r = 23 := by omega
              subst hr23
              let env23 := mkRoundEnv sp rcBase 23 sA sB s tA tB0
              rcases mkLoopInitState_matches (tB := tB0) hlen hsp hspA hrc hcnt hne19 hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg env23 (mkLoopInitState cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
                    (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                      (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [env23, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_runKRange_seg2b hv (by simp [env23, mkRoundEnv]) hwLo (by omega) hpc hrun hmI hrunB ?_
              intro sm hmpc hmrun hmB
              have htBB : evalMemTree env23 stB.memB = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk03_seg2b (b := b) (by omega) (by omega) hfw
              have hps23 : sm.pstate = subsPState64 192#64 192#64 := by
                have hp := hmB.hpflag; rw [hpf] at hp; simpa [KPFlagMatches, env23, mkRoundEnv] using hp
              have hzNe : ConditionHolds .NE sm.pstate = false := by
                rw [hps23, conditionHolds_ne_subsPState64]; decide
              refine SepWP.step_pure hmpc hmrun hfetchBr (s' := sm.advancePC) ?_ rfl ?_
              · rw [setPC_self hmpc]; simp [Program.evalInst, execInstWithSvc, hzNe]
              · have hpcEnd : sm.advancePC.pc = b + BitVec.ofNat 64 (4 * (wHead + nBody + 1)) := by
                  simp only [State.advancePC, hmpc]; bv_omega
                have hspEnd : KSpatial cfg env23 stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
                      (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env23 stB.memA) ∗
                        (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [env23, mkRoundEnv]
                rw [hspEnd]
                have hA23 : keccakF1600Round sA (keccakRcAt 23) = keccakF1600 sA0 := by
                  rwa [keccakRunFrom_step 23 (by decide) sA, keccakRunFrom_24] at hrunA
                refine hnext sm.advancePC env23 hpcEnd hmrun hmB.hsp hmB.hsp_al ?_ ?_ hps23
                  (fun g hg31 hgv => (roundEnv_preserved_gpr hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv => (roundEnv_preserved_memA sp rcBase 23 sA sB s tA tB0 hi hmv).trans (hmemAP i hi hmv))
                  ?_ ?_ ⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hpflag⟩
                · have h := hmB.hgprs 19#5 (by decide); change _ = evalKExpr env23 (stB.gprs.get 19) at h
                  rw [hrcNext] at h; simpa [evalKExpr, env23, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hne31; rw [hcntNext] at h; simpa [evalKExpr, env23, mkRoundEnv] using h
                · intro e idx hidx hanfE
                  have hv0 : ∀ j, j < 25 → env23.vars (0 + j) = sA.getD j 0#64 := fun j hj => by simp [env23, mkRoundEnv, hj]
                  rw [anf_eq_keccakRoundLane hv0 hanfE, ← hA23]; exact (keccakF1600Round_getD sA (keccakRcAt 23) hidx).symm
                · intro hp e idx hidx hanfE
                  have hB23 : keccakF1600Round sB (keccakRcAt 23) = keccakF1600 sB0 := by
                    have hrB := hrunB_st hp; rwa [keccakRunFrom_step 23 (by decide) sB, keccakRunFrom_24] at hrB
                  have hv25 : ∀ j, j < 25 → env23.vars (25 + j) = sB.getD j 0#64 := fun j hj => by
                    simp [env23, mkRoundEnv, show ¬(25 + j < 25) by omega, show 25 + j < 50 by omega, show 25 + j - 25 = j by omega]
                  rw [anf_eq_keccakRoundLane hv25 hanfE, ← hB23]; exact (keccakF1600Round_getD sB (keccakRcAt 23) hidx).symm
          | succ rem' ih =>
              intro r sA sB s tA hrSum _hsA _hsB hrunA hrunB_st hpc hrun hsp hspA hrc hcnt
                hslots hgprP hvregP hmemAP
              have hrLt23 : r < 23 := by omega
              let envR := mkRoundEnv sp rcBase r sA sB s tA tB0
              rcases mkLoopInitState_matches (tB := tB0) hlen hsp hspA hrc hcnt hne19 hslots
                with ⟨hmI, htAI, htBI, hmBInit⟩
              have hspEq : KSpatial cfg envR (mkLoopInitState cfg rCnt slots) F =
                  ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
                    (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tA ∗
                      (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) := by
                dsimp only [KSpatial]; rw [htAI, htBI]; simp [envR, mkRoundEnv]
              rw [← hspEq]
              refine sepWP_runKRange_seg2b hv (by simp [envR, mkRoundEnv]; omega) hwLo (by omega) hpc hrun hmI hrunB ?_
              intro sm hmpc hmrun hmB
              have htBB : evalMemTree envR stB.memB = tB0 := by rw [hmemBEq, ← hmBInit, htBI]
              have hfetchBr := fetch_blk03_seg2b (b := b) (by omega) (by omega) hfw
              have hzNe : ConditionHolds .NE sm.pstate = true := by
                have hp := hmB.hpflag; rw [hpf] at hp; simp only [KPFlagMatches, envR, mkRoundEnv] at hp
                rw [hp, conditionHolds_ne_subsPState64, bne_iff_ne]; exact loop_done_ne_of_lt23 hrLt23
              have hpcBack : sm.pc + disp = b + BitVec.ofNat 64 (4 * wHead) := by rw [hmpc, hdisp]; bv_omega
              refine SepWP.step_pure hmpc hmrun hfetchBr (s' := sm.setPC (b + BitVec.ofNat 64 (4 * wHead))) ?_ rfl ?_
              · rw [setPC_self hmpc]; simp only [Program.evalInst, execInstWithSvc, hzNe, ↓reduceIte]; rw [hpcBack]
              · have hspNext : KSpatial cfg envR stB F =
                    ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt sp cfg.hasConstsLo ∗
                      (TreeMem (sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree envR stB.memA) ∗
                        (TreeMem (sp + BitVec.ofNat 64 cfg.offB) cfg.lenB tB0 ∗ F)))) := by
                  dsimp only [KSpatial]; rw [htBB]; simp [envR, mkRoundEnv]
                rw [hspNext]
                let sA' := keccakF1600Round sA (keccakRcAt r)
                let sB' := if isPair then keccakF1600Round sB (keccakRcAt r) else sB
                refine ih (r + 1) sA' sB' (sm.setPC (b + BitVec.ofNat 64 (4 * wHead)))
                  (evalMemTree envR stB.memA) (by omega) (keccakF1600Round_size sA _)
                  (by dsimp only [sB']; split <;> [exact keccakF1600Round_size sB _; exact _hsB])
                  (by rwa [keccakRunFrom_step r (by omega) sA] at hrunA)
                  (fun hp => by
                    have hrB := hrunB_st hp; simp only [sB', hp, ↓reduceIte]
                    rwa [keccakRunFrom_step r (by omega) sB] at hrB)
                  rfl hmrun hmB.hsp hmB.hsp_al ?_ ?_ ?_
                  (fun g hg31 hgv => (roundEnv_preserved_gpr hmB hg31 hgv).trans (hgprP g hg31 hgv))
                  (fun vr hvrv => (roundEnv_preserved_vreg hmB hvrv).trans (hvregP vr hvrv))
                  (fun i hi hmv =>
                    (roundEnv_preserved_memA sp rcBase r sA sB s tA tB0 hi hmv).trans
                      (hmemAP i hi hmv))
                · have h := hmB.hgprs 19#5 (by decide)
                  change _ = evalKExpr envR (stB.gprs.get 19) at h
                  rw [hrcNext] at h; simpa [evalKExpr, envR, mkRoundEnv] using h
                · have h := hmB.hgprs rCnt hne31
                  rw [hcntNext] at h; change sm.readReg64 (.gpr rCnt) = _
                  rw [h]; simp only [evalKExpr, envR, mkRoundEnv]; bv_omega
                · intro idx hidx
                  rcases hslValIdx idx hidx with ⟨hsvI, hsmI⟩
                  have hsl := readSlot_holds hsvI
                    (⟨hmB.hsp, hmB.hsp_al, hmB.hvregs, hmB.hgprs, hmB.hpflag⟩ :
                      KStateMatches envR stB (sm.setPC (b + BitVec.ofNat 64 (4 * wHead))))
                  rcases hanfIdx idx hidx with ⟨hLoAnf, hHiAnf⟩
                  have hv0 : ∀ j, j < 25 → envR.vars (0 + j) = sA.getD j 0#64 :=
                    fun j hj => by simp [envR, mkRoundEnv, hj]
                  have hLoEq : evalKExpr envR (readSlot cfg stB (slots.getD idx (.vreg 0))).1 =
                      sA'.getD idx 0#64 := by
                    rw [anf_eq_keccakRoundLane hv0 hLoAnf]
                    exact (keccakF1600Round_getD sA (keccakRcAt r) hidx).symm
                  by_cases hp : isPair = true
                  · have hv25 : ∀ j, j < 25 → envR.vars (25 + j) = sB.getD j 0#64 := fun j hj => by
                      simp [envR, mkRoundEnv, show ¬(25 + j < 25) by omega,
                        show 25 + j < 50 by omega, show 25 + j - 25 = j by omega]
                    have hHiEq : evalKExpr envR (readSlot cfg stB (slots.getD idx (.vreg 0))).2 =
                        sB'.getD idx 0#64 := by
                      simp only [sB', hp, ↓reduceIte, anf_eq_keccakRoundLane hv25 (hHiAnf hp)]
                      exact (keccakF1600Round_getD sB (keccakRcAt r) hidx).symm
                    rwa [hLoEq, hHiEq] at hsl
                  · rw [Bool.eq_false_iff.mpr hp] at hsmI
                    exact slotHolds_of_not_pair hsmI (hLoEq ▸ hsl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop
