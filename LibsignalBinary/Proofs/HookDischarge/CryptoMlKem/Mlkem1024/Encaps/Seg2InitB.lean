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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Row Init Slice B (`+0x0fa8 .. +0x25c0`, `Seg2InitB`)

Proves the 4-loop (`L3`–`L6`) 3-block SHAKE-128 squeeze (`seg2_initB_ok`, `+0x0fa8 → +0x25c0`)
and `slotExprsLo`/`slotExprsHi` symbolic helpers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakAbsorb keccakExtractRate keccakF1600 keccakPermuteN keccakSqueezeBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600_size keccakState_eq_of_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (blkPC07 blkPl07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KSpatial KStateMatches SepWP.of_memRegion_btreeMem btreeBytesFrom btreeBytesFrom_split evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get readSlot slotHolds vreg128_repack)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  btreeBytesFrom_eq_extractRate_21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memB extendLoopVars exprVarsOk
  keccakAbsorb_rowSeed progBases rowSeed runAndCheckKProg sepWP_of_runAndCheckKProg specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowCalleeGprs cfgB cfgB_valid slotsFa8_01 slotsFa8_23 slotsL3 slotsL4 slotsL5 slotsL6
  slotsMidInit01 slotsMidInit23)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  RowInitAPost calleeGprExpr checkCalleeGprsPreserved checkHeaderPreserved checkOutSlots
  checked_calleeGprs checked_headerOk checked_outSlots envInitA eval_headerMemAExpr headerMemAExpr stInitA_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast (runAndCheckKProg_of_fast)

/-! ## 1. `keccakPermuteN` & `slotExprs` Helpers -/

theorem keccakPermuteN_succ_right : ∀ (n : Nat) (s : KeccakState),
    keccakF1600 (keccakPermuteN n s) = keccakPermuteN (n + 1) s
  | 0, _ => rfl
  | n + 1, s => keccakPermuteN_succ_right n (keccakF1600 s)

theorem keccakPermuteN_size : ∀ (n : Nat) {s : KeccakState}, s.size = 25 → (keccakPermuteN n s).size = 25
  | 0, _, hs => hs
  | n + 1, s, _ => keccakPermuteN_size n (keccakF1600_size s)

theorem keccakAbsorb_rowSeed_size {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col : Nat) :
    (keccakAbsorb 21 0x1f#8 (rowSeed rho row col)).size = 25 := by
  rw [keccakAbsorb_rowSeed hrho row col]; exact keccakF1600_size _

@[expose] def expVars25 (base : Nat) : List KExpr :=
  (List.range 25).map (fun i => .var (base + i))

@[expose] def slotExprsLo (cfg : KCfg) (st : KState) (slots : List KSlot) : List KExpr :=
  (List.range 25).map fun i => (readSlot cfg st (slots.getD i (.vreg 0))).1

@[expose] def slotExprsHi (cfg : KCfg) (st : KState) (slots : List KSlot) : List KExpr :=
  (List.range 25).map fun i => (readSlot cfg st (slots.getD i (.vreg 0))).2

@[expose] def slotNonHeader (cfg : KCfg) : KSlot → Bool
  | .vreg r => decide (r < 32)
  | .spillQ off => decide (24 ≤ (off - cfg.offA) / 8 ∧ (off - cfg.offA) / 8 + 1 < 512)

private theorem append_lo64 (b a : BitVec 64) : (b ++ a).truncate 64 = a := by bv_bits
private theorem append_hi64 (b a : BitVec 64) : ((b ++ a) >>> 64).truncate 64 = b := by bv_bits

theorem slotHolds_inj {cfg : KCfg} {s : State} {tA : BTree (BitVec 64) 9} {sl : KSlot}
    {a1 b1 a2 b2 : BitVec 64}
    (h1 : slotHolds cfg s tA sl a1 b1) (h2 : slotHolds cfg s tA sl a2 b2) :
    a1 = a2 ∧ b1 = b2 := by
  cases sl with
  | vreg r =>
      have heq := h1.2.symm.trans h2.2
      exact ⟨by simpa [append_lo64] using congrArg (fun v : BitVec 128 => v.truncate 64) heq,
        by simpa [append_hi64] using congrArg (fun v : BitVec 128 => (v >>> 64).truncate 64) heq⟩
  | spillQ off => exact ⟨h1.2.1.symm.trans h2.2.1, h1.2.2.symm.trans h2.2.2⟩

theorem readSlot_varsLt800 {cfg : KCfg} {sl : KSlot}
    (hnh : slotNonHeader cfg sl = true) :
    exprVarsOk (fun id => decide (id < 800)) (readSlot cfg
      { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
        gprs := BTree.ofFn 5 calleeGprExpr
        memA := BTree.ofFn 9 headerMemAExpr
        memB := BTree.ofFn 9 (fun i => .var (800 + i))
        zFlag := none } sl).1 = true ∧
    exprVarsOk (fun id => decide (id < 800)) (readSlot cfg
      { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
        gprs := BTree.ofFn 5 calleeGprExpr
        memA := BTree.ofFn 9 headerMemAExpr
        memB := BTree.ofFn 9 (fun i => .var (800 + i))
        zFlag := none } sl).2 = true := by
  cases sl with
  | vreg r =>
      simp only [slotNonHeader, decide_eq_true_eq] at hnh
      simp only [readSlot, BTree.get_ofFn 5 _ r hnh, exprVarsOk, decide_eq_true_eq]
      omega
  | spillQ off =>
      simp only [slotNonHeader, decide_eq_true_eq] at hnh
      simp only [readSlot]
      generalize (off - cfg.offA) / 8 = k at hnh ⊢
      have h0 : k < 2 ^ 9 := by change k < 512; omega
      have h1 : k + 1 < 2 ^ 9 := hnh.2
      have hne (m : Nat) (hm : 24 ≤ m) : headerMemAExpr m = .var (200 + m) := by
        simp [headerMemAExpr, show m ≠ 0 by omega, show m ≠ 1 by omega, show m ≠ 2 by omega,
          show m ≠ 3 by omega, show m ≠ 4 by omega, show m ≠ 5 by omega, show m ≠ 7 by omega,
          show m ≠ 8 by omega, show m ≠ 9 by omega, show m ≠ 14 by omega, show m ≠ 15 by omega,
          show m ≠ 16 by omega, show m ≠ 17 by omega, show m ≠ 18 by omega, show m ≠ 19 by omega,
          show m ≠ 20 by omega, show m ≠ 21 by omega, show m ≠ 22 by omega, show m ≠ 23 by omega]
      rw [BTree.get_ofFn 9 _ k h0, BTree.get_ofFn 9 _ (k + 1) h1, hne k hnh.1, hne (k + 1) (by omega)]
      simp only [exprVarsOk, decide_eq_true_eq]
      omega

@[expose] def stRawB : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs  := BTree.ofFn 5 calleeGprExpr
    memA  := BTree.ofFn 9 headerMemAExpr
    memB  := BTree.ofFn 9 (fun i => .var (800 + i))
    zFlag := none }

@[expose] def envInitB (sp rcBase : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (s : State) (tA tB : BTree (BitVec 64) 9) : KEnv :=
  { (envInitA sp rcBase rho row s tA) with
    vars := fun id =>
      if id < 800 then (envInitA sp rcBase rho row s tA).vars id
      else if id < 1312 then tB.get (id - 800)
      else 0#64 }

private theorem calleeGprExpr_varsLt800 :
    ∀ k : Fin 32, exprVarsOk (fun id => decide (id < 800)) (calleeGprExpr k.val) = true := by decide

private theorem headerMemAExpr_varsLt800 :
    ∀ i : Fin 512, exprVarsOk (fun id => decide (id < 800)) (headerMemAExpr i.val) = true := by
  decide +kernel

theorem stRawB_matches {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA tB : BTree (BitVec 64) 9}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA) :
    let env := envInitB sp rcBase rho row s tA tB
    KStateMatches env stRawB s ∧
      evalMemTree env stRawB.memA = tA ∧
      evalMemTree env stRawB.memB = tB := by
  have hsub : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (envInitB sp rcBase rho row s tA tB) e =
        evalKExpr (envInitA sp rcBase rho row s tA) e :=
    Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid; simp [envInitB, hid]
  rcases hgprs with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp⟩
  have hmA0 := (stInitA_matches hsp hspA ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp⟩ hhdr).1
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_, ?_⟩
  · intro vr
    have hlt := vr.isLt
    have hv := hmA0.hvregs vr
    simp only [Seg2InitA.stInitA, BTree.get_ofFn 5 _ vr.toNat hlt] at hv
    simp only [stRawB, BTree.get_ofFn 5 _ vr.toNat hlt]
    rw [hsub _ (by simp [exprVarsOk]; omega), hsub _ (by simp [exprVarsOk]; omega)]
    exact hv
  · intro g hg31
    have hlt := g.isLt
    have hg := hmA0.hgprs g hg31
    simp only [Seg2InitA.stInitA, BTree.get_ofFn 5 _ g.toNat hlt] at hg
    simp only [stRawB, BTree.get_ofFn 5 _ g.toNat hlt]
    rwa [hsub _ (calleeGprExpr_varsLt800 ⟨g.toNat, hlt⟩)]
  · apply btree_ext_get; intro i hi
    simp only [evalMemTree, stRawB, BTree.get_map, BTree.get_ofFn 9 _ i hi]
    rw [hsub _ (headerMemAExpr_varsLt800 ⟨i, hi⟩)]; exact eval_headerMemAExpr hhdr i hi
  · apply btree_ext_get; intro i hi
    change i < 512 at hi
    simp [evalMemTree, stRawB, BTree.get_map, BTree.get_ofFn 9 _ i (show i < 2 ^ 9 from hi),
      evalKExpr, envInitB, show ¬(800 + i < 800) by omega, show 800 + i < 1312 by omega]

theorem evalExprList25_slotExprs {cfg : KCfg} {env0 env : KEnv} {s : State} {tA : BTree (BitVec 64) 9}
    {slots : List KSlot} {sLo sHi : KeccakState}
    (hm0 : KStateMatches env0 stRawB s) (htA : evalMemTree env0 stRawB.memA = tA)
    (heval : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true → evalKExpr env e = evalKExpr env0 e)
    (hvalid : slots.all (KeccakLoop.slotValid cfg) = true)
    (hnh : slots.all (slotNonHeader cfg) = true) (hlen : slots.length = 25)
    (hsLo : sLo.size = 25) (hsHi : sHi.size = 25)
    (hholds : ∀ idx, idx < 25 → slotHolds cfg s tA (slots.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64)) :
    evalExprList25 env (slotExprsLo cfg stRawB slots) = sLo ∧
      evalExprList25 env (slotExprsHi cfg stRawB slots) = sHi := by
  have hpair : ∀ idx, idx < 25 →
      evalKExpr env (readSlot cfg stRawB (slots.getD idx (.vreg 0))).1 = sLo.getD idx 0#64 ∧
      evalKExpr env (readSlot cfg stRawB (slots.getD idx (.vreg 0))).2 = sHi.getD idx 0#64 := by
    intro idx hidx
    have hmem : slots.getD idx (.vreg 0) ∈ slots := by
      have hlt : idx < slots.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
    have hv := List.all_eq_true.mp hvalid _ hmem
    have hn := List.all_eq_true.mp hnh _ hmem
    have hr := KeccakLoop.readSlot_holds hv hm0 (sl := slots.getD idx (.vreg 0))
    rw [htA] at hr
    rcases slotHolds_inj hr (hholds idx hidx) with ⟨h1, h2⟩
    rcases readSlot_varsLt800 (cfg := cfg) hn with ⟨hok1, hok2⟩
    exact ⟨(heval _ hok1).trans h1, (heval _ hok2).trans h2⟩
  refine ⟨keccakState_eq_of_getD (by simp [evalExprList25]) hsLo fun idx hidx => ?_,
    keccakState_eq_of_getD (by simp [evalExprList25]) hsHi fun idx hidx => ?_⟩
  · have hg : (slotExprsLo cfg stRawB slots).getD idx (.const64 0#64) =
        (readSlot cfg stRawB (slots.getD idx (.vreg 0))).1 := by
      simp [slotExprsLo, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
    rw [show (evalExprList25 env (slotExprsLo cfg stRawB slots)).getD idx 0#64 =
      evalKExpr env ((slotExprsLo cfg stRawB slots).getD idx (.const64 0#64)) by
      simp [evalExprList25, Array.getD, hidx], hg, (hpair idx hidx).1]
  · have hg : (slotExprsHi cfg stRawB slots).getD idx (.const64 0#64) =
        (readSlot cfg stRawB (slots.getD idx (.vreg 0))).2 := by
      simp [slotExprsHi, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
    rw [show (evalExprList25 env (slotExprsHi cfg stRawB slots)).getD idx 0#64 =
      evalKExpr env ((slotExprsHi cfg stRawB slots).getD idx (.const64 0#64)) by
      simp [evalExprList25, Array.getD, hidx], hg, (hpair idx hidx).2]

theorem evalExprList25_vars {env : KEnv} {base : Nat} {s : KeccakState} (hs : s.size = 25)
    (hv : ∀ idx, idx < 25 → env.vars (base + idx) = s.getD idx 0#64) :
    evalExprList25 env (expVars25 base) = s :=
  keccakState_eq_of_getD (by simp [evalExprList25]) hs fun idx hidx => by
    have hg : (expVars25 base).getD idx (.const64 0#64) = .var (base + idx) := by
      simp [expVars25, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
    rw [show (evalExprList25 env (expVars25 base)).getD idx 0#64 =
      evalKExpr env ((expVars25 base).getD idx (.const64 0#64)) by
      simp [evalExprList25, Array.getD, hidx], hg]
    exact hv idx hidx

/-! ## 2. Slice B Certificate (`+0x0fa8 → +0x25c0`, `L3`–`L6`) & `seg2_initB_ok` -/

@[expose] def stepsRawB : List KProgStep :=
  [.range 1002 24,
   .loop 1026 197 8#5 slotsL3 (slotExprsLo cfgB stRawB slotsFa8_01) (slotExprsHi cfgB stRawB slotsFa8_01) 2000,
   .range 1224 29,
   .loop 1253 208 8#5 slotsL4 (expVars25 2000) (expVars25 2025) 3000,
   .range 1462 44,
   .loop 1506 202 8#5 slotsL5 (slotExprsLo cfgB stRawB slotsFa8_23) (slotExprsHi cfgB stRawB slotsFa8_23) 4000,
   .range 1709 38,
   .loop 1747 204 8#5 slotsL6 (expVars25 4000) (expVars25 4025) 5000,
   .range 1952 464]

@[expose] def expMemBInit3 (c blk j : Nat) : KExpr :=
  match c, blk with
  | 0, 0 => (readSlot cfgB stRawB (slotsFa8_01.getD j (.vreg 0))).1
  | 0, 1 => .var (2000 + j) | 0, 2 => .var (3000 + j)
  | 1, 0 => (readSlot cfgB stRawB (slotsFa8_01.getD j (.vreg 0))).2
  | 1, 1 => .var (2025 + j) | 1, 2 => .var (3025 + j)
  | 2, 0 => (readSlot cfgB stRawB (slotsFa8_23.getD j (.vreg 0))).1
  | 2, 1 => .var (4000 + j) | 2, 2 => .var (5000 + j)
  | _, 0 => (readSlot cfgB stRawB (slotsFa8_23.getD j (.vreg 0))).2
  | _, 1 => .var (4025 + j) | _, _ => .var (5025 + j)

@[expose] def chkMemBInit3 (ok : Nat → Bool) (st : KState) : Bool :=
  (List.range 4).all fun c => (List.range 3).all fun blk => (List.range 21).all fun j =>
    let e := expMemBInit3 c blk j
    (st.memB.get (63 * c + 21 * blk + j)).beq e && exprVarsOk ok e

@[expose] def chkRawB (ok : Nat → Bool) (st : KState) : Bool :=
  (st.gprs.get 1).beq (.add64 (.var 64) (.const64 1#64)) && exprVarsOk ok (.add64 (.var 64) (.const64 1#64)) &&
  (st.gprs.get 8).beq (.const64 0#64) && exprVarsOk ok (.const64 0#64) &&
  (st.gprs.get 9).beq (.spAdd 28859#64) && exprVarsOk ok (.spAdd 28859#64) &&
  checkHeaderPreserved ok st && checkCalleeGprsPreserved ok st && chkMemBInit3 ok st &&
  checkOutSlots cfgB ok st slotsMidInit01 3000 && checkOutSlots cfgB ok st slotsMidInit23 5000

theorem cert_sliceB :
    runAndCheckKProg cfgB 1002 2416 1002 2416 1600 stepsRawB stRawB chkRawB = true :=
  runAndCheckKProg_of_fast (by decide +kernel)

attribute [local irreducible] blkPC07 keccakF1600 keccakAbsorb BTreeMem

@[expose] def RowInitBPost [MlKemPlacement] (sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  RowCalleeGprs sp rcBase row sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 28859#64 ∧
  ∃ (tA tB : BTree (BitVec 64) 9), MemAHeaderOk sp rho tA ∧
    (∀ c, c < 4 → btreeBytesFrom (63 * c) 63 tB = shake128FirstBlocks (rowSeed rho row c) 3) ∧
    (∀ idx, idx < 25 → slotHolds cfgB sf tA (slotsMidInit01.getD idx (.vreg 0))
      ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
      ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHolds cfgB sf tA (slotsMidInit23.getD idx (.vreg 0))
      ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
      ((keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64)) ∧
    (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      BTreeMem (sp + 28848#64) 252 tB ∗ MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
      MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 26768#64) 672 ∗ Rest)

private theorem extract3_eq_shake128 {tB : BTree (BitVec 64) 9} {seed : List (BitVec 8)} {c : Nat}
    (hb0 : ∀ j, j < 21 → tB.get (63 * c + j) = (keccakAbsorb 21 0x1f#8 seed).getD j 0#64)
    (hb1 : ∀ j, j < 21 → tB.get (63 * c + 21 + j) = (keccakPermuteN 1 (keccakAbsorb 21 0x1f#8 seed)).getD j 0#64)
    (hb2 : ∀ j, j < 21 → tB.get (63 * c + 42 + j) = (keccakPermuteN 2 (keccakAbsorb 21 0x1f#8 seed)).getD j 0#64) :
    btreeBytesFrom (63 * c) 63 tB = shake128FirstBlocks seed 3 := by
  have h1 : btreeBytesFrom (63 * c) 63 tB =
      btreeBytesFrom (63 * c) 21 tB ++ (btreeBytesFrom (63 * c + 21) 21 tB ++ btreeBytesFrom (63 * c + 42) 21 tB) := by
    rw [show (63 : Nat) = 21 + 42 from rfl, btreeBytesFrom_split (63 * c) 21 42 tB,
      show (42 : Nat) = 21 + 21 from rfl, btreeBytesFrom_split (63 * c + 21) 21 21 tB]
  rw [h1, btreeBytesFrom_eq_extractRate_21 hb0, btreeBytesFrom_eq_extractRate_21 hb1,
    btreeBytesFrom_eq_extractRate_21 hb2]
  simp [shake128FirstBlocks, keccakSqueezeBlocks, keccakPermuteN]

theorem seg2_initB_ok [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) {s : State} {P : SepProp}
    (hpc : s.pc = b + 4008#64) (hrun : s.status = .Running)
    (hpre : RowInitAPost sp rcBase rho row Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 9664#64) s P (RowInitBPost sp rcBase rho row Rest) := by
  rcases hpre with ⟨hsp, hspA, hsp_chk, hcl, hro, hgprs, tA0, hhdr0, hsl01, hsl23, hP⟩
  refine sepWP_seq_env hcl hro (post1 := fun sf Pf =>
    mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem →
      RowInitBPost sp rcBase rho row Rest sf Pf) ?_ fun sf Pf hpcF hrunF hclF hroF hpost =>
    SepWP.done hpcF hrunF (hpost hclF hroF)
  refine SepWP.weaken_pre hP ?_
  refine SepWP.of_memRegion_btreeMem 252 (sp + 28848#64) (by decide) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun tB0 => ?_
  rcases stRawB_matches hsp hspA hgprs hhdr0 (tB := tB0) with ⟨hm0, htA0, htB0⟩
  let env0 := envInitB sp rcBase rho row s tA0 tB0
  change KStateMatches env0 stRawB s at hm0
  change evalMemTree env0 stRawB.memA = tA0 at htA0
  change evalMemTree env0 stRawB.memB = tB0 at htB0
  have henvSp : env0.sp = sp := rfl
  have henvRc : env0.rcBase = rcBase := rfl
  have hspEnt :
      (BTreeMem (sp + 28848#64) 252 tB0 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
        MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
        MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 26768#64) 672 ∗ Rest)) ⊢
      KSpatial cfgB env0 stRawB (MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
        MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 26768#64) 672 ∗ Rest) := by
    simp only [KSpatial, cfgB, henvSp, henvRc, htA0, htB0]; sep_frame
  refine SepWP.weaken_pre hspEnt ?_
  refine sepWP_of_runAndCheckKProg cfgB_valid (env0 := env0) (show 0 < 24 by decide) cert_sliceB hm0 hpc hrun ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _ heval hmF hchk
  simp only [chkRawB, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx1_eq, hx1_ok⟩, hx8_eq⟩, hx8_ok⟩, hx9_eq⟩, hx9_ok⟩,
    hhdr_chk⟩, hgpr_chk⟩, hmemB_chk⟩, hout01⟩, hout23⟩
  let s0 (col : Nat) := keccakAbsorb 21 0x1f#8 (rowSeed rho row col)
  have hlt800_01 : evalExprList25 env0 (slotExprsLo cfgB stRawB slotsFa8_01) = s0 0 ∧
      evalExprList25 env0 (slotExprsHi cfgB stRawB slotsFa8_01) = s0 1 :=
    evalExprList25_slotExprs hm0 htA0 (fun _ _ => rfl) (by decide) (by decide) rfl
      (keccakAbsorb_rowSeed_size hrho row 0) (keccakAbsorb_rowSeed_size hrho row 1) hsl01
  let env1 := extendLoopVars env0 2000 (s0 0) (s0 1)
  have hv1 : evalExprList25 env1 (expVars25 2000) = keccakPermuteN 1 (s0 0) ∧
      evalExprList25 env1 (expVars25 2025) = keccakPermuteN 1 (s0 1) :=
    ⟨evalExprList25_vars (keccakPermuteN_size 1 (keccakAbsorb_rowSeed_size hrho row 0)) fun i hi => by
      simp [env1, extendLoopVars, keccakPermuteN, show ¬(2000 + i < 2000) by omega, show 2000 + i < 2000 + 25 by omega],
     evalExprList25_vars (keccakPermuteN_size 1 (keccakAbsorb_rowSeed_size hrho row 1)) fun i hi => by
      simp [env1, extendLoopVars, keccakPermuteN, show ¬(2025 + i < 2000) by omega,
        show ¬(2025 + i < 2000 + 25) by omega, show 2025 + i < 2000 + 50 by omega,
        show 2025 + i - (2000 + 25) = i by omega]⟩
  let env2 := extendLoopVars env1 3000 (keccakPermuteN 1 (s0 0)) (keccakPermuteN 1 (s0 1))
  have hsub2 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true → evalKExpr env2 e = evalKExpr env0 e :=
    Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid
      simp [env2, env1, extendLoopVars, show id < 3000 by omega, show id < 2000 by omega]
  have hlt800_23 : evalExprList25 env2 (slotExprsLo cfgB stRawB slotsFa8_23) = s0 2 ∧
      evalExprList25 env2 (slotExprsHi cfgB stRawB slotsFa8_23) = s0 3 :=
    evalExprList25_slotExprs hm0 htA0 hsub2 (by decide) (by decide) rfl
      (keccakAbsorb_rowSeed_size hrho row 2) (keccakAbsorb_rowSeed_size hrho row 3) hsl23
  let env3 := extendLoopVars env2 4000 (s0 2) (s0 3)
  have hv3 : evalExprList25 env3 (expVars25 4000) = keccakPermuteN 1 (s0 2) ∧
      evalExprList25 env3 (expVars25 4025) = keccakPermuteN 1 (s0 3) :=
    ⟨evalExprList25_vars (keccakPermuteN_size 1 (keccakAbsorb_rowSeed_size hrho row 2)) fun i hi => by
      simp [env3, extendLoopVars, keccakPermuteN, show ¬(4000 + i < 4000) by omega, show 4000 + i < 4000 + 25 by omega],
     evalExprList25_vars (keccakPermuteN_size 1 (keccakAbsorb_rowSeed_size hrho row 3)) fun i hi => by
      simp [env3, extendLoopVars, keccakPermuteN, show ¬(4025 + i < 4000) by omega,
        show ¬(4025 + i < 4000 + 25) by omega, show 4025 + i < 4000 + 50 by omega,
        show 4025 + i - (4000 + 25) = i by omega]⟩
  let env4 := extendLoopVars env3 5000 (keccakPermuteN 1 (s0 2)) (keccakPermuteN 1 (s0 3))
  have hspecEq : specEnvSteps env0 stepsRawB = env4 := by
    simp only [stepsRawB, specEnvSteps, hlt800_01.1, hlt800_01.2]
    change specEnvSteps env1 [.range 1224 29, .loop 1253 208 8#5 slotsL4 (expVars25 2000) (expVars25 2025) 3000,
      .range 1462 44, .loop 1506 202 8#5 slotsL5 (slotExprsLo cfgB stRawB slotsFa8_23) (slotExprsHi cfgB stRawB slotsFa8_23) 4000,
      .range 1709 38, .loop 1747 204 8#5 slotsL6 (expVars25 4000) (expVars25 4025) 5000, .range 1952 464] = env4
    simp only [specEnvSteps, hv1.1, hv1.2]
    change specEnvSteps env2 [.range 1462 44, .loop 1506 202 8#5 slotsL5 (slotExprsLo cfgB stRawB slotsFa8_23) (slotExprsHi cfgB stRawB slotsFa8_23) 4000,
      .range 1709 38, .loop 1747 204 8#5 slotsL6 (expVars25 4000) (expVars25 4025) 5000, .range 1952 464] = env4
    simp only [specEnvSteps, hlt800_23.1, hlt800_23.2]
    change specEnvSteps env3 [.range 1709 38, .loop 1747 204 8#5 slotsL6 (expVars25 4000) (expVars25 4025) 5000, .range 1952 464] = env4
    simp only [specEnvSteps, hv3.1, hv3.2]; rfl
  have hsub4 : ∀ e, exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (specEnvSteps env0 stepsRawB) e = evalKExpr env0 e := by
    rw [hspecEq]
    exact Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid
      simp [env4, env3, env2, env1, extendLoopVars,
        show id < 5000 by omega, show id < 4000 by omega, show id < 3000 by omega, show id < 2000 by omega]
  have hspecSp : (specEnvSteps env0 stepsRawB).sp = sp := by rw [hspecEq]; rfl
  have hspecRc : (specEnvSteps env0 stepsRawB).rcBase = rcBase := by rw [hspecEq]; rfl
  have hspec64 : (specEnvSteps env0 stepsRawB).vars 64 = BitVec.ofNat 64 row :=
    (hsub4 (.var 64) (by decide)).trans rfl
  have hx1 := eval_checked_gpr hmF heval 1#5 (by decide) (.add64 (.var 64) (.const64 1#64)) hx1_eq hx1_ok
  have hx8 := eval_checked_gpr hmF heval 8#5 (by decide) (.const64 0#64) hx8_eq hx8_ok
  have hx9 := eval_checked_gpr hmF heval 9#5 (by decide) (.spAdd 28859#64) hx9_eq hx9_ok
  have hhdrF := checked_headerOk heval hspecSp
    ((hsub4 (.var 100) (by decide)).trans rfl)
    ((hsub4 (.var 101) (by decide)).trans rfl)
    ((hsub4 (.var 102) (by decide)).trans rfl)
    ((hsub4 (.var 103) (by decide)).trans rfl) hhdr_chk
  have hgprsF := checked_calleeGprs hmF heval hspecSp hspecRc hspec64 hgpr_chk
  have hslOut01 := checked_outSlots hmF heval (by decide) (by decide) hout01
  have hslOut23 := checked_outSlots hmF heval (by decide) (by decide) hout23
  refine SepWP.done hpcF hrunF fun hclF hroF => ⟨hmF.hsp.trans hspF, hmF.hsp_al, hsp_chk, hclF, hroF, hgprsF,
    by simpa [Reg.x1, evalKExpr, hspec64, BitVec.ofNat_add] using hx1,
    by simpa [Reg.x8, evalKExpr] using hx8,
    by simpa [Reg.x9, evalKExpr, hspecSp] using hx9,
    evalMemTree envFinal stEnd.memA, evalMemTree envFinal stEnd.memB, hhdrF, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hmB_at (blk j : Nat) (hblk : blk < 3) (hj : j < 21) :
        (evalMemTree envFinal stEnd.memB).get (63 * c + 21 * blk + j) =
          evalKExpr (specEnvSteps env0 stepsRawB) (expMemBInit3 c blk j) := by
      have h1 := List.all_eq_true.mp hmemB_chk c (List.mem_range.mpr hc)
      have h2 := List.all_eq_true.mp h1 blk (List.mem_range.mpr hblk)
      have h3 := List.all_eq_true.mp h2 j (List.mem_range.mpr hj)
      rcases Bool.and_eq_true _ _ |>.mp h3 with ⟨heq, hok⟩
      exact eval_checked_memB heval _ _ heq hok
    have hslot_val (slots : List KSlot)
        (hval : slots.all (KeccakLoop.slotValid cfgB) = true)
        (hnh : slots.all (slotNonHeader cfgB) = true) (hlen : slots.length = 25)
        {sLo sHi : KeccakState}
        (hh : ∀ idx, idx < 25 → slotHolds cfgB s tA0 (slots.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64))
        (j : Nat) (hj : j < 21) :
        evalKExpr (specEnvSteps env0 stepsRawB) (readSlot cfgB stRawB (slots.getD j (.vreg 0))).1 = sLo.getD j 0#64 ∧
        evalKExpr (specEnvSteps env0 stepsRawB) (readSlot cfgB stRawB (slots.getD j (.vreg 0))).2 = sHi.getD j 0#64 := by
      have hmem : slots.getD j (.vreg 0) ∈ slots := by
        have hlt : j < slots.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
      have hr := KeccakLoop.readSlot_holds (List.all_eq_true.mp hval _ hmem) hm0 (sl := slots.getD j (.vreg 0))
      rw [htA0] at hr
      rcases slotHolds_inj hr (hh j (by omega)) with ⟨e1, e2⟩
      rcases readSlot_varsLt800 (cfg := cfgB) (List.all_eq_true.mp hnh _ hmem) with ⟨ok1, ok2⟩
      exact ⟨(hsub4 _ ok1).trans e1, (hsub4 _ ok2).trans e2⟩
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · refine extract3_eq_shake128 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      · simpa [expMemBInit3] using (hmB_at 0 j (by decide) hj).trans (hslot_val slotsFa8_01 (by decide) (by decide) rfl hsl01 j hj).1
      · rw [show 63 * 0 + 21 + j = 63 * 0 + 21 * 1 + j by omega, hmB_at 1 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, env2, env1, extendLoopVars, keccakPermuteN,
          show 2000 + j < 5000 by omega, show 2000 + j < 4000 by omega, show 2000 + j < 3000 by omega,
          show ¬(2000 + j < 2000) by omega, show 2000 + j < 2000 + 25 by omega]
      · rw [show 63 * 0 + 42 + j = 63 * 0 + 21 * 2 + j by omega, hmB_at 2 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, env2, extendLoopVars, keccakPermuteN_succ_right 1,
          show 3000 + j < 5000 by omega, show 3000 + j < 4000 by omega,
          show ¬(3000 + j < 3000) by omega, show 3000 + j < 3000 + 25 by omega]
    · refine extract3_eq_shake128 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      · simpa [expMemBInit3] using (hmB_at 0 j (by decide) hj).trans (hslot_val slotsFa8_01 (by decide) (by decide) rfl hsl01 j hj).2
      · rw [show 63 * 1 + 21 + j = 63 * 1 + 21 * 1 + j by omega, hmB_at 1 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, env2, env1, extendLoopVars, keccakPermuteN,
          show 2025 + j < 5000 by omega, show 2025 + j < 4000 by omega, show 2025 + j < 3000 by omega,
          show ¬(2025 + j < 2000) by omega, show ¬(2025 + j < 2000 + 25) by omega,
          show 2025 + j < 2000 + 50 by omega, show 2025 + j - (2000 + 25) = j by omega]
      · rw [show 63 * 1 + 42 + j = 63 * 1 + 21 * 2 + j by omega, hmB_at 2 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, env2, extendLoopVars, keccakPermuteN_succ_right 1,
          show 3025 + j < 5000 by omega, show 3025 + j < 4000 by omega,
          show ¬(3025 + j < 3000) by omega, show ¬(3025 + j < 3000 + 25) by omega,
          show 3025 + j < 3000 + 50 by omega, show 3025 + j - (3000 + 25) = j by omega]
    · refine extract3_eq_shake128 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      · simpa [expMemBInit3] using (hmB_at 0 j (by decide) hj).trans (hslot_val slotsFa8_23 (by decide) (by decide) rfl hsl23 j hj).1
      · rw [show 63 * 2 + 21 + j = 63 * 2 + 21 * 1 + j by omega, hmB_at 1 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, extendLoopVars, keccakPermuteN,
          show 4000 + j < 5000 by omega, show ¬(4000 + j < 4000) by omega, show 4000 + j < 4000 + 25 by omega]
      · rw [show 63 * 2 + 42 + j = 63 * 2 + 21 * 2 + j by omega, hmB_at 2 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, extendLoopVars, keccakPermuteN_succ_right 1,
          show ¬(5000 + j < 5000) by omega, show 5000 + j < 5000 + 25 by omega]
    · refine extract3_eq_shake128 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      · simpa [expMemBInit3] using (hmB_at 0 j (by decide) hj).trans (hslot_val slotsFa8_23 (by decide) (by decide) rfl hsl23 j hj).2
      · rw [show 63 * 3 + 21 + j = 63 * 3 + 21 * 1 + j by omega, hmB_at 1 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, env3, extendLoopVars, keccakPermuteN,
          show 4025 + j < 5000 by omega, show ¬(4025 + j < 4000) by omega,
          show ¬(4025 + j < 4000 + 25) by omega, show 4025 + j < 4000 + 50 by omega,
          show 4025 + j - (4000 + 25) = j by omega]
      · rw [show 63 * 3 + 42 + j = 63 * 3 + 21 * 2 + j by omega, hmB_at 2 j (by decide) hj, hspecEq]
        simp [s0, expMemBInit3, evalKExpr, env4, extendLoopVars, keccakPermuteN_succ_right 1,
          show ¬(5025 + j < 5000) by omega, show ¬(5025 + j < 5000 + 25) by omega,
          show 5025 + j < 5000 + 50 by omega, show 5025 + j - (5000 + 25) = j by omega]
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsRawB).vars (3000 + idx) = (keccakPermuteN 2 (s0 0)).getD idx 0#64 := by
      rw [hspecEq]; simp [env4, env3, env2, extendLoopVars, keccakPermuteN_succ_right 1,
        show 3000 + idx < 5000 by omega, show 3000 + idx < 4000 by omega,
        show ¬(3000 + idx < 3000) by omega, show 3000 + idx < 3000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsRawB).vars (3000 + 25 + idx) = (keccakPermuteN 2 (s0 1)).getD idx 0#64 := by
      rw [hspecEq]; simp [env4, env3, env2, extendLoopVars, keccakPermuteN_succ_right 1,
        show 3000 + 25 + idx < 5000 by omega, show 3000 + 25 + idx < 4000 by omega,
        show ¬(3000 + 25 + idx < 3000) by omega, show ¬(3000 + 25 + idx < 3000 + 25) by omega,
        show 3000 + 25 + idx < 3000 + 50 by omega]
    simpa [hvLo, hvHi] using hslOut01 idx hidx
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsRawB).vars (5000 + idx) = (keccakPermuteN 2 (s0 2)).getD idx 0#64 := by
      rw [hspecEq]; simp [env4, extendLoopVars, keccakPermuteN_succ_right 1,
        show ¬(5000 + idx < 5000) by omega, show 5000 + idx < 5000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsRawB).vars (5000 + 25 + idx) = (keccakPermuteN 2 (s0 3)).getD idx 0#64 := by
      rw [hspecEq]; simp [env4, extendLoopVars, keccakPermuteN_succ_right 1,
        show ¬(5000 + 25 + idx < 5000) by omega, show ¬(5000 + 25 + idx < 5000 + 25) by omega,
        show 5000 + 25 + idx < 5000 + 50 by omega]
    simpa [hvLo, hvHi] using hslOut23 idx hidx
  · simp only [KSpatial, cfgB, hspF, hrcF, henvSp, henvRc]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB
