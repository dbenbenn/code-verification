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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf

/-!
# `kyber_encapsulate` (`B07`) — Post-Loop Symbolic Transition & Squeeze Bridges (`KeccakProg`)

Variable-bound congruence (`exprVarsLt`, `stateVarsLt`), symbolic post-loop state transition
(`stepKLoopSym`, `sepWP_of_stepKLoop`), and `BTreeMem` ↔ `keccakExtractRate` / `RejBufReadable`
squeeze bridges for `Seg2` (`+0x0758 .. +0x3d0c`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakExtractRate keccakF1600 unpackLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (blkPC07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf (
  anfBeq keccakSpecRoundExpr toAnf?
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMem_eq_bytes KCfgValid KSpatial KStateMatches
  btreeBytes btreeBytesFrom btreeBytesFrom_length btreeBytesFrom_split evalMemTree
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  anfMatchesSpec btree_ext_get checkKeccakLoop07 readSlot readSlot_holds sepWP_of_keccakLoop24
  slotHolds slotValid truncate64_append ushr64_truncate64_append
)

attribute [local irreducible] keccakF1600 blkPC07

/-! ## 1. `btreeAll`, `exprVarsLt`, `stateVarsLt`, & Variable-Bound Congruence -/

@[expose] def btreeAll {α : Type} (p : α → Bool) : {d : Nat} → BTree α d → Bool
  | 0, .leaf v => p v
  | _ + 1, .node lo hi => btreeAll p lo && btreeAll p hi

theorem btreeAll_get {α : Type} (p : α → Bool) :
    ∀ {d : Nat} (t : BTree α d),
      btreeAll p t = true → ∀ i, i < 2 ^ d → p (t.get i) = true
  | 0, .leaf v, h, i, hi => by
      have hi0 : i = 0 := by omega
      subst hi0; exact h
  | d + 1, .node lo hi, h, i, hii => by
      simp only [btreeAll, Bool.and_eq_true] at h
      have hi2 : i / 2 < 2 ^ d := by rw [Nat.pow_succ] at hii; omega
      simp only [BTree.get]
      split
      · exact btreeAll_get p lo h.1 (i / 2) hi2
      · exact btreeAll_get p hi h.2 (i / 2) hi2

theorem btreeAll_ofFn {α : Type} (p : α → Bool) :
    ∀ (d : Nat) (f : Nat → α),
      (∀ i, i < 2 ^ d → p (f i) = true) → btreeAll p (BTree.ofFn d f) = true
  | 0, f, hf => hf 0 (by decide)
  | d + 1, f, hf => by
      simp only [BTree.ofFn, btreeAll, Bool.and_eq_true]
      exact ⟨btreeAll_ofFn p d _ (fun k hk => hf (2 * k) (by rw [Nat.pow_succ]; omega)),
        btreeAll_ofFn p d _ (fun k hk => hf (2 * k + 1) (by rw [Nat.pow_succ]; omega))⟩

@[expose] def exprVarsLt (bound : Nat) : KExpr → Bool
  | .var id => Nat.blt id bound
  | .const64 _ | .spAdd _ | .rcAdd _ | .rcVal _
  | .rcLoopOff | .rcLoopPtr | .rcLoopNext | .rcLoopVal => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprVarsLt bound a && exprVarsLt bound b
  | .bsl x y z | .bitOp x y z =>
      exprVarsLt bound x && exprVarsLt bound y && exprVarsLt bound z
  | .shl a _ | .ushr a _ | .rotl a _ => exprVarsLt bound a

theorem exprVarsLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) :
    ∀ (e : KExpr), exprVarsLt b1 e = true → exprVarsLt b2 e = true := by
  intro e
  induction e with
  | var id =>
      simp only [exprVarsLt, Nat.blt_eq]; omega
  | const64 _ | spAdd _ | rcAdd _ | rcVal _ | rcLoopOff | rcLoopPtr | rcLoopNext | rcLoopVal =>
      simp [exprVarsLt]
  | xor a b iha ihb | bic a b iha ihb | and64 a b iha ihb | or64 a b iha ihb
  | add64 a b iha ihb | insByte0 a b iha ihb =>
      simp only [exprVarsLt, Bool.and_eq_true]
      exact fun h => ⟨iha h.1, ihb h.2⟩
  | bsl x y z ihx ihy ihz | bitOp x y z ihx ihy ihz =>
      simp only [exprVarsLt, Bool.and_eq_true]
      exact fun h => ⟨⟨ihx h.1.1, ihy h.1.2⟩, ihz h.2⟩
  | shl a _ ih | ushr a _ ih | rotl a _ ih =>
      exact ih

theorem evalKExpr_congr_vars {bound : Nat} {env1 env2 : KEnv}
    (hsp : env1.sp = env2.sp) (hrc : env1.rcBase = env2.rcBase) (hrl : env1.rLoop = env2.rLoop)
    (hvars : ∀ id, id < bound → env1.vars id = env2.vars id) :
    ∀ (e : KExpr), exprVarsLt bound e = true → evalKExpr env1 e = evalKExpr env2 e := by
  intro e
  induction e with
  | var id =>
      simp only [exprVarsLt, Nat.blt_eq, evalKExpr]
      exact fun h => hvars id h
  | const64 _ | rcVal _ => intro _; rfl
  | spAdd _ => intro _; simp [evalKExpr, hsp]
  | rcAdd _ => intro _; simp [evalKExpr, hrc]
  | rcLoopOff | rcLoopNext | rcLoopVal => intro _; simp [evalKExpr, hrl]
  | rcLoopPtr => intro _; simp [evalKExpr, hrc, hrl]
  | xor a b iha ihb | bic a b iha ihb | and64 a b iha ihb | or64 a b iha ihb
  | add64 a b iha ihb | insByte0 a b iha ihb =>
      simp only [exprVarsLt, Bool.and_eq_true, evalKExpr]
      intro h; rw [iha h.1, ihb h.2]
  | bsl x y z ihx ihy ihz | bitOp x y z ihx ihy ihz =>
      simp only [exprVarsLt, Bool.and_eq_true, evalKExpr]
      intro h; rw [ihx h.1.1, ihy h.1.2, ihz h.2]
  | shl a _ ih | ushr a _ ih | rotl a _ ih =>
      simp only [exprVarsLt, evalKExpr]
      intro h; rw [ih h]

@[expose] def stateVarsLt (bound : Nat) (st : KState) : Bool :=
  btreeAll (fun p => exprVarsLt bound p.1 && exprVarsLt bound p.2) st.vregs &&
    btreeAll (exprVarsLt bound) st.gprs &&
    btreeAll (exprVarsLt bound) st.memA &&
    btreeAll (exprVarsLt bound) st.memB

theorem evalMemTree_congr_vars {bound : Nat} {env1 env2 : KEnv} {m : BTree KExpr 9}
    (hm : btreeAll (exprVarsLt bound) m = true)
    (hsp : env1.sp = env2.sp) (hrc : env1.rcBase = env2.rcBase) (hrl : env1.rLoop = env2.rLoop)
    (hvars : ∀ id, id < bound → env1.vars id = env2.vars id) :
    evalMemTree env1 m = evalMemTree env2 m := by
  apply btree_ext_get; intro i hi
  simp only [evalMemTree, BTree.get_map]
  exact evalKExpr_congr_vars hsp hrc hrl hvars _ (btreeAll_get _ m hm i hi)

/-! ## 2. Output Lane Lookup (`findSpecLane`), `evalSlotsLo`/`Hi`, & `stepKLoopSym` -/

@[expose] def findSpecLaneAux
    (p : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat)))
    (base : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
      let idx := 25 - (rem + 1)
      match toAnf? (keccakSpecRoundExpr base idx) with
      | some q => if anfBeq p q then some idx else findSpecLaneAux p base rem
      | none => findSpecLaneAux p base rem

@[expose] def findSpecLane (e : KExpr) (base : Nat) : Option Nat :=
  match toAnf? e with
  | some p => findSpecLaneAux p base 25
  | none => none

private theorem findSpecLaneAux_sound
    {p : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat))}
    {e : KExpr} (hp : toAnf? e = some p) {base : Nat} :
    ∀ (rem : Nat) {idx : Nat},
      rem ≤ 25 → findSpecLaneAux p base rem = some idx →
      idx < 25 ∧ anfMatchesSpec e base idx = true := by
  intro rem
  induction rem with
  | zero => intro _ _ h; cases h
  | succ r ih =>
      intro idx hle h
      unfold findSpecLaneAux at h
      dsimp only at h
      cases hq : toAnf? (keccakSpecRoundExpr base (25 - (r + 1))) with
      | none =>
          simp only [hq] at h
          exact ih (by omega) h
      | some q =>
          simp only [hq] at h
          split at h
          case isTrue hbeq =>
            simp only [Option.some.injEq] at h; subst h
            exact ⟨by omega, by simp only [anfMatchesSpec, hp, hq]; exact hbeq⟩
          case isFalse =>
            exact ih (by omega) h

theorem findSpecLane_sound {e : KExpr} {base idx : Nat}
    (h : findSpecLane e base = some idx) :
    idx < 25 ∧ anfMatchesSpec e base idx = true := by
  unfold findSpecLane at h
  cases hp : toAnf? e with
  | none => simp [hp] at h
  | some p =>
      simp only [hp] at h
      exact findSpecLaneAux_sound hp 25 (Nat.le_refl _) h
@[expose] def mapBodyExpr (baseOut fallbackId : Nat) (e : KExpr) : KExpr :=
  match findSpecLane e 0 with
  | some idx => .var (baseOut + idx)
  | none =>
      match findSpecLane e 25 with
      | some idx => .var (baseOut + 25 + idx)
      | none => .var fallbackId

theorem exprVarsLt_mapBodyExpr {bound baseOut fallbackId : Nat}
    (hb : baseOut + 50 ≤ bound) (hfb : fallbackId < bound) (e : KExpr) :
    exprVarsLt bound (mapBodyExpr baseOut fallbackId e) = true := by
  unfold mapBodyExpr
  cases h0 : findSpecLane e 0 with
  | some idx =>
      have hi := (findSpecLane_sound h0).1
      simp only [exprVarsLt, Nat.blt_eq]; omega
  | none =>
      cases h25 : findSpecLane e 25 with
      | some idx =>
          have hi := (findSpecLane_sound h25).1
          simp only [exprVarsLt, Nat.blt_eq]; omega
      | none =>
          simp only [exprVarsLt, Nat.blt_eq]; exact hfb

@[expose] def evalSlotsLo (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (readSlot cfg st (slots.getD idx.1 (.vreg 0))).1

@[expose] def evalSlotsHi (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (readSlot cfg st (slots.getD idx.1 (.vreg 0))).2

@[simp] theorem evalSlotsLo_size (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    (evalSlotsLo cfg env st slots).size = 25 := by simp [evalSlotsLo]

@[simp] theorem evalSlotsHi_size (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    (evalSlotsHi cfg env st slots).size = 25 := by simp [evalSlotsHi]

theorem evalSlotsLo_getD (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot)
    {idx : Nat} (hidx : idx < 25) :
    (evalSlotsLo cfg env st slots).getD idx 0#64 =
      evalKExpr env (readSlot cfg st (slots.getD idx (.vreg 0))).1 := by
  simp [evalSlotsLo, Array.getD, hidx]

theorem evalSlotsHi_getD (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot)
    {idx : Nat} (hidx : idx < 25) :
    (evalSlotsHi cfg env st slots).getD idx 0#64 =
      evalKExpr env (readSlot cfg st (slots.getD idx (.vreg 0))).2 := by
  simp [evalSlotsHi, Array.getD, hidx]

@[expose] def buildPostLoopState (baseOut : Nat) (rCnt : BitVec 5) (stPre stBody : KState) : KState :=
  { vregs := BTree.ofFn 5 (fun vr =>
      let pB := stBody.vregs.get vr
      if pB == (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)) then stPre.vregs.get vr
      else
        (mapBodyExpr baseOut (baseOut + 50 + 2 * vr) pB.1,
         mapBodyExpr baseOut (baseOut + 50 + 2 * vr + 1) pB.2))
    gprs := BTree.ofFn 5 (fun g =>
      if Nat.beq g 21 then .rcAdd 0#64
      else if Nat.beq g rCnt.toNat then .const64 192#64
      else if stBody.gprs.get g == .var (200 + g) then stPre.gprs.get g
      else .var (baseOut + 114 + g))
    memA := BTree.ofFn 9 (fun i =>
      let eB := stBody.memA.get i
      if eB == .var (300 + i) then stPre.memA.get i
      else mapBodyExpr baseOut (baseOut + 146 + i) eB)
    memB := stPre.memB
    zFlag := some (.constBool true) }

@[expose] def stepKLoopSym (cfg : KCfg) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) : Option KState :=
  if Nat.ble 100 baseOut && stateVarsLt baseOut stPre &&
     Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 31#5) &&
     (stPre.gprs.get 21 == .rcAdd 0#64) &&
     (stPre.gprs.get rCnt.toNat == .const64 0#64) then
    match checkKeccakLoop07 cfg wHead nBody rCnt slots with
    | none => none
    | some stBody => some (buildPostLoopState baseOut rCnt stPre stBody)
  else none

@[expose] def mkPostLoopEnv (env0 : KEnv) (baseOut : Nat) (sA sB : KeccakState)
    (sf : State) (tA : BTree (BitVec 64) 9) : KEnv :=
  { sp := env0.sp, rcBase := env0.rcBase, rLoop := env0.rLoop
    vars := fun id =>
      if id < baseOut then env0.vars id
      else if id < baseOut + 25 then sA.getD (id - baseOut) 0#64
      else if id < baseOut + 50 then sB.getD (id - (baseOut + 25)) 0#64
      else if id < baseOut + 114 then
        let k := id - (baseOut + 50)
        let v := sf.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < baseOut + 146 then sf.readReg64 (.gpr (BitVec.ofNat 5 (id - (baseOut + 114))))
      else if id < baseOut + 658 then tA.get (id - (baseOut + 146))
      else 0#64 }

private theorem eval_mapBodyExpr {env0 env23 : KEnv} {baseOut fallbackId : Nat}
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

theorem btreeAll_mono {α : Type} {p q : α → Bool} (hpq : ∀ x, p x = true → q x = true) :
    ∀ {d : Nat} (t : BTree α d), btreeAll p t = true → btreeAll q t = true
  | 0, .leaf v, h => hpq v h
  | _ + 1, .node lo hi, h => by
      simp only [btreeAll, Bool.and_eq_true] at h ⊢
      exact ⟨btreeAll_mono hpq lo h.1, btreeAll_mono hpq hi h.2⟩

theorem stateVarsLt_stepKLoopSym {cfg : KCfg} {wHead nBody : Nat} {rCnt : BitVec 5}
    {slots : List KSlot} {baseOut : Nat} {stPre stPost : KState}
    (h : stepKLoopSym cfg wHead nBody rCnt slots baseOut stPre = some stPost) :
    stateVarsLt (baseOut + 658) stPost = true := by
  unfold stepKLoopSym at h
  split at h
  case isFalse => cases h
  case isTrue hhdr =>
  simp only [Bool.and_eq_true] at hhdr
  have hsv : stateVarsLt baseOut stPre = true := hhdr.1.1.1.1.1.2
  simp only [stateVarsLt, Bool.and_eq_true] at hsv
  rcases hsv with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hc : checkKeccakLoop07 cfg wHead nBody rCnt slots with
  | none => simp [hc] at h
  | some stBody =>
      simp only [hc, Option.some.injEq] at h; subst h
      simp only [stateVarsLt, buildPostLoopState, Bool.and_eq_true]
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

/-! ## 3. Soundness of `stepKLoopSym` (`sepWP_of_stepKLoop`) & Squeeze Buffer Bridges -/

theorem sepWP_of_stepKLoop [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgValid cfg) {env0 : KEnv}
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {baseOut : Nat}
    {stPre stPost : KState}
    (hstep : stepKLoopSym cfg wHead nBody rCnt slots baseOut stPre = some stPost)
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
      SepWP (blkPC07.rebase b (fun _ => none)) tgt sf (KSpatial cfg envPost stPost F) post oom) :
    SepWP (blkPC07.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 stPre F) post oom := by
  unfold stepKLoopSym at hstep
  split at hstep
  case isFalse => cases hstep
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨⟨_hb100, hsvPre⟩, hlen⟩, hslVal⟩, hne31⟩, hrcB⟩, hcntB⟩
  have hrcExpr : stPre.gprs.get 21 = .rcAdd 0#64 := beq_iff_eq.mp hrcB
  have hcntExpr : stPre.gprs.get rCnt.toNat = .const64 0#64 := beq_iff_eq.mp hcntB
  simp only [stateVarsLt, Bool.and_eq_true] at hsvPre
  rcases hsvPre with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hchk : checkKeccakLoop07 cfg wHead nBody rCnt slots with
  | none => simp [hchk] at hstep
  | some stBody =>
      simp only [hchk, Option.some.injEq] at hstep; subst hstep
      let sA0 := evalSlotsLo cfg env0 stPre slots
      let sB0 := evalSlotsHi cfg env0 stPre slots
      have hrc0 : s0.readReg64 (.gpr 21#5) = env0.rcBase := by
        have h := hm0.hgprs 21#5 (by decide)
        change _ = evalKExpr env0 (stPre.gprs.get 21) at h
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
      refine sepWP_of_keccakLoop24 (sA0 := sA0) (sB0 := sB0)
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
            if eB == .var (300 + i) then stPre.memA.get i
            else mapBodyExpr baseOut (baseOut + 146 + i) eB) = tAPost := by
        apply btree_ext_get; intro i hi
        simp only [evalMemTree, BTree.get_map]
        rw [BTree.get_ofFn 9 _ i hi]
        by_cases heq : (stBody.memA.get i == .var (300 + i)) = true
        · simp only [heq, ↓reduceIte]
          have hv := hmemAP i hi (beq_iff_eq.mp heq)
          have hcongr := evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP
            (stPre.memA.get i) (btreeAll_get _ stPre.memA hmAPre i hi)
          rw [hcongr]; simpa [tAPost, evalMemTree, BTree.get_map] using hv.symm
        · have heqF : (stBody.memA.get i == .var (300 + i)) = false := Bool.eq_false_iff.mpr heq
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
          exact (eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
            (fun idx hi hm => hB23 _ idx hi hm) hfb).trans
            (BTree.get_map (evalKExpr env23) stBody.memA i).symm
      have htBPEq : evalMemTree envP stPre.memB = evalMemTree env0 stPre.memB :=
        evalMemTree_congr_vars hmBPre rfl rfl rfl hvarsP
      have hmP : KStateMatches envP (buildPostLoopState baseOut rCnt stPre stBody) sf := by
        refine ⟨hspf, hspAf, ?_, ?_, ⟨hzfEq, by simp [hzfNe]⟩⟩
        · intro vr
          have hlt := vr.isLt
          dsimp only [buildPostLoopState]
          rw [BTree.get_ofFn 5 _ vr.toNat hlt]
          by_cases heq : (stBody.vregs.get vr.toNat ==
              (.var (100 + 2 * vr.toNat), .var (100 + 2 * vr.toNat + 1))) = true
          · simp only [heq, ↓reduceIte]
            rw [hvregP vr (beq_iff_eq.mp heq), hm0.hvregs vr]
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
            rw [eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
              (fun idx hi hm => hB23 _ idx hi hm) hfbHi,
              eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
                (fun idx hi hm => hB23 _ idx hi hm) hfbLo, ← hv23]
        · intro g hg31
          have hlt := g.isLt
          dsimp only [buildPostLoopState]
          rw [BTree.get_ofFn 5 _ g.toNat hlt]
          by_cases hg21 : Nat.beq g.toNat 21 = true
          · simp only [hg21, ↓reduceIte, evalKExpr, envP, mkPostLoopEnv]
            have hgEq : g = 21#5 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hg21)
            subst hgEq; simpa using hrcf
          · have hg21F := Bool.eq_false_iff.mpr hg21
            simp only [hg21F, Bool.false_eq_true, ↓reduceIte]
            by_cases hgc : Nat.beq g.toNat rCnt.toNat = true
            · simp only [hgc, ↓reduceIte, evalKExpr]
              have hgEq : g = rCnt := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hgc)
              subst hgEq; exact hcntf
            · have hgcF := Bool.eq_false_iff.mpr hgc
              simp only [hgcF, Bool.false_eq_true, ↓reduceIte]
              by_cases hgVar : (stBody.gprs.get g.toNat == .var (200 + g.toNat)) = true
              · simp only [hgVar, ↓reduceIte]
                rw [hgprP g hg31 (beq_iff_eq.mp hgVar), hm0.hgprs g hg31]
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
      have hspOut : KSpatial cfg envP (buildPostLoopState baseOut rCnt stPre stBody) F =
          ((env0.rcBase ↦ᵣ mlkemData01Bytes) ∗
            (BTreeMem (env0.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tAPost ∗
              (BTreeMem (env0.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB
                (evalMemTree env0 stPre.memB) ∗ F))) := by
        dsimp only [KSpatial, buildPostLoopState]; rw [htAPEq, htBPEq]; simp [envP, mkPostLoopEnv]
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

private theorem btreeBytesFrom_eq_range (start : Nat) :
    ∀ (n : Nat) (t : BTree (BitVec 64) 9),
      btreeBytesFrom start n t =
        ((List.range n).map fun j => unpackLane64 (t.get (start + j))).flatten := by
  intro n
  induction n with
  | zero => intro _; simp [btreeBytesFrom]
  | succ k ih =>
      intro t
      rw [btreeBytesFrom_split start k 1 t, ih t, List.range_succ, List.map_append,
        List.flatten_append]
      simp [btreeBytesFrom]

theorem btreeBytesFrom_eq_extractRate_21 {start : Nat} {t : BTree (BitVec 64) 9} {s : KeccakState}
    (h : ∀ j, j < 21 → t.get (start + j) = s.getD j 0#64) :
    btreeBytesFrom start 21 t = keccakExtractRate 21 s := by
  rw [btreeBytesFrom_eq_range, keccakExtractRate]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.mp hj)]

theorem rejBufReadable_of_btreeMem {basePtr sqAddr : BitVec 64} {offWords nChunks len : Nat}
    {t : BTree (BitVec 64) 9} {buf : List (BitVec 8)}
    (haddr : sqAddr = basePtr + BitVec.ofNat 64 (8 * offWords))
    (hbound : offWords + 3 * nChunks ≤ len)
    (hbuf : btreeBytesFrom offWords (3 * nChunks) t = buf) :
    RejBufReadable sqAddr buf nChunks (BTreeMem basePtr len t) := by
  intro off hoff
  rw [BTreeMem_eq_bytes]
  have hlenSplit : len = offWords + (3 * nChunks + (len - offWords - 3 * nChunks)) := by omega
  have hbs : btreeBytes len t =
      btreeBytesFrom 0 offWords t ++
        (buf ++ btreeBytesFrom (offWords + 3 * nChunks) (len - offWords - 3 * nChunks) t) := by
    conv_lhs => unfold btreeBytes; rw [hlenSplit]
    rw [btreeBytesFrom_split 0 offWords (3 * nChunks + (len - offWords - 3 * nChunks)) t,
      btreeBytesFrom_split (0 + offWords) (3 * nChunks) (len - offWords - 3 * nChunks) t,
      Nat.zero_add, hbuf]
  have hpreLen : (btreeBytesFrom 0 offWords t).length = 8 * offWords :=
    btreeBytesFrom_length 0 offWords t
  have hbufLen : buf.length = 24 * nChunks := by
    rw [← hbuf, btreeBytesFrom_length]; omega
  have htotLen : 8 * offWords + off < (btreeBytes len t).length := by
    unfold btreeBytes; rw [btreeBytesFrom_length]; omega
  have hgetD : (btreeBytes len t).getD (8 * offWords + off) 0#8 = buf.getD off 0#8 := by
    rw [hbs]
    simp only [List.getD, List.getElem?_append, hpreLen,
      show ¬(8 * offWords + off < 8 * offWords) by omega, ↓reduceIte,
      show 8 * offWords + off - 8 * offWords = off by omega,
      show off < buf.length by omega]
  rw [← hgetD]
  exact SepLoad8.of_pointsToBytes (sepConj_emp _).symm htotLen (by rw [haddr]; bv_omega)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
