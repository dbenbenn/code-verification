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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Anf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import

/-!
# `encapsulate1_serialized` (`B03`) — Post-Loop Symbolic Transition & Squeeze Bridges (`Seg2Prog`)

Variable-bound congruence (`exprVarsLt`, `stateVarsLt`), 1-lane & 2-lane symbolic post-loop state
transition (`stepKLoopSym`, `sepWP_of_stepKLoop`), `TreeMem` ↔ `keccakExtractRate` /
`RejBufReadable` squeeze bridges, and concrete slot tables (`slotsL1..slotsL8`, `inv01Slots`,
`inv2Slots`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  KeccakState keccakExtractRate keccakF1600 unpackLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Anf (
  anfBeq checkAnfLane keccakSpecRoundExpr toAnf?)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KPFlag KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeWords btreeWords_length treeMem_eq_pointsToBytes wordsToBytes wordsToBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KConstsLoOpt KSpatial KStateMatches evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  btree_ext_get checkKeccakLoop03 readSlot readSlot_holds sepWP_of_keccakLoop24
  slotHolds slotValid truncate64_append ushr64_truncate64_append)

attribute [local irreducible] keccakF1600 blkPC03

/-! ## 1. `btreeAll`, `exprVarsLt`, `stateVarsLt`, & Variable-Bound Congruence -/

@[expose] def btreeAll {α : Type} (p : α → Bool) : {d : Nat} → BTree α d → Bool
  | 0, .leaf v => p v
  | _ + 1, .node lo hi => btreeAll p lo && btreeAll p hi

theorem btreeAll_get {α : Type} (p : α → Bool) :
    ∀ {d : Nat} (t : BTree α d),
      btreeAll p t = true → ∀ i, i < 2 ^ d → p (t.get i) = true
  | 0, .leaf _, h, i, hi => by
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

theorem btreeAll_mono {α : Type} {p q : α → Bool} (hpq : ∀ x, p x = true → q x = true) :
    ∀ {d : Nat} (t : BTree α d), btreeAll p t = true → btreeAll q t = true
  | 0, .leaf v, h => hpq v h
  | _ + 1, .node lo hi, h => by
      simp only [btreeAll, Bool.and_eq_true] at h ⊢
      exact ⟨btreeAll_mono hpq lo h.1, btreeAll_mono hpq hi h.2⟩

@[expose] def exprVarsLt (bound : Nat) : KExpr → Bool
  | .var id => Nat.blt id bound
  | .const64 _ | .spAdd _ | .rcAdd _ | .rcVal _
  | .rcLoopOff | .rcLoopPtr | .rcLoopNext | .rcLoopVal => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprVarsLt bound a && exprVarsLt bound b
  | .bsl x y z => exprVarsLt bound x && exprVarsLt bound y && exprVarsLt bound z
  | .shl a _ | .ushr a _ | .rotl a _ | .clamp64 a => exprVarsLt bound a

theorem exprVarsLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) :
    ∀ (e : KExpr), exprVarsLt b1 e = true → exprVarsLt b2 e = true := by
  intro e
  induction e with
  | var id => simp only [exprVarsLt, Nat.blt_eq]; omega
  | const64 _ | spAdd _ | rcAdd _ | rcVal _ | rcLoopOff | rcLoopPtr | rcLoopNext | rcLoopVal =>
      simp [exprVarsLt]
  | xor a b iha ihb | bic a b iha ihb | and64 a b iha ihb | or64 a b iha ihb
  | add64 a b iha ihb | insByte0 a b iha ihb =>
      simp only [exprVarsLt, Bool.and_eq_true]; exact fun h => ⟨iha h.1, ihb h.2⟩
  | bsl x y z ihx ihy ihz =>
      simp only [exprVarsLt, Bool.and_eq_true]; exact fun h => ⟨⟨ihx h.1.1, ihy h.1.2⟩, ihz h.2⟩
  | shl a _ ih | ushr a _ ih | rotl a _ ih | clamp64 a ih => exact ih

theorem evalKExpr_congr_vars {bound : Nat} {env1 env2 : KEnv}
    (hsp : env1.sp = env2.sp) (hrc : env1.rcBase = env2.rcBase) (hrl : env1.rLoop = env2.rLoop)
    (hvars : ∀ id, id < bound → env1.vars id = env2.vars id) :
    ∀ (e : KExpr), exprVarsLt bound e = true → evalKExpr env1 e = evalKExpr env2 e := by
  intro e
  induction e with
  | var id => simp only [exprVarsLt, Nat.blt_eq, evalKExpr]; exact fun h => hvars id h
  | const64 _ | rcVal _ => intro _; rfl
  | spAdd _ => intro _; simp [evalKExpr, hsp]
  | rcAdd _ => intro _; simp [evalKExpr, hrc]
  | rcLoopOff | rcLoopNext | rcLoopVal => intro _; simp [evalKExpr, hrl]
  | rcLoopPtr => intro _; simp [evalKExpr, hrc, hrl]
  | xor a b iha ihb | bic a b iha ihb | and64 a b iha ihb | or64 a b iha ihb
  | add64 a b iha ihb | insByte0 a b iha ihb =>
      simp only [exprVarsLt, Bool.and_eq_true, evalKExpr]; intro h; rw [iha h.1, ihb h.2]
  | bsl x y z ihx ihy ihz =>
      simp only [exprVarsLt, Bool.and_eq_true, evalKExpr]
      intro h; rw [ihx h.1.1, ihy h.1.2, ihz h.2]
  | shl a _ ih | ushr a _ ih | rotl a _ ih | clamp64 a ih =>
      simp only [exprVarsLt, evalKExpr]; intro h; rw [ih h]

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
      idx < 25 ∧ checkAnfLane e base idx = true := by
  intro rem
  induction rem with
  | zero => intro _ _ h; cases h
  | succ r ih =>
      intro idx hle h
      unfold findSpecLaneAux at h; dsimp only at h
      cases hq : toAnf? (keccakSpecRoundExpr base (25 - (r + 1))) with
      | none => simp only [hq] at h; exact ih (by omega) h
      | some q =>
          simp only [hq] at h; split at h
          case isTrue hbeq =>
            simp only [Option.some.injEq] at h; subst h
            exact ⟨by omega, by simp only [checkAnfLane, hp, hq]; exact hbeq⟩
          case isFalse => exact ih (by omega) h

theorem findSpecLane_sound {e : KExpr} {base idx : Nat}
    (h : findSpecLane e base = some idx) :
    idx < 25 ∧ checkAnfLane e base idx = true := by
  unfold findSpecLane at h
  cases hp : toAnf? e with
  | none => simp [hp] at h
  | some p => simp only [hp] at h; exact findSpecLaneAux_sound hp 25 (Nat.le_refl _) h

@[expose] def mapBodyExpr (isPair : Bool) (baseOut fallbackId : Nat) (e : KExpr) : KExpr :=
  match findSpecLane e 0 with
  | some idx => .var (baseOut + idx)
  | none =>
      if isPair then
        match findSpecLane e 25 with
        | some idx => .var (baseOut + 25 + idx)
        | none => .var fallbackId
      else .var fallbackId

theorem exprVarsLt_mapBodyExpr {isPair : Bool} {bound baseOut fallbackId : Nat}
    (hb : baseOut + 50 ≤ bound) (hfb : fallbackId < bound) (e : KExpr) :
    exprVarsLt bound (mapBodyExpr isPair baseOut fallbackId e) = true := by
  unfold mapBodyExpr
  cases h0 : findSpecLane e 0 with
  | some idx =>
      have hi := (findSpecLane_sound h0).1
      simp only [exprVarsLt, Nat.blt_eq]; omega
  | none =>
      cases isPair with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, exprVarsLt, Nat.blt_eq]; exact hfb
      | true =>
          simp only [↓reduceIte]
          cases h25 : findSpecLane e 25 with
          | some idx =>
              have hi := (findSpecLane_sound h25).1
              simp only [exprVarsLt, Nat.blt_eq]; omega
          | none => simp only [exprVarsLt, Nat.blt_eq]; exact hfb

@[expose] def evalSlotsLo (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (readSlot cfg st (slots.getD idx.1 (.vreg 0))).1

@[expose] def evalSlotsHi (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (readSlot cfg st (slots.getD idx.1 (.vreg 0))).2

theorem evalSlotsLo_size (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
    (evalSlotsLo cfg env st slots).size = 25 := by simp [evalSlotsLo]

theorem evalSlotsHi_size (cfg : KCfg) (env : KEnv) (st : KState) (slots : List KSlot) :
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

@[expose] def kpairBeq (p q : KExpr × KExpr) : Bool := p.1.beq q.1 && p.2.beq q.2

theorem kpairBeq_eq_true {p q : KExpr × KExpr} (h : kpairBeq p q = true) : p = q := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [kpairBeq, Bool.and_eq_true] at h; rw [KExpr.beq_eq_true h.1, KExpr.beq_eq_true h.2]

@[expose] def kpflagOptBeq : Option KPFlag → Option KPFlag → Bool
  | none, none | some .loopDone, some .loopDone => true
  | some (.subs64 a1 r1), some (.subs64 a2 r2) => a1.beq a2 && (r1 == r2)
  | _, _ => false

theorem kpflagOptBeq_eq_true : ∀ {a b : Option KPFlag}, kpflagOptBeq a b = true → a = b
  | none, none, _ | some .loopDone, some .loopDone, _ => rfl
  | some (.subs64 _ _), some (.subs64 _ _), h => by
      simp only [kpflagOptBeq, Bool.and_eq_true] at h
      rw [KExpr.beq_eq_true h.1, beq_iff_eq.mp h.2]

@[expose] def buildPostLoopState (isPair : Bool) (baseOut : Nat) (rCnt : BitVec 5)
    (stPre stBody : KState) : KState :=
  { vregs := BTree.ofFn 5 (fun vr =>
      let pB := stBody.vregs.get vr
      if kpairBeq pB (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)) then stPre.vregs.get vr
      else (mapBodyExpr isPair baseOut (baseOut + 50 + 2 * vr) pB.1,
            mapBodyExpr isPair baseOut (baseOut + 50 + 2 * vr + 1) pB.2))
    gprs := BTree.ofFn 5 (fun g =>
      if Nat.beq g 19 then .rcAdd 0#64
      else if Nat.beq g rCnt.toNat then .const64 192#64
      else if (stBody.gprs.get g).beq (.var (200 + g)) then stPre.gprs.get g
      else .var (baseOut + 114 + g))
    memA := BTree.ofFn 9 (fun i =>
      let eB := stBody.memA.get i
      if eB.beq (.var (300 + i)) then stPre.memA.get i
      else mapBodyExpr isPair baseOut (baseOut + 146 + i) eB)
    memB := stPre.memB
    pstateFlag := some (.subs64 (.const64 192#64) 192#64) }

@[expose] def stepKLoopSym (cfg : KCfg) (isPair : Bool) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) : Option KState :=
  if Nat.ble 100 baseOut && stateVarsLt baseOut stPre &&
     Nat.beq slots.length 25 && slots.all (slotValid cfg) && (rCnt != 31#5) &&
     (stPre.gprs.get 19).beq (.rcAdd 0#64) &&
     (stPre.gprs.get rCnt.toNat).beq (.const64 0#64) then
    match checkKeccakLoop03 cfg isPair wHead nBody rCnt slots with
    | none => none
    | some stBody => some (buildPostLoopState isPair baseOut rCnt stPre stBody)
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

private theorem eval_mapBodyExpr {isPair : Bool} {env0 env23 : KEnv} {baseOut fallbackId : Nat}
    {sA sB : KeccakState} {sf : State} {tA : BTree (BitVec 64) 9} {e : KExpr}
    (hA : ∀ idx, idx < 25 → checkAnfLane e 0 idx = true → evalKExpr env23 e = sA.getD idx 0#64)
    (hB : isPair = true → ∀ idx, idx < 25 → checkAnfLane e 25 idx = true →
      evalKExpr env23 e = sB.getD idx 0#64)
    (hfb : (mkPostLoopEnv env0 baseOut sA sB sf tA).vars fallbackId = evalKExpr env23 e) :
    evalKExpr (mkPostLoopEnv env0 baseOut sA sB sf tA) (mapBodyExpr isPair baseOut fallbackId e) =
      evalKExpr env23 e := by
  unfold mapBodyExpr
  cases h0 : findSpecLane e 0 with
  | some idx =>
      rcases findSpecLane_sound h0 with ⟨hi, hm⟩
      rw [hA idx hi hm]
      simp [evalKExpr, mkPostLoopEnv, show ¬(baseOut + idx < baseOut) by omega,
        show baseOut + idx < baseOut + 25 by omega, show baseOut + idx - baseOut = idx by omega]
  | none =>
      cases hp : isPair with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, evalKExpr]; exact hfb
      | true =>
          simp only [↓reduceIte]
          cases h25 : findSpecLane e 25 with
          | some idx =>
              rcases findSpecLane_sound h25 with ⟨hi, hm⟩
              rw [hB hp idx hi hm]
              simp [evalKExpr, mkPostLoopEnv, show ¬(baseOut + 25 + idx < baseOut) by omega,
                show ¬(baseOut + 25 + idx < baseOut + 25) by omega,
                show baseOut + 25 + idx < baseOut + 50 by omega,
                show baseOut + 25 + idx - (baseOut + 25) = idx by omega]
          | none => exact hfb

theorem stateVarsLt_stepKLoopSym {cfg : KCfg} {isPair : Bool} {wHead nBody : Nat} {rCnt : BitVec 5}
    {slots : List KSlot} {baseOut : Nat} {stPre stPost : KState}
    (h : stepKLoopSym cfg isPair wHead nBody rCnt slots baseOut stPre = some stPost) :
    stateVarsLt (baseOut + 658) stPost = true := by
  unfold stepKLoopSym at h
  split at h; case isFalse => cases h
  case isTrue hhdr =>
  simp only [Bool.and_eq_true] at hhdr
  have hsv : stateVarsLt baseOut stPre = true := hhdr.1.1.1.1.1.2
  simp only [stateVarsLt, Bool.and_eq_true] at hsv
  rcases hsv with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hc : checkKeccakLoop03 cfg isPair wHead nBody rCnt slots with
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
    {cfg : KCfg} (hv : KCfgWf cfg) {isPair : Bool} {env0 : KEnv}
    {wHead nBody : Nat} {rCnt : BitVec 5} {slots : List KSlot} {baseOut : Nat}
    {stPre stPost : KState}
    (hstep : stepKLoopSym cfg isPair wHead nBody rCnt slots baseOut stPre = some stPost)
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
      SepWP (blkPC03.rebase b (fun _ => none)) tgt sf (KSpatial cfg envPost stPost F) post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 stPre F) post oom := by
  unfold stepKLoopSym at hstep
  split at hstep; case isFalse => cases hstep
  case isTrue hhdr =>
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, bne_iff_ne] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨⟨_hb100, hsvPre⟩, hlen⟩, hslVal⟩, hne31⟩, hrcB⟩, hcntB⟩
  have hrcExpr : stPre.gprs.get 19 = .rcAdd 0#64 := KExpr.beq_eq_true hrcB
  have hcntExpr : stPre.gprs.get rCnt.toNat = .const64 0#64 := KExpr.beq_eq_true hcntB
  simp only [stateVarsLt, Bool.and_eq_true] at hsvPre
  rcases hsvPre with ⟨⟨⟨hvPre, hgPre⟩, hmAPre⟩, hmBPre⟩
  cases hchk : checkKeccakLoop03 cfg isPair wHead nBody rCnt slots with
  | none => simp [hchk] at hstep
  | some stBody =>
      simp only [hchk, Option.some.injEq] at hstep; subst hstep
      let sA0 := evalSlotsLo cfg env0 stPre slots
      let sB0 := evalSlotsHi cfg env0 stPre slots
      have hrc0 : s0.readReg64 (.gpr 19#5) = env0.rcBase := by
        have h := hm0.hgprs 19#5 (by decide)
        change _ = evalKExpr env0 (stPre.gprs.get 19) at h
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
      intro sf env23 hpcf hrunf hspf hspAf hrcf hcntf hps23
        hgprP hvregP hmemAP hA23 hB23 hm23
      let tAPost := evalMemTree env23 stBody.memA
      let envP := mkPostLoopEnv env0 baseOut (keccakF1600 sA0) (keccakF1600 sB0) sf tAPost
      have hvarsP : ∀ id, id < baseOut → envP.vars id = env0.vars id :=
        fun id hid => by simp [envP, mkPostLoopEnv, hid]
      have htAPEq : evalMemTree envP
          (BTree.ofFn 9 fun i =>
            let eB := stBody.memA.get i
            if eB.beq (.var (300 + i)) then stPre.memA.get i
            else mapBodyExpr isPair baseOut (baseOut + 146 + i) eB) = tAPost := by
        apply btree_ext_get; intro i hi
        simp only [evalMemTree, BTree.get_map]; rw [BTree.get_ofFn 9 _ i hi]
        by_cases heq : (stBody.memA.get i).beq (.var (300 + i)) = true
        · simp only [heq, ↓reduceIte]
          have hv0 := hmemAP i hi (KExpr.beq_eq_true heq)
          have hcongr := evalKExpr_congr_vars (env1 := envP) (env2 := env0) rfl rfl rfl hvarsP
            (stPre.memA.get i) (btreeAll_get _ stPre.memA hmAPre i hi)
          rw [hcongr]; simpa [tAPost, evalMemTree, BTree.get_map] using hv0.symm
        · simp only [Bool.eq_false_iff.mpr heq, Bool.false_eq_true, ↓reduceIte]
          have hfb : envP.vars (baseOut + 146 + i) = evalKExpr env23 (stBody.memA.get i) := by
            change i < 512 at hi
            simp [envP, mkPostLoopEnv, tAPost, evalMemTree, BTree.get_map,
              show ¬(baseOut + 146 + i < baseOut) by omega, show ¬(baseOut + 146 + i < baseOut + 25) by omega,
              show ¬(baseOut + 146 + i < baseOut + 50) by omega, show ¬(baseOut + 146 + i < baseOut + 114) by omega,
              show ¬(baseOut + 146 + i < baseOut + 146) by omega, show baseOut + 146 + i < baseOut + 658 by omega,
              show baseOut + 146 + i - (baseOut + 146) = i by omega]
          exact (eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
            (fun hp idx hi hm => hB23 hp _ idx hi hm) hfb).trans
            (BTree.get_map (evalKExpr env23) stBody.memA i).symm
      have htBPEq : evalMemTree envP stPre.memB = evalMemTree env0 stPre.memB :=
        evalMemTree_congr_vars hmBPre rfl rfl rfl hvarsP
      have hmP : KStateMatches envP (buildPostLoopState isPair baseOut rCnt stPre stBody) sf := by
        refine ⟨hspf, hspAf, ?_, ?_, hps23⟩
        · intro vr
          have hlt := vr.isLt
          dsimp only [buildPostLoopState]; rw [BTree.get_ofFn 5 _ vr.toNat hlt]
          by_cases heq : kpairBeq (stBody.vregs.get vr.toNat)
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
            rw [eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
              (fun hp idx hi hm => hB23 hp _ idx hi hm) hfbHi,
              eval_mapBodyExpr (fun idx hi hm => hA23 _ idx hi hm)
                (fun hp idx hi hm => hB23 hp _ idx hi hm) hfbLo, ← hv23]
        · intro g hg31
          have hlt := g.isLt
          dsimp only [buildPostLoopState]; rw [BTree.get_ofFn 5 _ g.toNat hlt]
          by_cases hg19 : Nat.beq g.toNat 19 = true
          · simp only [hg19, ↓reduceIte, evalKExpr, envP, mkPostLoopEnv]
            have hgEq : g = 19#5 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hg19)
            subst hgEq; simpa using hrcf
          · simp only [Bool.eq_false_iff.mpr hg19, Bool.false_eq_true, ↓reduceIte]
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
      have hspOut : KSpatial cfg envP (buildPostLoopState isPair baseOut rCnt stPre stBody) F =
          ((env0.rcBase ↦ᵣ mlkemData01Bytes) ∗ (KConstsLoOpt env0.sp cfg.hasConstsLo ∗
            (TreeMem (env0.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA tAPost ∗
              (TreeMem (env0.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB
                (evalMemTree env0 stPre.memB) ∗ F)))) := by
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

private theorem unpack64_eq_unpackLane64 (w : BitVec 64) : unpack64 w = unpackLane64 w := by
  unfold unpack64 unpackLane64
  have h (k : Nat) : w.extractLsb' k 8 = (w >>> k).truncate 8 := by
    ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]
  simp only [h]

theorem wordsToBytes_append (ws1 ws2 : List (BitVec 64)) :
    wordsToBytes (ws1 ++ ws2) = wordsToBytes ws1 ++ wordsToBytes ws2 := by
  induction ws1 <;> [rfl; simp [wordsToBytes, *, List.append_assoc]]

theorem btreeWords_split (start n1 n2 : Nat) (t : BTree (BitVec 64) 9) :
    btreeWords start (n1 + n2) t = btreeWords start n1 t ++ btreeWords (start + n1) n2 t := by
  induction n1 generalizing start with
  | zero => simp [btreeWords]
  | succ _ ih => simp only [Nat.succ_add, btreeWords, List.cons_append, ih (start + 1)]; congr 2

private theorem wordsToBytes_btreeWords_eq_range (start : Nat) :
    ∀ (n : Nat) (t : BTree (BitVec 64) 9),
      wordsToBytes (btreeWords start n t) =
        ((List.range n).map fun j => unpackLane64 (t.get (start + j))).flatten
  | 0, _ => by simp [btreeWords, wordsToBytes]
  | k + 1, t => by
      rw [btreeWords_split start k 1 t, wordsToBytes_append, wordsToBytes_btreeWords_eq_range start k t,
        List.range_succ, List.map_append, List.flatten_append]
      simp [btreeWords, wordsToBytes, unpack64_eq_unpackLane64]

theorem wordsToBytes_btreeWords_eq_extractRate_21 {start : Nat} {t : BTree (BitVec 64) 9}
    {s : KeccakState} (h : ∀ j, j < 21 → t.get (start + j) = s.getD j 0#64) :
    wordsToBytes (btreeWords start 21 t) = keccakExtractRate 21 s := by
  rw [wordsToBytes_btreeWords_eq_range, keccakExtractRate]
  congr 1; apply List.map_congr_left; intro j hj; rw [h j (List.mem_range.mp hj)]

theorem rejBufReadable_of_treeMem {basePtr sqAddr : BitVec 64} {offWords nChunks len : Nat}
    {t : BTree (BitVec 64) 9} {buf : List (BitVec 8)}
    (haddr : sqAddr = basePtr + BitVec.ofNat 64 (8 * offWords))
    (hbound : offWords + 3 * nChunks ≤ len)
    (hbuf : wordsToBytes (btreeWords offWords (3 * nChunks) t) = buf) :
    RejBufReadable sqAddr buf nChunks (TreeMem basePtr len t) := by
  intro off hoff
  let pre := wordsToBytes (btreeWords 0 offWords t)
  let suf := wordsToBytes (btreeWords (offWords + 3 * nChunks) (len - offWords - 3 * nChunks) t)
  have hbs : wordsToBytes (btreeWords 0 len t) = pre ++ (buf ++ suf) := by
    conv_lhs => rw [show len = offWords + (3 * nChunks + (len - offWords - 3 * nChunks)) by omega]
    rw [btreeWords_split 0 offWords, btreeWords_split (0 + offWords) (3 * nChunks),
      Nat.zero_add, wordsToBytes_append, wordsToBytes_append, hbuf]
  rw [treeMem_eq_pointsToBytes hbs]
  have hpreLen : pre.length = 8 * offWords := by dsimp [pre]; rw [wordsToBytes_length, btreeWords_length]
  have hbufLen : buf.length = 24 * nChunks := by rw [← hbuf, wordsToBytes_length, btreeWords_length]; omega
  have htotLen : 8 * offWords + off < (pre ++ (buf ++ suf)).length := by
    simp only [List.length_append, hpreLen, hbufLen]; omega
  have hgetD : (pre ++ (buf ++ suf)).getD (8 * offWords + off) 0#8 = buf.getD off 0#8 := by
    simp only [List.getD, List.getElem?_append, hpreLen, show ¬(8 * offWords + off < 8 * offWords) by omega,
      ↓reduceIte, show 8 * offWords + off - 8 * offWords = off by omega, show off < buf.length by omega]
  rw [← hgetD]
  exact SepLoad8.of_pointsToBytes (sepConj_emp _).symm htotLen (by rw [haddr]; bv_omega)

/-! ## 4. Concrete `B03` `Seg2` Keccak Loop & `+0x2580` Invariant Slot Tables -/

@[expose] def slotsL1 : List KSlot :=
  [.vreg 0, .vreg 28, .vreg 29, .vreg 8, .spillQ 1840, .vreg 19, .vreg 23, .spillQ 1536, .spillQ 1760, .spillQ 1776,
   .vreg 15, .vreg 11, .vreg 26, .vreg 12, .vreg 13, .vreg 30, .vreg 27, .vreg 5, .vreg 10, .vreg 7, .vreg 25, .vreg 24, .vreg 20, .vreg 17, .vreg 18]
@[expose] def slotsL2 : List KSlot :=
  [.vregLo 17, .vregLo 1, .vregLo 3, .vregLo 8, .spillD 1744, .vregLo 18, .vregLo 16, .vregLo 13, .vregLo 28, .vregLo 15,
   .vregLo 14, .vregLo 26, .vregLo 11, .vregLo 30, .vregLo 10, .vregLo 7, .vregLo 12, .vregLo 25, .vregLo 4, .vregLo 6, .vregLo 24, .vregLo 27, .vregLo 31, .vregLo 19, .vregLo 20]
@[expose] def slotsL3 : List KSlot :=
  [.vreg 6, .vreg 2, .vreg 3, .spillQ 1520, .spillQ 1824, .vreg 18, .vreg 11, .vreg 28, .spillQ 1808, .vreg 15,
   .vreg 8, .vreg 13, .vreg 30, .vreg 10, .vreg 12, .vreg 31, .vreg 25, .vreg 29, .vreg 9, .vreg 26, .vreg 17, .vreg 23, .vreg 20, .vreg 16, .vreg 21]
@[expose] def slotsL4 : List KSlot :=
  [.vreg 9, .spillQ 1680, .vreg 12, .vreg 4, .vreg 24, .vreg 19, .vreg 13, .spillQ 1856, .vreg 10, .vreg 22,
   .vreg 15, .vreg 14, .vreg 30, .vreg 31, .spillQ 2112, .spillQ 1792, .vreg 25, .vreg 29, .vreg 27, .vreg 6, .vreg 28, .vreg 23, .vreg 20, .vreg 16, .vreg 21]
@[expose] def slotsL5 : List KSlot :=
  [.vregLo 18, .vregLo 12, .vregLo 28, .spillD 1328, .vregLo 14, .vregLo 19, .vregLo 8, .spillD 1712, .spillD 1728, .vregLo 15,
   .vregLo 9, .vregLo 27, .vregLo 21, .vregLo 13, .vregLo 25, .vregLo 29, .vregLo 26, .vregLo 20, .vregLo 4, .vregLo 24, .vregLo 17, .vregLo 11, .vregLo 31, .spillD 2176, .vregLo 10]
@[expose] def slotsL6 : List KSlot :=
  [.vregLo 16, .spillD 1968, .vregLo 21, .spillD 1664, .vregLo 8, .spillD 1584, .spillD 1600, .spillD 1616, .spillD 1888, .vregLo 14,
   .spillD 1568, .vregLo 23, .vregLo 6, .spillD 1648, .vregLo 19, .vregLo 15, .vregLo 17, .vregLo 13, .vregLo 26, .vregLo 30, .vregLo 7, .vregLo 11, .vregLo 31, .spillD 2176, .vregLo 10]
@[expose] def slotsL7 : List KSlot :=
  [.vreg 18, .vreg 15, .spillQ 1984, .spillQ 2096, .spillQ 2160, .vreg 21, .vreg 16, .vreg 30, .vreg 14, .vreg 11,
   .vreg 8, .vreg 25, .vreg 9, .vreg 24, .vreg 22, .vreg 13, .vreg 23, .vreg 10, .vreg 31, .vreg 27, .vreg 12, .vreg 6, .vreg 7, .vreg 19, .vreg 28]
@[expose] def slotsL8 : List KSlot :=
  [.vregLo 18, .vregLo 26, .vregLo 10, .vregLo 9, .vregLo 13, .vregLo 8, .vregLo 25, .vregLo 28, .vregLo 15, .vregLo 14,
   .vregLo 11, .vregLo 23, .vregLo 21, .vregLo 22, .vregLo 12, .vregLo 30, .vregLo 24, .vregLo 20, .vregLo 6, .vregLo 5, .vregLo 27, .vregLo 7, .vregLo 29, .spillD 2176, .vregLo 19]
@[expose] def inv01Slots : List KSlot :=
  [.vreg 18, .vreg 15, .spillQ 1984, .vreg 10, .vreg 26, .vreg 12, .spillQ 1136, .vreg 21, .vreg 28, .vreg 11,
   .vreg 14, .vreg 25, .vreg 9, .vreg 24, .vreg 5, .spillQ 1792, .vreg 23, .spillQ 1120, .vreg 31, .vreg 27, .spillQ 1008, .vreg 17, .vreg 2, .vreg 3, .vreg 4]
@[expose] def inv2Slots : List KSlot :=
  [.spillD 1456, .spillD 1968, .spillD 1632, .vregLo 0, .vregLo 13, .spillD 1584, .spillD 1600, .spillD 1616, .spillD 1888, .spillD 2048,
   .spillD 1568, .spillD 1728, .spillD 1744, .vregLo 22, .spillD 2032, .spillD 1488, .spillD 1712, .spillD 1840, .vregLo 6, .vregLo 8, .spillD 1312, .vregLo 7, .vregLo 29, .spillD 2176, .vregLo 19]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
