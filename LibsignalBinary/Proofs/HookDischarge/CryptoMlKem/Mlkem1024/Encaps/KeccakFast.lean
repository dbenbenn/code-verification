/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base

/-!
# `kyber_encapsulate` (`B07`) — Kernel-Transparent Symbolic Keccak Runner (`KeccakFast`)

Defines `@[expose]` boolean equality on `KZFlag`, `KExpr × KExpr`, and `BTree` so `rfl_kernel`
reduces `runAndCheckKProgFast` certificates under Lean 4 `module` encapsulation, together with the
soundness bridge `runAndCheckKProg_of_fast` to `Seg2Base.runAndCheckKProg`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast

open Arm64 BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (fetchWordTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KExpr KSlot KState KZFlag runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  blk07NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  anfMatchesSpec checkKeccakLoop07 mkBaseState mkLoopInitState readSlot slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg (
  buildPostLoopState mapBodyExpr stateVarsLt stepKLoopSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep checkLoopInputs runAndCheckKProg runKProgSteps validSpecVar)

@[expose] def kzFlagBeq : KZFlag → KZFlag → Bool
  | .constBool a, .constBool b => a == b
  | .loopDone, .loopDone => true
  | _, _ => false

theorem kzFlagBeq_refl (a : KZFlag) : kzFlagBeq a a = true := by
  cases a <;> simp [kzFlagBeq]

theorem kzFlagBeq_eq_true {a b : KZFlag} (h : kzFlagBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [kzFlagBeq] at h ⊢
  exact h

theorem kzFlagBeq_eq (a b : KZFlag) : kzFlagBeq a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [kzFlagBeq_refl a]
  · cases hb : kzFlagBeq a b
    · simp [h]
    · exact absurd (kzFlagBeq_eq_true hb) h

@[expose] def optKZFlagBeq : Option KZFlag → Option KZFlag → Bool
  | none, none => true
  | some a, some b => kzFlagBeq a b
  | _, _ => false

theorem optKZFlagBeq_eq (a b : Option KZFlag) : optKZFlagBeq a b = (a == b) := by
  by_cases h : a = b
  · subst h; cases a <;> simp [optKZFlagBeq, kzFlagBeq_refl]
  · cases a <;> cases b <;> simp_all [optKZFlagBeq, kzFlagBeq_eq]

theorem kexprBeq_refl : ∀ (x : KExpr), x.beq x = true
  | .var a => Nat.beq_refl a
  | .const64 a => beq_self_eq_true a
  | .spAdd a => beq_self_eq_true a
  | .rcAdd a => beq_self_eq_true a
  | .rcVal a => Nat.beq_refl a
  | .rcLoopOff => rfl
  | .rcLoopPtr => rfl
  | .rcLoopNext => rfl
  | .rcLoopVal => rfl
  | .xor a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .bic a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .and64 a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .or64 a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .add64 a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .insByte0 a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .bsl m a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl m, kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .bitOp m a b => by dsimp only [KExpr.beq]; rw [kexprBeq_refl m, kexprBeq_refl a, kexprBeq_refl b]; rfl
  | .shl a s => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, Nat.beq_refl s]; rfl
  | .ushr a s => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, Nat.beq_refl s]; rfl
  | .rotl a s => by dsimp only [KExpr.beq]; rw [kexprBeq_refl a, Nat.beq_refl s]; rfl

theorem kexprBeq_eq (a b : KExpr) : a.beq b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [kexprBeq_refl a]
  · cases hb : a.beq b
    · simp [h]
    · exact absurd (KExpr.beq_eq_true hb) h

@[expose] def kexprPairBeq (p q : KExpr × KExpr) : Bool :=
  p.1.beq q.1 && p.2.beq q.2

theorem kexprPairBeq_eq (p q : KExpr × KExpr) : kexprPairBeq p q = (p == q) := by
  by_cases h : p = q
  · subst h; rcases p with ⟨p1, p2⟩; simp [kexprPairBeq, kexprBeq_refl]
  · cases hb : kexprPairBeq p q
    · simp [h]
    · simp only [kexprPairBeq, Bool.and_eq_true] at hb
      exact absurd (Prod.ext (KExpr.beq_eq_true hb.1) (KExpr.beq_eq_true hb.2)) h

@[expose] def btreeKExprBeq : {d : Nat} → BTree KExpr d → BTree KExpr d → Bool
  | 0, .leaf a, .leaf b => a.beq b
  | _ + 1, .node l1 h1, .node l2 h2 => btreeKExprBeq l1 l2 && btreeKExprBeq h1 h2

theorem btreeKExprBeq_refl : ∀ {d : Nat} (t : BTree KExpr d), btreeKExprBeq t t = true
  | 0, .leaf a => kexprBeq_refl a
  | _ + 1, .node l h => by simp [btreeKExprBeq, btreeKExprBeq_refl l, btreeKExprBeq_refl h]

theorem btreeKExprBeq_eq_true :
    ∀ {d : Nat} {t1 t2 : BTree KExpr d}, btreeKExprBeq t1 t2 = true → t1 = t2
  | 0, .leaf _, .leaf _, h => congrArg BTree.leaf (KExpr.beq_eq_true h)
  | _ + 1, .node l1 h1, .node l2 h2, h => by
      simp only [btreeKExprBeq, Bool.and_eq_true] at h
      rw [btreeKExprBeq_eq_true h.1, btreeKExprBeq_eq_true h.2]

theorem btreeKExprBeq_eq {d : Nat} (t1 t2 : BTree KExpr d) :
    btreeKExprBeq t1 t2 = (t1 == t2) := by
  by_cases h : t1 = t2
  · subst h; simp [btreeKExprBeq_refl t1]
  · cases hb : btreeKExprBeq t1 t2
    · simp [h]
    · exact absurd (btreeKExprBeq_eq_true hb) h
@[expose] def checkKeccakLoop07Fast (cfg : KCfg) (wHead nBody : Nat)
    (rCnt : BitVec 5) (slots : List KSlot) : Option KState :=
  if Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 21#5) && (rCnt != 31#5) &&
     blk07NoRelocInRange wHead (wHead + nBody + 1) &&
     Nat.ble (wHead + nBody + 1) 10252 then
    match fetchWordTree07 (wHead + nBody) with
    | some (.bCond cond disp) =>
        if cond == .NE && disp == 0#64 - BitVec.ofNat 64 (4 * nBody) then
          match runKRange cfg wHead nBody (mkLoopInitState cfg rCnt slots) with
          | none => none
          | some stBody =>
              if optKZFlagBeq stBody.zFlag (some .loopDone) &&
                 (stBody.gprs.get rCnt.toNat).beq .rcLoopNext &&
                 (stBody.gprs.get 21).beq (.rcAdd 0#64) &&
                 btreeKExprBeq stBody.memB (mkBaseState rCnt).memB &&
                 (List.range 25).all (fun idx =>
                   let (eLo, eHi) := readSlot cfg stBody (slots.getD idx (.vreg 0))
                   anfMatchesSpec eLo 0 idx && anfMatchesSpec eHi 25 idx)
              then some stBody
              else none
        else none
    | _ => none
  else none

theorem checkKeccakLoop07Fast_eq (cfg : KCfg) (wHead nBody : Nat)
    (rCnt : BitVec 5) (slots : List KSlot) :
    checkKeccakLoop07Fast cfg wHead nBody rCnt slots =
      checkKeccakLoop07 cfg wHead nBody rCnt slots := by
  unfold checkKeccakLoop07Fast checkKeccakLoop07
  split
  · cases fetchWordTree07 (wHead + nBody) with
    | none => rfl
    | some inst =>
        cases inst <;> try rfl
        rename_i cond disp
        dsimp only
        split
        · cases runKRange cfg wHead nBody (mkLoopInitState cfg rCnt slots) with
          | none => rfl
          | some stBody =>
              dsimp only
              rw [optKZFlagBeq_eq, kexprBeq_eq, kexprBeq_eq, btreeKExprBeq_eq]
        · rfl
  · rfl

@[expose] def buildPostLoopStateFast (baseOut : Nat) (rCnt : BitVec 5) (stPre stBody : KState) : KState :=
  { vregs := BTree.ofFn 5 (fun vr =>
      let pB := stBody.vregs.get vr
      if kexprPairBeq pB (.var (100 + 2 * vr), .var (100 + 2 * vr + 1)) then stPre.vregs.get vr
      else
        (mapBodyExpr baseOut (baseOut + 50 + 2 * vr) pB.1,
         mapBodyExpr baseOut (baseOut + 50 + 2 * vr + 1) pB.2))
    gprs := BTree.ofFn 5 (fun g =>
      if Nat.beq g 21 then .rcAdd 0#64
      else if Nat.beq g rCnt.toNat then .const64 192#64
      else if (stBody.gprs.get g).beq (.var (200 + g)) then stPre.gprs.get g
      else .var (baseOut + 114 + g))
    memA := BTree.ofFn 9 (fun i =>
      let eB := stBody.memA.get i
      if eB.beq (.var (300 + i)) then stPre.memA.get i
      else mapBodyExpr baseOut (baseOut + 146 + i) eB)
    memB := stPre.memB
    zFlag := some (.constBool true) }

theorem buildPostLoopStateFast_eq (baseOut : Nat) (rCnt : BitVec 5) (stPre stBody : KState) :
    buildPostLoopStateFast baseOut rCnt stPre stBody =
      buildPostLoopState baseOut rCnt stPre stBody := by
  unfold buildPostLoopStateFast buildPostLoopState
  simp only [kexprPairBeq_eq, kexprBeq_eq]

@[expose] def stepKLoopSymFast (cfg : KCfg) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) : Option KState :=
  if Nat.ble 100 baseOut && stateVarsLt baseOut stPre &&
     Nat.beq slots.length 25 && slots.all (slotValid cfg) &&
     (rCnt != 31#5) &&
     (stPre.gprs.get 21).beq (.rcAdd 0#64) &&
     (stPre.gprs.get rCnt.toNat).beq (.const64 0#64) then
    match checkKeccakLoop07Fast cfg wHead nBody rCnt slots with
    | none => none
    | some stBody => some (buildPostLoopStateFast baseOut rCnt stPre stBody)
  else none

theorem stepKLoopSymFast_eq (cfg : KCfg) (wHead nBody : Nat) (rCnt : BitVec 5)
    (slots : List KSlot) (baseOut : Nat) (stPre : KState) :
    stepKLoopSymFast cfg wHead nBody rCnt slots baseOut stPre =
      stepKLoopSym cfg wHead nBody rCnt slots baseOut stPre := by
  unfold stepKLoopSymFast stepKLoopSym
  rw [kexprBeq_eq, kexprBeq_eq]
  split
  · rw [checkKeccakLoop07Fast_eq]
    cases checkKeccakLoop07 cfg wHead nBody rCnt slots with
    | none => rfl
    | some stBody => dsimp only; rw [buildPostLoopStateFast_eq]
  · rfl

@[expose] def runKProgStepsFast (cfg : KCfg) (wLo wHi initBnd : Nat) :
    Nat → List Nat → List KProgStep → KState → Option (Nat × List Nat × KState)
  | wCur, bases, [], st => some (wCur, bases, st)
  | wCur, bases, .range w count :: rest, st =>
      if Nat.beq wCur w && Nat.ble wLo w && Nat.ble (w + count) wHi then
        match runKRange cfg w count st with
        | none => none
        | some st' => runKProgStepsFast cfg wLo wHi initBnd (w + count) bases rest st'
      else none
  | wCur, bases, .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, st =>
      if Nat.beq wCur wHead && Nat.ble initBnd baseOut &&
         bases.all (fun b => Nat.ble (b + 658) baseOut) &&
         checkLoopInputs cfg (validSpecVar initBnd bases) st slots expLo expHi then
        match stepKLoopSymFast cfg wHead nBody rCnt slots baseOut st with
        | none => none
        | some st' =>
            runKProgStepsFast cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      else none

theorem runKProgStepsFast_eq (cfg : KCfg) (wLo wHi initBnd : Nat) :
    ∀ (wCur : Nat) (bases : List Nat) (steps : List KProgStep) (st : KState),
      runKProgStepsFast cfg wLo wHi initBnd wCur bases steps st =
        runKProgSteps cfg wLo wHi initBnd wCur bases steps st
  | _, _, [], _ => rfl
  | wCur, bases, .range w count :: rest, st => by
      unfold runKProgStepsFast runKProgSteps
      split
      · cases runKRange cfg w count st with
        | none => rfl
        | some st' => exact runKProgStepsFast_eq cfg wLo wHi initBnd (w + count) bases rest st'
      · rfl
  | wCur, bases, .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, st => by
      unfold runKProgStepsFast runKProgSteps
      split
      · rw [stepKLoopSymFast_eq]
        cases stepKLoopSym cfg wHead nBody rCnt slots baseOut st with
        | none => rfl
        | some st' =>
            exact runKProgStepsFast_eq cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      · rfl

@[expose] def runAndCheckKProgFast (cfg : KCfg) (wLo wHi wStart wEnd initBnd : Nat)
    (steps : List KProgStep) (st0 : KState)
    (chk : (Nat → Bool) → KState → Bool) : Bool :=
  blk07NoRelocInRange wLo wHi && Nat.ble wHi 10252 &&
  match runKProgStepsFast cfg wLo wHi initBnd wStart [] steps st0 with
  | none => false
  | some (wFinal, finalBases, stEnd) =>
      Nat.beq wFinal wEnd && chk (validSpecVar initBnd finalBases) stEnd

theorem runAndCheckKProg_of_fast {cfg : KCfg} {wLo wHi wStart wEnd initBnd : Nat}
    {steps : List KProgStep} {st0 : KState} {chk : (Nat → Bool) → KState → Bool}
    (h : runAndCheckKProgFast cfg wLo wHi wStart wEnd initBnd steps st0 chk = true) :
    runAndCheckKProg cfg wLo wHi wStart wEnd initBnd steps st0 chk = true := by
  unfold runAndCheckKProgFast at h
  unfold runAndCheckKProg
  rwa [runKProgStepsFast_eq] at h

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast
