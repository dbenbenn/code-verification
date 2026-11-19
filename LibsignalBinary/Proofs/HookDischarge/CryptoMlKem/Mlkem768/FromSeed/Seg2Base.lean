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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep

/-!
# `generate_keypair_compressed` (`B05`) — Segment 2 Shared Foundations (`Seg2Base`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakAbsorb keccakExtractRate keccakF1600 keccakPermuteN
  keccakZeroState packLane64 shake128BlockAt shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  keccakPermuteN_succ_right shake128FirstBlocks_three)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism (
  keccakAbsorb_21_lt168 keccakXorRate21 keccakXorRate21_getD_ge keccakXorRate21_getD_lt
  keccakXorRate21_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (blkPC05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf KSpatial KStateMatches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep (
  sepWP_of_runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  readSlot slotHolds slotValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  evalSlotsHi evalSlotsLo sepWP_of_stepKLoop stepKLoopSym)

/-! ## 1. Pure `rowSeed`, `preAbsorbState`, & `rowPermState` Characterizations -/

@[expose] def rhoW (rho : List (BitVec 8)) (idx : Nat) : BitVec 64 :=
  packLane64 rho (8 * idx)

@[expose] def rowSeed (rho : List (BitVec 8)) (row col : Nat) : List (BitVec 8) :=
  rho.take 32 ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col]

@[expose] def rowSeeds (rho : List (BitVec 8)) (row : Nat) : Nat → List (BitVec 8) :=
  fun col => rowSeed rho row col

theorem rowSeed_eq_of_len32 {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col : Nat) :
    rowSeed rho row col = rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col] := by
  simp [rowSeed, List.take_of_length_le (Nat.le_of_eq hrho)]

theorem rowSeed_length {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col : Nat) :
    (rowSeed rho row col).length = 34 := by
  rw [rowSeed_eq_of_len32 hrho]; simp [hrho]

@[expose] def preAbsorbLane (rho : List (BitVec 8)) (row col idx : Nat) : BitVec 64 :=
  if idx < 4 then rhoW rho idx
  else if idx = 4 then
    (BitVec.ofNat 8 row).zeroExtend 64 |||
      ((BitVec.ofNat 8 col).zeroExtend 64 <<< 8) |||
      0x00000000001f0000#64
  else if idx = 20 then 0x8000000000000000#64
  else 0#64

@[expose] def preAbsorbState (rho : List (BitVec 8)) (row col : Nat) : KeccakState :=
  Array.ofFn (n := 25) fun ⟨idx, _⟩ => preAbsorbLane rho row col idx

@[simp] theorem preAbsorbState_size (rho : List (BitVec 8)) (row col : Nat) :
    (preAbsorbState rho row col).size = 25 := by
  simp [preAbsorbState]

theorem preAbsorbState_getD (rho : List (BitVec 8)) (row col : Nat) {idx : Nat} (hidx : idx < 25) :
    (preAbsorbState rho row col).getD idx 0#64 = preAbsorbLane rho row col idx := by
  simp [preAbsorbState, Array.getD, hidx]

private theorem lastBlock168_getD {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (row col j : Nat) (hj : j < 168) :
    (keccakLastBlock 168 0x1f#8 (rowSeed rho row col)).getD j 0#8 =
      if j < 32 then rho.getD j 0#8
      else if j = 32 then BitVec.ofNat 8 row
      else if j = 33 then BitVec.ofNat 8 col
      else if j = 34 then 0x1f#8
      else if j = 167 then 0x80#8
      else 0#8 := by
  have hlen : (rowSeed rho row col).length = 34 := rowSeed_length hrho row col
  rw [keccakLastBlock, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some, hlen,
    show 34 / 168 = 0 by decide, show 34 % 168 = 34 by decide, Nat.zero_mul, List.drop_zero,
    show 168 - 1 = 167 by decide]
  by_cases hj32 : j < 32
  · have hj34 : j < 34 := by omega
    have hj167 : (j == 167) = false := beq_false_of_ne (by omega)
    simp only [hj32, hj34, hj167, ↓reduceIte, Bool.false_eq_true]
    rw [rowSeed_eq_of_len32 hrho, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  · by_cases heq32 : j = 32
    · subst heq32
      simp only [hj32, show (32 : Nat) < 34 by decide, show ((32 : Nat) == 167) = false by decide,
        ↓reduceIte, Bool.false_eq_true]
      rw [rowSeed_eq_of_len32 hrho, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hrho]; rfl
    · by_cases heq33 : j = 33
      · subst heq33
        simp only [hj32, heq32, show (33 : Nat) < 34 by decide,
          show ((33 : Nat) == 167) = false by decide, ↓reduceIte, Bool.false_eq_true]
        rw [rowSeed_eq_of_len32 hrho, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega), hrho]; rfl
      · by_cases heq34 : j = 34
        · subst heq34; rfl
        · by_cases heq167 : j = 167
          · subst heq167; simp
          · have hnot34 : ¬(j < 34) := by omega
            have hbeq34 : (j == 34) = false := beq_false_of_ne heq34
            have hbeq167 : (j == 167) = false := beq_false_of_ne heq167
            simp only [hj32, heq32, heq33, heq34, heq167, hnot34, hbeq34, hbeq167,
              ↓reduceIte, Bool.false_eq_true]

private theorem array_getElem_eq_getD64 (a : Array (BitVec 64)) (idx : Nat) (h : idx < a.size) :
    a[idx]'h = a.getD idx 0#64 := by
  simp only [Array.getD, h, ↓reduceDIte]; rfl

set_option maxHeartbeats 400000 in
theorem keccakAbsorb_rowSeed {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col : Nat) :
    keccakAbsorb 21 0x1f#8 (rowSeed rho row col) = keccakF1600 (preAbsorbState rho row col) := by
  have hlen : (rowSeed rho row col).length = 34 := rowSeed_length hrho row col
  rw [keccakAbsorb_21_lt168 0x1f#8 (rowSeed rho row col) (by omega)]
  apply congrArg keccakF1600; apply Array.ext
  · simp [keccakXorRate21_size, preAbsorbState_size]
  · intro idx h1 h2
    have hidx : idx < 25 := by simpa [preAbsorbState_size] using h2
    have hgetR : (preAbsorbState rho row col).getD idx 0#64 = preAbsorbLane rho row col idx := by
      simp [preAbsorbState, Array.getD, hidx]
    rw [array_getElem_eq_getD64 _ idx h1, array_getElem_eq_getD64 _ idx h2, hgetR]
    by_cases hlt21 : idx < 21
    · rw [keccakXorRate21_getD_lt _ _ hlt21]
      have hz0 : keccakZeroState.getD idx 0#64 = 0#64 := by simp [keccakZeroState, Array.getD, hidx]
      rw [hz0, BitVec.zero_xor]
      by_cases hlt4 : idx < 4
      · simp only [preAbsorbLane, hlt4, ↓reduceIte, rhoW, packLane64,
          lastBlock168_getD hrho row col (8 * idx) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 1) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 2) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 3) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 4) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 5) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 6) (by omega),
          lastBlock168_getD hrho row col (8 * idx + 7) (by omega),
          show 8 * idx < 32 by omega, show 8 * idx + 1 < 32 by omega,
          show 8 * idx + 2 < 32 by omega, show 8 * idx + 3 < 32 by omega,
          show 8 * idx + 4 < 32 by omega, show 8 * idx + 5 < 32 by omega,
          show 8 * idx + 6 < 32 by omega, show 8 * idx + 7 < 32 by omega]
      · by_cases heq4 : idx = 4
        · subst heq4
          simp only [preAbsorbLane, show ¬(4 < 4) by omega, ↓reduceIte, packLane64,
            lastBlock168_getD hrho row col 32 (by decide), lastBlock168_getD hrho row col 33 (by decide),
            lastBlock168_getD hrho row col 34 (by decide), lastBlock168_getD hrho row col 35 (by decide),
            lastBlock168_getD hrho row col 36 (by decide), lastBlock168_getD hrho row col 37 (by decide),
            lastBlock168_getD hrho row col 38 (by decide), lastBlock168_getD hrho row col 39 (by decide)]
          simp
        · by_cases heq20 : idx = 20
          · subst heq20
            simp only [preAbsorbLane, show ¬(20 < 4) by omega, show ¬(20 = 4) by omega, ↓reduceIte, packLane64,
              lastBlock168_getD hrho row col 160 (by decide), lastBlock168_getD hrho row col 161 (by decide),
              lastBlock168_getD hrho row col 162 (by decide), lastBlock168_getD hrho row col 163 (by decide),
              lastBlock168_getD hrho row col 164 (by decide), lastBlock168_getD hrho row col 165 (by decide),
              lastBlock168_getD hrho row col 166 (by decide), lastBlock168_getD hrho row col 167 (by decide)]
            simp
          · have hbZero : ∀ k, 40 ≤ k → k < 160 →
                (keccakLastBlock 168 0x1f#8 (rowSeed rho row col)).getD k 0#8 = 0#8 := by
              intro k hklo hkhi; rw [lastBlock168_getD hrho row col k (by omega)]
              simp [show ¬(k < 32) by omega, show k ≠ 32 by omega, show k ≠ 33 by omega,
                show k ≠ 34 by omega, show k ≠ 167 by omega]
            simp only [preAbsorbLane, hlt4, heq4, heq20, ↓reduceIte, packLane64,
              hbZero (8 * idx) (by omega) (by omega), hbZero (8 * idx + 1) (by omega) (by omega),
              hbZero (8 * idx + 2) (by omega) (by omega), hbZero (8 * idx + 3) (by omega) (by omega),
              hbZero (8 * idx + 4) (by omega) (by omega), hbZero (8 * idx + 5) (by omega) (by omega),
              hbZero (8 * idx + 6) (by omega) (by omega), hbZero (8 * idx + 7) (by omega) (by omega)]
            decide
    · rw [keccakXorRate21_getD_ge _ _ (by omega) (by simp [keccakZeroState])]
      simp [preAbsorbLane, show ¬(idx < 4) by omega, show idx ≠ 4 by omega, show idx ≠ 20 by omega,
        keccakZeroState, Array.getD, hidx]

@[expose] def rowPermState (rho : List (BitVec 8)) (row col n : Nat) : KeccakState :=
  keccakPermuteN n (keccakAbsorb 21 0x1f#8 (rowSeed rho row col))

theorem rowPermState_zero {rho : List (BitVec 8)} (hrho : rho.length = 32) (row col : Nat) :
    rowPermState rho row col 0 = keccakF1600 (preAbsorbState rho row col) := by
  simp [rowPermState, keccakPermuteN, keccakAbsorb_rowSeed hrho row col]

theorem rowPermState_succ (rho : List (BitVec 8)) (row col n : Nat) :
    keccakF1600 (rowPermState rho row col n) = rowPermState rho row col (n + 1) :=
  (keccakPermuteN_succ_right n _).symm

theorem shake128BlockAt_rowSeeds_eq (rho : List (BitVec 8)) (row col n : Nat) :
    keccakExtractRate 21 (rowPermState rho row col n) = shake128BlockAt (rowSeeds rho row col) n := rfl

theorem shake128FirstBlocks_rowSeeds_three (rho : List (BitVec 8)) (row col : Nat) :
    keccakExtractRate 21 (rowPermState rho row col 0) ++
        (keccakExtractRate 21 (rowPermState rho row col 1) ++
          keccakExtractRate 21 (rowPermState rho row col 2)) =
      shake128FirstBlocks (rowSeeds rho row col) 3 := by
  rw [← List.append_assoc, shake128BlockAt_rowSeeds_eq, shake128BlockAt_rowSeeds_eq,
      shake128BlockAt_rowSeeds_eq, ← shake128FirstBlocks_three]

/-! ## 2. Multi-Step Symbolic Keccak Program Runner (`runAndCheckKProg`) -/

inductive KProgStep where
  | range (w count : Nat)
  | loop (wHead nBody : Nat) (rCnt : BitVec 5) (slots : List KSlot)
      (expLo expHi : List KExpr) (baseOut : Nat)
  deriving Repr

@[expose] def validSpecVar (initBnd : Nat) (bases : List Nat) (id : Nat) : Bool :=
  Nat.blt id initBnd || bases.any (fun b => Nat.ble b id && Nat.blt id (b + 50))

@[expose] def exprVarsOk (ok : Nat → Bool) : KExpr → Bool
  | .var id => ok id
  | .const64 _ | .spAdd _ | .rcAdd _ | .rcVal _
  | .rcLoopOff | .rcLoopPtr | .rcLoopNext | .rcLoopVal => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprVarsOk ok a && exprVarsOk ok b
  | .bsl x y z | .bitOp x y z | .selHi255 x y z =>
      exprVarsOk ok x && exprVarsOk ok y && exprVarsOk ok z
  | .shl a _ | .ushr a _ | .rotl a _ => exprVarsOk ok a

theorem evalKExpr_congr_ok {ok : Nat → Bool} {env1 env2 : KEnv}
    (hsp : env1.sp = env2.sp) (hrc : env1.rcBase = env2.rcBase) (hrl : env1.rLoop = env2.rLoop)
    (hvars : ∀ id, ok id = true → env1.vars id = env2.vars id) :
    ∀ (e : KExpr), exprVarsOk ok e = true → evalKExpr env1 e = evalKExpr env2 e
  | .var id, h => hvars id h
  | .const64 _, _ => rfl
  | .spAdd _, _ => by simp [evalKExpr, hsp]
  | .rcAdd _, _ => by simp [evalKExpr, hrc]
  | .rcVal _, _ => rfl
  | .rcLoopOff, _ => by simp [evalKExpr, hrl]
  | .rcLoopPtr, _ => by simp [evalKExpr, hrc, hrl]
  | .rcLoopNext, _ => by simp [evalKExpr, hrl]
  | .rcLoopVal, _ => by simp [evalKExpr, hrl]
  | .xor a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .bic a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .and64 a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .or64 a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .add64 a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .insByte0 a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1, evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .bsl x y z, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars x h.1.1,
        evalKExpr_congr_ok hsp hrc hrl hvars y h.1.2, evalKExpr_congr_ok hsp hrc hrl hvars z h.2]
  | .bitOp x y z, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars x h.1.1,
        evalKExpr_congr_ok hsp hrc hrl hvars y h.1.2, evalKExpr_congr_ok hsp hrc hrl hvars z h.2]
  | .selHi255 x y z, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars x h.1.1,
        evalKExpr_congr_ok hsp hrc hrl hvars y h.1.2, evalKExpr_congr_ok hsp hrc hrl hvars z h.2]
  | .shl a _, h => by simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h]
  | .ushr a _, h => by simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h]
  | .rotl a _, h => by simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h]

@[expose] def evalExprList25 (env : KEnv) (es : List KExpr) : KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (es.getD idx.1 (.const64 0#64))

@[expose] def extendLoopVars (env : KEnv) (baseOut : Nat) (sLo sHi : KeccakState) : KEnv :=
  { env with
    vars := fun id =>
      if id < baseOut then env.vars id
      else if id < baseOut + 25 then (keccakF1600 sLo).getD (id - baseOut) 0#64
      else if id < baseOut + 50 then (keccakF1600 sHi).getD (id - (baseOut + 25)) 0#64
      else env.vars id }

@[expose] def specEnvSteps : KEnv → List KProgStep → KEnv
  | env, [] => env
  | env, .range _ _ :: rest => specEnvSteps env rest
  | env, .loop _ _ _ _ expLo expHi baseOut :: rest =>
      specEnvSteps (extendLoopVars env baseOut (evalExprList25 env expLo) (evalExprList25 env expHi)) rest

@[expose] def progBasesAux (acc : List Nat) : List KProgStep → List Nat
  | [] => acc
  | .range _ _ :: rest => progBasesAux acc rest
  | .loop _ _ _ _ _ _ baseOut :: rest => progBasesAux (baseOut :: acc) rest

@[expose] def progBases (steps : List KProgStep) : List Nat :=
  progBasesAux [] steps

@[expose] def checkLoopInputs (cfg : KCfg) (ok : Nat → Bool) (st : KState)
    (slots : List KSlot) (expLo expHi : List KExpr) : Bool :=
  (List.range 25).all fun idx =>
    let p := readSlot cfg st (slots.getD idx (.vreg 0))
    let eLo := expLo.getD idx (.const64 0#64)
    let eHi := expHi.getD idx (.const64 0#64)
    p.1.beq eLo && p.2.beq eHi && exprVarsOk ok eLo && exprVarsOk ok eHi

@[expose] def runKProgSteps (cfg : KCfg) (wLo wHi initBnd : Nat) :
    Nat → List Nat → List KProgStep → KState → Option (Nat × List Nat × KState)
  | wCur, bases, [], st => some (wCur, bases, st)
  | wCur, bases, .range w count :: rest, st =>
      if Nat.beq wCur w && Nat.ble wLo w && Nat.ble (w + count) wHi then
        match runKRange cfg w count st with
        | none => none
        | some st' => runKProgSteps cfg wLo wHi initBnd (w + count) bases rest st'
      else none
  | wCur, bases, .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, st =>
      if Nat.beq wCur wHead && Nat.ble initBnd baseOut &&
         bases.all (fun b => Nat.ble (b + 658) baseOut) &&
         checkLoopInputs cfg (validSpecVar initBnd bases) st slots expLo expHi then
        match stepKLoopSym cfg wHead nBody rCnt slots baseOut st with
        | none => none
        | some st' =>
            runKProgSteps cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      else none

@[expose] def runAndCheckKProg (cfg : KCfg) (wLo wHi wStart wEnd initBnd : Nat)
    (steps : List KProgStep) (st0 : KState)
    (chk : (Nat → Bool) → KState → Bool) : Bool :=
  Nat.ble 183 wLo && Nat.ble wHi 3297 &&
  match runKProgSteps cfg wLo wHi initBnd wStart [] steps st0 with
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

private theorem sepWP_of_runKProgSteps [MlKemPlacement] {b tgt : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {wLo wHi initBnd : Nat}
    (hmin : 183 ≤ wLo) (hmax : wHi ≤ 3297)
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
        SepWP (blkPC05.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) →
      SepWP (blkPC05.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env st F) post oom
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
            exact sepWP_of_runKRange hv hrLoop (by omega) (by omega) hrng hpc0 hrun0 hm0
              (fun sf1 hpc1 hrun1 hm1 =>
                sepWP_of_runKProgSteps hv hmin hmax rest (w + count) wFinal bases finalBases
                  st' stEnd env envSpec sf1 hrun_p hrLoop hsp hrc hrl hvars hm1 hpc1 hrun1 hnext)
      · contradiction
  | .loop wHead nBody rCnt slots expLo expHi baseOut :: rest, wCur, wFinal, bases, finalBases,
      st, stEnd, env, envSpec, s0, hrun_p, hrLoop, hsp, hrc, hrl, hvars, hm0, hpc0, hrun0,
      hnext => by
      simp only [runKProgSteps] at hrun_p
      split at hrun_p
      · rename_i hcond
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
        rcases hcond with ⟨⟨⟨hcur, hinit⟩, hbases⟩, hinp⟩
        subst wCur
        cases hstep : stepKLoopSym cfg wHead nBody rCnt slots baseOut st with
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
      SepWP (blkPC05.rebase b (fun _ => none)) tgt sf (KSpatial cfg envFinal stEnd F) post oom) :
    SepWP (blkPC05.rebase b (fun _ => none)) tgt s0 (KSpatial cfg env0 st0 F) post oom := by
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

/-! ## 3. Checked-State Extractors (`KExpr.beq`) -/

theorem eval_checked_gpr {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (r : BitVec 5) (hr : r.toNat < 31) (eExp : KExpr)
    (heq : (stEnd.gprs.get r.toNat).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    sf.readReg64 (.gpr r) = evalKExpr envSpec eExp := by
  rw [hm.hgprs r hr, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_memA {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (idx : Nat) (eExp : KExpr)
    (heq : (stEnd.memA.get idx).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    (stEnd.memA.map (evalKExpr envFinal)).get idx = evalKExpr envSpec eExp := by
  rw [BTree.get_map, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_memB {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (idx : Nat) (eExp : KExpr)
    (heq : (stEnd.memB.get idx).beq eExp = true) (hok : exprVarsOk ok eExp = true) :
    (stEnd.memB.map (evalKExpr envFinal)).get idx = evalKExpr envSpec eExp := by
  rw [BTree.get_map, KExpr.beq_eq_true heq, heval eExp hok]

theorem eval_checked_slot {cfg : KCfg} {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (sl : KSlot) (hsl : slotValid cfg sl = true) (eLo eHi : KExpr)
    (heqLo : (readSlot cfg stEnd sl).1.beq eLo = true)
    (heqHi : (readSlot cfg stEnd sl).2.beq eHi = true)
    (hokLo : exprVarsOk ok eLo = true) (hokHi : exprVarsOk ok eHi = true) :
    slotHolds cfg sf (stEnd.memA.map (evalKExpr envFinal)) sl
      (evalKExpr envSpec eLo) (evalKExpr envSpec eHi) := by
  have hLo : (readSlot cfg stEnd sl).1 = eLo := KExpr.beq_eq_true heqLo
  have hHi : (readSlot cfg stEnd sl).2 = eHi := KExpr.beq_eq_true heqHi
  cases sl with
  | vreg r =>
      have hr : r < 32 := by simpa [slotValid, Nat.blt_eq] using hsl
      simp only [readSlot] at hLo hHi
      have hto : (BitVec.ofNat 5 r).toNat = r := Nat.mod_eq_of_lt hr
      have hv := hm.hvregs (BitVec.ofNat 5 r)
      rw [hto, hLo, hHi, heval eLo hokLo, heval eHi hokHi] at hv
      exact ⟨hr, hv⟩
  | spillQ off =>
      simp only [slotValid, Bool.and_eq_true, Nat.ble_eq] at hsl
      have h512 : (off - cfg.offA) / 8 + 1 < 512 := by omega
      simp only [readSlot] at hLo hHi
      refine ⟨h512, ?_, ?_⟩
      · rw [BTree.get_map, hLo, heval eLo hokLo]
      · rw [BTree.get_map, hHi, heval eHi hokHi]

theorem eval_checked_pstate {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (eL eR : KExpr)
    (heq : (match stEnd.pstate with
            | some (l, r) => l.beq eL && r.beq eR
            | none => false) = true)
    (hokL : exprVarsOk ok eL = true) (hokR : exprVarsOk ok eR = true) :
    sf.pstate = (AddWithCarry64 (evalKExpr envSpec eL) (~~~(evalKExpr envSpec eR)) true).2 := by
  cases hp : stEnd.pstate with
  | none => simp [hp] at heq
  | some pr =>
      rcases pr with ⟨l, r⟩
      simp only [hp, Bool.and_eq_true] at heq
      have hpst := hm.hpstate l r hp
      rw [KExpr.beq_eq_true heq.1, KExpr.beq_eq_true heq.2, heval eL hokL, heval eR hokR] at hpst
      exact hpst

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
