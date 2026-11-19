/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `encapsulate1_serialized` (`B03`) — Symbolic NEON Keccak, Clamp, & Copy Engine (`Seg2SymDefs`)

Pure `O(log N)` binary-tree register/stack-word arrays (`BTree`), 64-bit symbolic lane AST
(`KExpr`), and instruction stepper (`stepKInst`, `runKRange`) for `Seg2` (`+0x026c .. +0x3280`)
of `mlkem768` `encapsulate1_serialized` (`B03`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (rotl_1_of_add_usra rotl_2 rotl_3 rotl_6 rotl_8 rotl_10 rotl_14 rotl_15 rotl_18
   rotl_20 rotl_21 rotl_25 rotl_27 rotl_28 rotl_36 rotl_39 rotl_41 rotl_43 rotl_44
   rotl_45 rotl_55 rotl_56 rotl_61 rotl_62)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkTree03)

/-! ## 1. `WordTree` Instruction Decode Lookup (`fetchWordTree03`) & `BTree` -/

@[expose] def fetchWordTree03 (j : Nat) : Option Instr :=
  match blkTree03.getQuad? j with
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)
  | none => none

inductive BTree (α : Type) : Nat → Type where
  | leaf (val : α) : BTree α 0
  | node {d : Nat} (lo hi : BTree α d) : BTree α (d + 1)
  deriving DecidableEq, Repr

@[expose] def BTree.ofFn {α : Type} : (d : Nat) → (Nat → α) → BTree α d
  | 0, f => .leaf (f 0)
  | d + 1, f =>
      .node (BTree.ofFn d (fun k => f (2 * k))) (BTree.ofFn d (fun k => f (2 * k + 1)))

@[expose] def BTree.get {α : Type} : {d : Nat} → BTree α d → Nat → α
  | 0, .leaf v, _ => v
  | _ + 1, .node lo hi, k =>
      if k % 2 == 0 then lo.get (k / 2) else hi.get (k / 2)

@[expose] def BTree.set {α : Type} : {d : Nat} → BTree α d → Nat → α → BTree α d
  | 0, .leaf _, _, x => .leaf x
  | _ + 1, .node lo hi, k, x =>
      if k % 2 == 0 then .node (lo.set (k / 2) x) hi
      else .node lo (hi.set (k / 2) x)

@[expose] def BTree.map {α β : Type} (f : α → β) : {d : Nat} → BTree α d → BTree β d
  | 0, .leaf v => .leaf (f v)
  | _ + 1, .node lo hi => .node (lo.map f) (hi.map f)

theorem BTree.get_ofFn {α : Type} :
    ∀ (d : Nat) (f : Nat → α) (k : Nat), k < 2 ^ d → (BTree.ofFn d f).get k = f k
  | 0, f, k, hk => by
      have hk0 : k = 0 := by omega
      subst hk0; rfl
  | d + 1, f, k, hk => by
      have hk2 : k / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega
      simp only [BTree.ofFn, BTree.get]
      by_cases hpar : (k % 2 == 0) = true
      · simp only [hpar, ↓reduceIte, BTree.get_ofFn d _ (k / 2) hk2]
        have hm : k % 2 = 0 := beq_iff_eq.mp hpar
        exact congrArg f (by omega)
      · have hparF : (k % 2 == 0) = false := Bool.eq_false_iff.mpr hpar
        simp only [hparF, Bool.false_eq_true, ↓reduceIte, BTree.get_ofFn d _ (k / 2) hk2]
        have hm : k % 2 ≠ 0 := fun h => hpar (beq_iff_eq.mpr h)
        exact congrArg f (by omega)

theorem BTree.get_set {α : Type} :
    ∀ {d : Nat} (t : BTree α d) (k : Nat) (x : α), k < 2 ^ d →
      ∀ (i : Nat), i < 2 ^ d → (t.set k x).get i = if i = k then x else t.get i
  | 0, .leaf v, k, x, hk, i, hii => by
      have hk0 : k = 0 := by omega
      have hi0 : i = 0 := by omega
      subst hk0; subst hi0; simp [BTree.set, BTree.get]
  | d + 1, .node lo hi, k, x, hk, i, hii => by
      have hk2 : k / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega
      have hi2 : i / 2 < 2 ^ d := by rw [Nat.pow_succ] at hii; omega
      simp only [BTree.set, BTree.get]
      by_cases hkp : (k % 2 == 0) = true <;> by_cases hip : (i % 2 == 0) = true
      · simp only [hkp, hip, ↓reduceIte, BTree.get, BTree.get_set lo (k / 2) x hk2 (i / 2) hi2]
        have hkm : k % 2 = 0 := beq_iff_eq.mp hkp
        have him : i % 2 = 0 := beq_iff_eq.mp hip
        by_cases h : i = k
        · subst h; simp
        · have h2 : i / 2 ≠ k / 2 := by omega
          simp [h, h2]
      · have hipF : (i % 2 == 0) = false := Bool.eq_false_iff.mpr hip
        simp only [hkp, ↓reduceIte, BTree.get, hipF, Bool.false_eq_true]
        have hkm : k % 2 = 0 := beq_iff_eq.mp hkp
        have him : i % 2 ≠ 0 := fun hc => hip (beq_iff_eq.mpr hc)
        have hne : i ≠ k := by omega
        simp [hne]
      · have hkpF : (k % 2 == 0) = false := Bool.eq_false_iff.mpr hkp
        simp only [hkpF, Bool.false_eq_true, ↓reduceIte, BTree.get, hip]
        have hkm : k % 2 ≠ 0 := fun hc => hkp (beq_iff_eq.mpr hc)
        have him : i % 2 = 0 := beq_iff_eq.mp hip
        have hne : i ≠ k := by omega
        simp [hne]
      · have hkpF : (k % 2 == 0) = false := Bool.eq_false_iff.mpr hkp
        have hipF : (i % 2 == 0) = false := Bool.eq_false_iff.mpr hip
        simp only [hkpF, Bool.false_eq_true, ↓reduceIte, BTree.get, hipF,
          BTree.get_set hi (k / 2) x hk2 (i / 2) hi2]
        have hkm : k % 2 ≠ 0 := fun hc => hkp (beq_iff_eq.mpr hc)
        have him : i % 2 ≠ 0 := fun hc => hip (beq_iff_eq.mpr hc)
        by_cases h : i = k
        · subst h; simp
        · have h2 : i / 2 ≠ k / 2 := by omega
          simp [h, h2]

theorem BTree.get_map {α β : Type} (f : α → β) :
    ∀ {d : Nat} (t : BTree α d) (k : Nat), (t.map f).get k = f (t.get k)
  | 0, .leaf _, _ => rfl
  | _ + 1, .node lo hi, k => by
      simp only [BTree.map, BTree.get]
      split <;> [exact BTree.get_map f lo (k / 2); exact BTree.get_map f hi (k / 2)]

theorem BTree.map_set {α β : Type} (f : α → β) :
    ∀ {d : Nat} (t : BTree α d) (k : Nat) (x : α),
      (t.set k x).map f = (t.map f).set k (f x)
  | 0, .leaf _, _, _ => rfl
  | _ + 1, .node lo hi, k, x => by
      by_cases h : (k % 2 == 0) = true
      · simp [BTree.set, BTree.map, h, BTree.map_set f lo]
      · have hf : (k % 2 == 0) = false := Bool.eq_false_iff.mpr h
        simp [BTree.set, BTree.map, hf, BTree.map_set f hi]

theorem BTree.map_ofFn {α β : Type} (g : α → β) :
    ∀ (d : Nat) (f : Nat → α), (BTree.ofFn d f).map g = BTree.ofFn d (fun k => g (f k))
  | 0, _ => rfl
  | d + 1, f => by simp [BTree.ofFn, BTree.map, BTree.map_ofFn g d]

/-! ## 2. `KExpr` 64-Bit Lane / GPR / Stack-Word AST & Smart Constructors -/

@[expose] def clampWord64 (v : BitVec 64) : BitVec 64 :=
  if ConditionHolds .HI (subsPState64 v 255#64) then 256#64 else v

inductive KExpr where
  | var (id : Nat)
  | const64 (v : BitVec 64)
  | spAdd (off : BitVec 64)
  | rcAdd (off : BitVec 64)
  | rcVal (idx : Nat)
  | rcLoopOff
  | rcLoopPtr
  | rcLoopNext
  | rcLoopVal
  | xor (a b : KExpr)
  | bic (a b : KExpr)
  | and64 (a b : KExpr)
  | or64 (a b : KExpr)
  | bsl (m a b : KExpr)
  | add64 (a b : KExpr)
  | shl (a : KExpr) (sh : Nat)
  | ushr (a : KExpr) (sh : Nat)
  | rotl (a : KExpr) (k : Nat)
  | insByte0 (d s : KExpr)
  | clamp64 (a : KExpr)
  deriving DecidableEq, Repr

structure KEnv where
  sp     : BitVec 64
  rcBase : BitVec 64
  rLoop  : Nat
  vars   : Nat → BitVec 64

@[expose] def evalKExpr (env : KEnv) : KExpr → BitVec 64
  | .var id => env.vars id
  | .const64 v => v
  | .spAdd off => env.sp + off
  | .rcAdd off => env.rcBase + off
  | .rcVal idx => keccakRcAt idx
  | .rcLoopOff => BitVec.ofNat 64 (8 * env.rLoop)
  | .rcLoopPtr => env.rcBase + BitVec.ofNat 64 (8 * env.rLoop)
  | .rcLoopNext => BitVec.ofNat 64 (8 * env.rLoop) + 8#64
  | .rcLoopVal => keccakRcAt env.rLoop
  | .xor a b => evalKExpr env a ^^^ evalKExpr env b
  | .bic a b => ~~~(evalKExpr env b) &&& evalKExpr env a
  | .and64 a b => evalKExpr env a &&& evalKExpr env b
  | .or64 a b => evalKExpr env a ||| evalKExpr env b
  | .bsl m a b => ((evalKExpr env a ^^^ evalKExpr env b) &&& evalKExpr env m) ^^^ evalKExpr env b
  | .add64 a b => evalKExpr env a + evalKExpr env b
  | .shl a sh => evalKExpr env a <<< sh
  | .ushr a sh => evalKExpr env a >>> sh
  | .rotl a k => (evalKExpr env a).rotateLeft k
  | .insByte0 d s => (evalKExpr env d &&& 0xffffffffffffff00#64) ||| (evalKExpr env s &&& 0xff#64)
  | .clamp64 a => clampWord64 (evalKExpr env a)

@[expose] def smartAdd64 (a b : KExpr) : KExpr :=
  match a, b with
  | .const64 x, .const64 y => .const64 (x + y)
  | .spAdd x, .const64 y => .spAdd (x + y)
  | .rcAdd x, .const64 y => .rcAdd (x + y)
  | .rcAdd x, .rcLoopOff => if x == 0#64 then .rcLoopPtr else .add64 a b
  | .rcLoopOff, .const64 y => if y == 8#64 then .rcLoopNext else .add64 a b
  | _, _ => .add64 a b

theorem eval_smartAdd64 (env : KEnv) (a b : KExpr) :
    evalKExpr env (smartAdd64 a b) = evalKExpr env a + evalKExpr env b := by
  cases a <;> cases b <;> try rfl
  · exact (BitVec.add_assoc _ _ _).symm
  · exact (BitVec.add_assoc _ _ _).symm
  · next x =>
      dsimp only [smartAdd64]
      by_cases hx : (x == 0#64) = true
      · simp only [hx, ↓reduceIte]
        rw [beq_iff_eq.mp hx]
        simp [evalKExpr]
      · simp [Bool.eq_false_iff.mpr hx, evalKExpr]
  · next y =>
      dsimp only [smartAdd64]
      by_cases hy : (y == 8#64) = true
      · simp only [hy, ↓reduceIte]
        rw [beq_iff_eq.mp hy]
        rfl
      · simp [Bool.eq_false_iff.mpr hy, evalKExpr]

inductive UsraRot where
  | r1 | r2 | r3 | r6 | r8 | r10 | r14 | r15 | r18 | r20 | r21 | r25
  | r27 | r28 | r36 | r39 | r41 | r43 | r44 | r45 | r55 | r56 | r61 | r62
  deriving DecidableEq, Repr

@[expose] def UsraRot.shlAmt : UsraRot → Nat
  | .r1 => 1 | .r2 => 2 | .r3 => 3 | .r6 => 6 | .r8 => 8 | .r10 => 10
  | .r14 => 14 | .r15 => 15 | .r18 => 18 | .r20 => 20 | .r21 => 21 | .r25 => 25
  | .r27 => 27 | .r28 => 28 | .r36 => 36 | .r39 => 39 | .r41 => 41 | .r43 => 43
  | .r44 => 44 | .r45 => 45 | .r55 => 55 | .r56 => 56 | .r61 => 61 | .r62 => 62

@[expose] def UsraRot.ushrAmt (rot : UsraRot) : Nat := 64 - rot.shlAmt

@[expose] def usraRot? (immh : BitVec 4) (immb : BitVec 3) : Option UsraRot :=
  let k : BitVec 7 := immh ++ immb
  if k == 65#7 then some .r1 else if k == 66#7 then some .r2
  else if k == 67#7 then some .r3 else if k == 70#7 then some .r6
  else if k == 72#7 then some .r8 else if k == 74#7 then some .r10
  else if k == 78#7 then some .r14 else if k == 79#7 then some .r15
  else if k == 82#7 then some .r18 else if k == 84#7 then some .r20
  else if k == 85#7 then some .r21 else if k == 89#7 then some .r25
  else if k == 91#7 then some .r27 else if k == 92#7 then some .r28
  else if k == 100#7 then some .r36 else if k == 103#7 then some .r39
  else if k == 105#7 then some .r41 else if k == 107#7 then some .r43
  else if k == 108#7 then some .r44 else if k == 109#7 then some .r45
  else if k == 119#7 then some .r55 else if k == 120#7 then some .r56
  else if k == 125#7 then some .r61 else if k == 126#7 then some .r62
  else none

@[expose] def KExpr.beq : KExpr → KExpr → Bool
  | .var a, .var b => Nat.beq a b
  | .const64 a, .const64 b => a == b
  | .spAdd a, .spAdd b => a == b
  | .rcAdd a, .rcAdd b => a == b
  | .rcVal a, .rcVal b => Nat.beq a b
  | .rcLoopOff, .rcLoopOff => true
  | .rcLoopPtr, .rcLoopPtr => true
  | .rcLoopNext, .rcLoopNext => true
  | .rcLoopVal, .rcLoopVal => true
  | .xor a1 b1, .xor a2 b2 => a1.beq a2 && b1.beq b2
  | .bic a1 b1, .bic a2 b2 => a1.beq a2 && b1.beq b2
  | .and64 a1 b1, .and64 a2 b2 => a1.beq a2 && b1.beq b2
  | .or64 a1 b1, .or64 a2 b2 => a1.beq a2 && b1.beq b2
  | .bsl m1 a1 b1, .bsl m2 a2 b2 => m1.beq m2 && a1.beq a2 && b1.beq b2
  | .add64 a1 b1, .add64 a2 b2 => a1.beq a2 && b1.beq b2
  | .shl a1 s1, .shl a2 s2 => a1.beq a2 && Nat.beq s1 s2
  | .ushr a1 s1, .ushr a2 s2 => a1.beq a2 && Nat.beq s1 s2
  | .rotl a1 k1, .rotl a2 k2 => a1.beq a2 && Nat.beq k1 k2
  | .insByte0 d1 s1, .insByte0 d2 s2 => d1.beq d2 && s1.beq s2
  | .clamp64 a1, .clamp64 a2 => a1.beq a2
  | _, _ => false

theorem KExpr.beq_eq_true : ∀ {a b : KExpr}, a.beq b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> try cases h
  · exact congrArg KExpr.var (Nat.eq_of_beq_eq_true h)
  · exact congrArg KExpr.const64 (beq_iff_eq.mp h)
  · exact congrArg KExpr.spAdd (beq_iff_eq.mp h)
  · exact congrArg KExpr.rcAdd (beq_iff_eq.mp h)
  · exact congrArg KExpr.rcVal (Nat.eq_of_beq_eq_true h)
  · rfl
  · rfl
  · rfl
  · rfl
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · obtain ⟨h12, h3⟩ := Bool.and_eq_true _ _ |>.mp h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h12
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2, KExpr.beq_eq_true h3]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
    rw [KExpr.beq_eq_true h1, KExpr.beq_eq_true h2]
  · exact congrArg KExpr.clamp64 (KExpr.beq_eq_true h)

@[expose] def smartUsra (d n : KExpr) (rot : UsraRot) : KExpr :=
  match rot with
  | .r1 =>
      match d with
      | .add64 x y => if x.beq n && y.beq n then .rotl n 1 else .add64 d (.ushr n 63)
      | _ => .add64 d (.ushr n 63)
  | rot =>
      let sh := rot.shlAmt
      let r := rot.ushrAmt
      match d with
      | .shl x s => if Nat.beq s sh && x.beq n then .rotl n sh else .add64 d (.ushr n r)
      | _ => .add64 d (.ushr n r)

private theorem eval_smartUsra_shl (env : KEnv) (d n : KExpr) (sh r : Nat)
    (hrot : ∀ a : BitVec 64, (a <<< sh) + (a >>> r) = a.rotateLeft sh) :
    evalKExpr env
      (match d with
       | .shl x s => if Nat.beq s sh && x.beq n then .rotl n sh else .add64 d (.ushr n r)
       | _ => .add64 d (.ushr n r)) =
    evalKExpr env d + (evalKExpr env n >>> r) := by
  cases d <;> try rfl
  next x s =>
    dsimp only
    by_cases hc : (Nat.beq s sh && x.beq n) = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨hs, hx⟩ := Bool.and_eq_true _ _ |>.mp hc
      rw [Nat.eq_of_beq_eq_true hs, KExpr.beq_eq_true hx]
      exact (hrot (evalKExpr env n)).symm
    · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]; rfl

theorem eval_smartUsra (env : KEnv) (d n : KExpr) (rot : UsraRot) :
    evalKExpr env (smartUsra d n rot) = evalKExpr env d + (evalKExpr env n >>> rot.ushrAmt) := by
  cases rot
  · cases d <;> try rfl
    next x y =>
      dsimp only [smartUsra, UsraRot.ushrAmt, UsraRot.shlAmt]
      by_cases hc : (x.beq n && y.beq n) = true
      · simp only [hc, ↓reduceIte]
        obtain ⟨hx, hy⟩ := Bool.and_eq_true _ _ |>.mp hc
        rw [KExpr.beq_eq_true hx, KExpr.beq_eq_true hy]
        exact (rotl_1_of_add_usra (evalKExpr env n)).symm
      · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]; rfl
  · exact eval_smartUsra_shl env d n 2 62 rotl_2
  · exact eval_smartUsra_shl env d n 3 61 rotl_3
  · exact eval_smartUsra_shl env d n 6 58 rotl_6
  · exact eval_smartUsra_shl env d n 8 56 rotl_8
  · exact eval_smartUsra_shl env d n 10 54 rotl_10
  · exact eval_smartUsra_shl env d n 14 50 rotl_14
  · exact eval_smartUsra_shl env d n 15 49 rotl_15
  · exact eval_smartUsra_shl env d n 18 46 rotl_18
  · exact eval_smartUsra_shl env d n 20 44 rotl_20
  · exact eval_smartUsra_shl env d n 21 43 rotl_21
  · exact eval_smartUsra_shl env d n 25 39 rotl_25
  · exact eval_smartUsra_shl env d n 27 37 rotl_27
  · exact eval_smartUsra_shl env d n 28 36 rotl_28
  · exact eval_smartUsra_shl env d n 36 28 rotl_36
  · exact eval_smartUsra_shl env d n 39 25 rotl_39
  · exact eval_smartUsra_shl env d n 41 23 rotl_41
  · exact eval_smartUsra_shl env d n 43 21 rotl_43
  · exact eval_smartUsra_shl env d n 44 20 rotl_44
  · exact eval_smartUsra_shl env d n 45 19 rotl_45
  · exact eval_smartUsra_shl env d n 55 9 rotl_55
  · exact eval_smartUsra_shl env d n 56 8 rotl_56
  · exact eval_smartUsra_shl env d n 61 3 rotl_61
  · exact eval_smartUsra_shl env d n 62 2 rotl_62

/-! ## 3. Symbolic Machine State (`KCfg`, `KState`) & Instruction Stepper (`stepKInst`) -/

inductive KPFlag where
  | subs64 (lhs : KExpr) (rhs : BitVec 64)
  | loopDone
  deriving DecidableEq, Repr

structure KCfg where
  offA        : Nat
  lenA        : Nat
  offB        : Nat := 0
  lenB        : Nat := 0
  hasConstsLo : Bool := false
  deriving DecidableEq, Repr

structure KState where
  vregs      : BTree (KExpr × KExpr) 5
  gprs       : BTree KExpr 5
  memA       : BTree KExpr 9
  memB       : BTree KExpr 9
  pstateFlag : Option KPFlag
  deriving DecidableEq, Repr

inductive KSlot where
  | vreg (r : Nat)
  | spillQ (off : Nat)
  | vregLo (r : Nat)
  | spillD (off : Nat)
  deriving DecidableEq, Repr

@[expose] def resolveByteOff? (st : KState) (addr : AddrMode) : Option Nat :=
  let (base, off64) :=
    match addr with
    | .Offset b off => (some b, off)
    | .UnscaledOffset b off => (some b, off)
    | _ => (none, 0#64)
  match base with
  | some .sp =>
      if Nat.blt off64.toNat 17024 && off64 == BitVec.ofNat 64 off64.toNat then some off64.toNat
      else none
  | some (.gpr r) =>
      if r == 31#5 then none
      else
        match st.gprs.get r.toNat with
        | .spAdd bOff =>
            let tot := bOff + off64
            if Nat.blt tot.toNat 17024 && tot == BitVec.ofNat 64 tot.toNat then some tot.toNat
            else none
        | _ => none
  | _ => none

@[expose] def resolveMemIdx? (cfg : KCfg) (st : KState) (addr : AddrMode) (words : Nat) :
    Option (Bool × Nat) :=
  match resolveByteOff? st addr with
  | none => none
  | some byteOff =>
      if !(Nat.beq (byteOff % 8) 0) then none
      else if Nat.ble cfg.offA byteOff && Nat.ble (byteOff + 8 * words) (cfg.offA + 8 * cfg.lenA) &&
          Nat.ble ((byteOff - cfg.offA) / 8 + words) 512 then
        some (false, (byteOff - cfg.offA) / 8)
      else if Nat.ble cfg.offB byteOff && Nat.ble (byteOff + 8 * words) (cfg.offB + 8 * cfg.lenB) &&
          Nat.ble ((byteOff - cfg.offB) / 8 + words) 512 then
        some (true, (byteOff - cfg.offB) / 8)
      else none

@[expose] def readMemWord (st : KState) (inB : Bool) (idx : Nat) : KExpr :=
  if inB then st.memB.get idx else st.memA.get idx

@[expose] def writeMemWord (st : KState) (inB : Bool) (idx : Nat) (val : KExpr) : KState :=
  if inB then { st with memB := st.memB.set idx val }
  else { st with memA := st.memA.set idx val }

@[expose] def stepKInst (cfg : KCfg) (inst : Instr) (st : KState) : Option KState :=
  match inst with
  | .simdThreeSame true false 0x3#2 rm 0x10#5 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (.add64 vn.1 vm.1, .add64 vn.2 vm.2) }
  | .simdThreeSame true true 0x0#2 rm 0x03#5 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (.xor vn.1 vm.1, .xor vn.2 vm.2) }
  | .simdThreeSame true false 0x1#2 rm 0x03#5 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (.bic vn.1 vm.1, .bic vn.2 vm.2) }
  | .simdThreeSame true false 0x2#2 rm 0x03#5 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      let p := if rm == rn then vn else (.or64 vn.1 vm.1, .or64 vn.2 vm.2)
      some { st with vregs := st.vregs.set rd.toNat p }
  | .simdThreeSame true true 0x1#2 rm 0x03#5 rn rd =>
      let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (.bsl vd.1 vn.1 vm.1, .bsl vd.2 vn.2 vm.2) }
  | .simdPermute true 0x3#2 rm 0x3#3 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.1, vm.1) }
  | .simdPermute true 0x3#2 rm 0x7#3 rn rd =>
      let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.2, vm.2) }
  | .simdTwoRegMisc true true 0x3#2 0x0f#5 rn rd =>
      let vn := st.vregs.get rn.toNat
      let p := (.xor vn.1 (.const64 0x8000000000000000#64), .xor vn.2 (.const64 0x8000000000000000#64))
      some { st with vregs := st.vregs.set rd.toNat p }
  | .simdImmShift true true 0x0#4 0x0#3 0x1c#5 0x00#5 rd =>
      some { st with vregs := st.vregs.set rd.toNat (.const64 0#64, .const64 0#64) }
  | .simdImmShift true false 0x0#4 0x0#3 0x10#5 0x1f#5 rd =>
      let p := (.const64 0x001f001f001f001f#64, .const64 0x001f001f001f001f#64)
      some { st with vregs := st.vregs.set rd.toNat p }
  | .simdImmShift true false immh immb 0x0a#5 rn rd =>
      if Nat.blt immh.toNat 8 then none
      else
        let sh := immh.toNat * 8 + immb.toNat - 64
        let vn := st.vregs.get rn.toNat
        some { st with vregs := st.vregs.set rd.toNat (.shl vn.1 sh, .shl vn.2 sh) }
  | .simdImmShift true true immh immb 0x02#5 rn rd =>
      match usraRot? immh immb with
      | some r =>
          let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat
          some { st with vregs := st.vregs.set rd.toNat (smartUsra vd.1 vn.1 r, smartUsra vd.2 vn.2 r) }
      | none => none
  | .simdInsDup true false 0x01#5 0x3#4 rn rd =>
      if rn == 31#5 then none
      else
        let vd := st.vregs.get rd.toNat; let gr := st.gprs.get rn.toNat
        some { st with vregs := st.vregs.set rd.toNat (.insByte0 vd.1 gr, vd.2) }
  | .simdInsDup true false 0x08#5 0x0#4 rn rd =>
      let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.1, vn.1) }
  | .simdInsDup true false 0x18#5 0x0#4 rn rd =>
      let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.2, vn.2) }
  | .simdInsDup true true 0x18#5 0x0#4 rn rd =>
      let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vd.1, vn.1) }
  | .simdDupScalar 0x18#5 rn rd =>
      let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.2, .const64 0#64) }
  | .simdInsDup true false 0x18#5 0x7#4 rn rd =>
      if rd == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (st.vregs.get rn.toNat).2 }
  | .fmovGprVec true 0x1#2 0x0#2 0x6#3 rn rd =>
      if rd == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (st.vregs.get rn.toNat).1 }
  | .simdLd1r true 0x3#2 (.gpr rn) false 0x00#5 vt =>
      if rn == 31#5 then none
      else
        match st.gprs.get rn.toNat with
        | .rcLoopPtr => some { st with vregs := st.vregs.set vt.toNat (.rcLoopVal, .rcLoopVal) }
        | .rcAdd off =>
            if Nat.beq (off.toNat % 8) 0 && Nat.blt (off.toNat / 8) 24 && off == BitVec.ofNat 64 off.toNat then
              let v := KExpr.rcVal (off.toNat / 8)
              some { st with vregs := st.vregs.set vt.toNat (v, v) }
            else none
        | _ => none
  | .addSubImm .W64 .ADD (.gpr rd) .sp imm12 shift12 =>
      if rd == 31#5 then none
      else
        let delta := if shift12 then imm12.toNat <<< 12 else imm12.toNat
        some { st with gprs := st.gprs.set rd.toNat (.spAdd (BitVec.ofNat 64 delta)) }
  | .addSubImm .W64 .ADD (.gpr rd) (.gpr rn) imm12 shift12 =>
      if rd == 31#5 || rn == 31#5 then none
      else
        let delta := if shift12 then imm12.toNat <<< 12 else imm12.toNat
        let v := smartAdd64 (st.gprs.get rn.toNat) (.const64 (BitVec.ofNat 64 delta))
        some { st with gprs := st.gprs.set rd.toNat v }
  | .addSubShift .W64 .ADD (.gpr rd) (.gpr rn) (.gpr rm) .LSL 0 =>
      if rd == 31#5 || rn == 31#5 || rm == 31#5 then none
      else
        let v := smartAdd64 (st.gprs.get rn.toNat) (st.gprs.get rm.toNat)
        some { st with gprs := st.gprs.set rd.toNat v }
  | .addSubImm .W64 .SUBS .xzr (.gpr rn) imm12 false =>
      if rn == 31#5 then none
      else
        match st.gprs.get rn.toNat with
        | .rcLoopNext => if imm12 == 192#12 then some { st with pstateFlag := some .loopDone } else none
        | lhs => some { st with pstateFlag := some (.subs64 lhs (imm12.zeroExtend 64)) }
  | .condSelect .W64 .CSEL (.gpr rd) (.gpr rn) (.gpr rm) .HI =>
      if rd == 31#5 || rn == 31#5 || rm == 31#5 then none
      else
        match st.pstateFlag with
        | some (.subs64 lhs 255#64) =>
            if st.gprs.get rn.toNat == .const64 256#64 && (st.gprs.get rm.toNat).beq lhs then
              some { st with gprs := st.gprs.set rd.toNat (.clamp64 lhs) }
            else none
        | _ => none
  | .moveWide .W32 .MOVZ (.gpr rd) imm16 0 =>
      if rd == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (.const64 (imm16.zeroExtend 64)) }
  | .logicalShift .W32 .ORR (.gpr rd) .xzr .xzr .LSL 0 =>
      if rd == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (.const64 0#64) }
  | .logicalShift .W64 .ORR (.gpr rd) .xzr .xzr .LSL 0 =>
      if rd == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (.const64 0#64) }
  | .logicalShift .W64 .ORR (.gpr rd) .xzr (.gpr rm) .LSL 0 =>
      if rd == 31#5 || rm == 31#5 then none
      else some { st with gprs := st.gprs.set rd.toNat (st.gprs.get rm.toNat) }
  | .ldrSimd .Q128 vt addr =>
      if cfg.hasConstsLo && addr == .Offset .sp 48#64 then
        some { st with vregs := st.vregs.set vt.toNat (.const64 0x00000000001f0200#64, .const64 0#64) }
      else if cfg.hasConstsLo && addr == .Offset .sp 64#64 then
        some { st with vregs := st.vregs.set vt.toNat (.const64 0x00000000001f0100#64, .const64 0#64) }
      else
        match resolveMemIdx? cfg st addr 2 with
        | some (inB, idx) =>
            some { st with vregs := st.vregs.set vt.toNat (readMemWord st inB idx, readMemWord st inB (idx + 1)) }
        | none => none
  | .ldpSimd .Q128 vt1 vt2 addr =>
      if vt1 == vt2 then none
      else
        match resolveMemIdx? cfg st addr 4 with
        | some (inB, idx) =>
            let v1 := (readMemWord st inB idx, readMemWord st inB (idx + 1))
            let v2 := (readMemWord st inB (idx + 2), readMemWord st inB (idx + 3))
            some { st with vregs := (st.vregs.set vt1.toNat v1).set vt2.toNat v2 }
        | none => none
  | .strSimd .Q128 vt addr =>
      match resolveMemIdx? cfg st addr 2 with
      | some (inB, idx) =>
          let vp := st.vregs.get vt.toNat
          some (writeMemWord (writeMemWord st inB idx vp.1) inB (idx + 1) vp.2)
      | none => none
  | .stpSimd .Q128 vt1 vt2 addr =>
      match resolveMemIdx? cfg st addr 4 with
      | some (inB, idx) =>
          let v1 := st.vregs.get vt1.toNat; let v2 := st.vregs.get vt2.toNat
          let s1 := writeMemWord (writeMemWord st inB idx v1.1) inB (idx + 1) v1.2
          some (writeMemWord (writeMemWord s1 inB (idx + 2) v2.1) inB (idx + 3) v2.2)
      | none => none
  | .strSimd .D64 vt addr =>
      match resolveMemIdx? cfg st addr 1 with
      | some (inB, idx) => some (writeMemWord st inB idx (st.vregs.get vt.toNat).1)
      | none => none
  | .ldr .W64 .X64 false (.gpr rt) addr =>
      if rt == 31#5 then none
      else if cfg.hasConstsLo && addr == .Offset .sp 40#64 then
        some { st with gprs := st.gprs.set rt.toNat (.spAdd 3496#64) }
      else if cfg.hasConstsLo && addr == .Offset .sp 88#64 then
        some { st with gprs := st.gprs.set rt.toNat (.spAdd 2203#64) }
      else
        match resolveMemIdx? cfg st addr 1 with
        | some (inB, idx) => some { st with gprs := st.gprs.set rt.toNat (readMemWord st inB idx) }
        | none => none
  | .str .X64 .xzr addr =>
      match resolveMemIdx? cfg st addr 1 with
      | some (inB, idx) => some (writeMemWord st inB idx (.const64 0#64))
      | none => none
  | .str .X64 (.gpr rt) addr =>
      if rt == 31#5 then none
      else
        match resolveMemIdx? cfg st addr 1 with
        | some (inB, idx) => some (writeMemWord st inB idx (st.gprs.get rt.toNat))
        | none => none
  | _ => none

@[expose] def runKRange (cfg : KCfg) : Nat → Nat → KState → Option KState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree03 w with
      | some inst =>
          match stepKInst cfg inst st with
          | some st' => runKRange cfg (w + 1) n st'
          | none => none
      | none => none

theorem runKRange_append {cfg : KCfg} :
    ∀ {m n w : Nat} {st0 st1 st2 : KState},
      runKRange cfg w m st0 = some st1 →
      runKRange cfg (w + m) n st1 = some st2 →
      runKRange cfg w (m + n) st0 = some st2
  | 0, _, _, _, _, _, h1, h2 => by
      simp only [runKRange, Option.some.injEq] at h1
      subst h1; simpa [Nat.add_zero] using h2
  | m + 1, n, w, st0, st1, st2, h1, h2 => by
      simp only [runKRange] at h1
      cases hfw : fetchWordTree03 w with
      | none => simp [hfw] at h1
      | some inst =>
          simp only [hfw] at h1
          cases hst : stepKInst cfg inst st0 with
          | none => simp [hst] at h1
          | some stm =>
              simp only [hst] at h1
              have hrec := runKRange_append h1 (by simpa [Nat.add_right_comm, Nat.add_assoc] using h2)
              simpa [Nat.succ_add, runKRange, hfw, hst] using hrec

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
