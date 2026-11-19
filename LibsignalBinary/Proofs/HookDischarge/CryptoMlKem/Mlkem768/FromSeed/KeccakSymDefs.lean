/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `generate_keypair_compressed` (`B05`) — Symbolic 2-Lane NEON Keccak & Slot Engine (`KeccakSymDefs`)

Pure AST, `O(log N)` binary-tree register/stack-word arrays (`BTree`), and configurable symbolic
ARM64 instruction stepper (`stepKInst`, `runKRange`) for `Seg2` (`+0x02dc .. +0x335c`) of
`mlkem768` `generate_keypair_compressed`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (rotl_1_of_add_usra rotl_2 rotl_3 rotl_6 rotl_8 rotl_10 rotl_14 rotl_15 rotl_18
   rotl_20 rotl_21 rotl_25 rotl_27 rotl_28 rotl_36 rotl_39 rotl_41 rotl_43 rotl_44
   rotl_45 rotl_55 rotl_56 rotl_61 rotl_62)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
  (blkLib05 blkPl05 blkPlaceable05 blkPC05 blkTree05 blk05_code_eq blk05_tree_size)

/-! ## 0. Relocation-Free `WordTree` Fetch Helper for `B05` -/

@[expose] def fetchWordTree05 (j : Nat) : Option Instr :=
  match blkTree05.getQuad? j with
  | none => none
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)

theorem fetch_blk05_noReloc [MlKemPlacement] {loOff hiOff : Nat}
    (hrel : blkLib05.text.relocs.all (fun r => decide (r.off < loOff ∨ hiOff ≤ r.off)) = true)
    {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : loOff ≤ 4 * j) (hhi : 4 * j < hiOff) (hbound : 4 * j + 4 ≤ 4 * 7112)
    (hfw : fetchWordTree05 j = some inst) :
    (blkPC05.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hnrel : (blkLib05.text.relocAt? (4 * j)).isNone = true := by
    cases hr : blkLib05.text.relocAt? (4 * j) with
    | none => rfl
    | some r =>
      have hmem := CodeBlock.relocAt?_mem hr
      have hoff := CodeBlock.relocAt?_off hr
      have hall := (List.all_eq_true.mp hrel) r hmem
      simp only [decide_eq_true_eq] at hall
      omega
  have hdec : blkTree05.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree05 at hfw
    cases hq : blkTree05.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl05) (b := b)
    (X := fun _ => none) blk05_code_eq blk05_tree_size blkPlaceable05 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk05_code_eq blk05_tree_size
    (by omega) hbound (by omega) hdec hnrel hnh

/-! ## 1. `O(log N)` Binary-Tree Array (`BTree`) -/

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
      have hk2 : k / 2 < 2 ^ d := by
        rw [Nat.pow_succ] at hk; omega
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
  | 0, .leaf _, k, _, hk, i, hii => by
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
  | bitOp (d a m : KExpr)
  | add64 (a b : KExpr)
  | shl (a : KExpr) (sh : Nat)
  | ushr (a : KExpr) (sh : Nat)
  | rotl (a : KExpr) (k : Nat)
  | insByte0 (d s : KExpr)
  | selHi255 (c t f : KExpr)
  deriving Repr

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
  | .bitOp d a m => ((evalKExpr env a ^^^ evalKExpr env d) &&& evalKExpr env m) ^^^ evalKExpr env d
  | .add64 a b => evalKExpr env a + evalKExpr env b
  | .shl a sh => evalKExpr env a <<< sh
  | .ushr a sh => evalKExpr env a >>> sh
  | .rotl a k => (evalKExpr env a).rotateLeft k
  | .insByte0 d s => (evalKExpr env d &&& 0xffffffffffffff00#64) ||| (evalKExpr env s &&& 0xff#64)
  | .selHi255 c t f => if 255#64 < evalKExpr env c then evalKExpr env t else evalKExpr env f

@[expose] def smartAdd64 (a b : KExpr) : KExpr :=
  match a, b with
  | .const64 x, .const64 y => .const64 (x + y)
  | .spAdd x, .const64 y => .spAdd (x + y)
  | .rcAdd x, .const64 y => .rcAdd (x + y)
  | .rcAdd 0#64, .rcLoopOff => .rcLoopPtr
  | .rcLoopOff, .const64 8#64 => .rcLoopNext
  | _, _ => .add64 a b

theorem eval_smartAdd64 (env : KEnv) (a b : KExpr) :
    evalKExpr env (smartAdd64 a b) = evalKExpr env a + evalKExpr env b := by
  unfold smartAdd64
  split
  · rfl
  · exact (BitVec.add_assoc _ _ _).symm
  · exact (BitVec.add_assoc _ _ _).symm
  · simp [evalKExpr]
  · rfl
  · rfl

@[expose] def usraShift? (immh : BitVec 4) (immb : BitVec 3) : Option Nat :=
  match immh, immb with
  | 8#4, 1#3 => some 63 | 8#4, 2#3 => some 62 | 8#4, 3#3 => some 61 | 8#4, 6#3 => some 58
  | 9#4, 0#3 => some 56 | 9#4, 2#3 => some 54 | 9#4, 6#3 => some 50 | 9#4, 7#3 => some 49
  | 10#4, 2#3 => some 46 | 10#4, 4#3 => some 44 | 10#4, 5#3 => some 43
  | 11#4, 1#3 => some 39 | 11#4, 3#3 => some 37 | 11#4, 4#3 => some 36
  | 12#4, 4#3 => some 28 | 12#4, 7#3 => some 25
  | 13#4, 1#3 => some 23 | 13#4, 3#3 => some 21 | 13#4, 4#3 => some 20 | 13#4, 5#3 => some 19
  | 14#4, 7#3 => some 9 | 15#4, 0#3 => some 8 | 15#4, 5#3 => some 3 | 15#4, 6#3 => some 2
  | _, _ => none

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
  | .bitOp d1 a1 m1, .bitOp d2 a2 m2 => d1.beq d2 && a1.beq a2 && m1.beq m2
  | .add64 a1 b1, .add64 a2 b2 => a1.beq a2 && b1.beq b2
  | .shl a1 s1, .shl a2 s2 => a1.beq a2 && Nat.beq s1 s2
  | .ushr a1 s1, .ushr a2 s2 => a1.beq a2 && Nat.beq s1 s2
  | .rotl a1 k1, .rotl a2 k2 => a1.beq a2 && Nat.beq k1 k2
  | .insByte0 d1 s1, .insByte0 d2 s2 => d1.beq d2 && s1.beq s2
  | .selHi255 c1 t1 f1, .selHi255 c2 t2 f2 => c1.beq c2 && t1.beq t2 && f1.beq f2
  | _, _ => false

theorem KExpr.beq_eq_true {a b : KExpr} (h : a.beq b = true) : a = b := by
  induction a generalizing b with
  | var x => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | exact congrArg KExpr.var (Nat.eq_of_beq_eq_true h)
  | const64 x => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | exact congrArg KExpr.const64 (beq_iff_eq.mp h)
  | spAdd x => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | exact congrArg KExpr.spAdd (beq_iff_eq.mp h)
  | rcAdd x => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | exact congrArg KExpr.rcAdd (beq_iff_eq.mp h)
  | rcVal x => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | exact congrArg KExpr.rcVal (Nat.eq_of_beq_eq_true h)
  | rcLoopOff => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | rfl
  | rcLoopPtr => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | rfl
  | rcLoopNext => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | rfl
  | rcLoopVal => cases b <;> simp only [KExpr.beq] at h <;> first | contradiction | rfl
  | xor a1 b1 iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, ihb h.2]
  | bic a1 b1 iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, ihb h.2]
  | and64 a1 b1 iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, ihb h.2]
  | or64 a1 b1 iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, ihb h.2]
  | bsl m1 a1 b1 ihm iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [ihm h.1.1, iha h.1.2, ihb h.2]
  | bitOp d1 a1 m1 ihd iha ihm =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [ihd h.1.1, iha h.1.2, ihm h.2]
  | add64 a1 b1 iha ihb =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, ihb h.2]
  | shl a1 s1 iha =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, Nat.eq_of_beq_eq_true h.2]
  | ushr a1 s1 iha =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, Nat.eq_of_beq_eq_true h.2]
  | rotl a1 k1 iha =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [iha h.1, Nat.eq_of_beq_eq_true h.2]
  | insByte0 d1 s1 ihd ihs =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [ihd h.1, ihs h.2]
  | selHi255 c1 t1 f1 ihc iht ihf =>
      cases b <;> simp only [KExpr.beq, Bool.and_eq_true] at h <;>
        first | contradiction | rw [ihc h.1.1, iht h.1.2, ihf h.2]

private theorem shl_add_ushr_eq_rotl64 (a : BitVec 64) {sh r : Nat}
    (hsum : sh + r = 64) (hpos : 0 < sh) (hlt : sh < 64) :
    (a <<< sh) + (a >>> r) = a.rotateLeft sh := by
  have hor : (a <<< sh) + (a >>> r) = (a <<< sh) ||| (a >>> r) := by
    apply BitVec.add_eq_or_of_and_eq_zero
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_zero, decide_eq_true hi, Bool.true_and]
    by_cases h : i < sh
    · simp [h]
    · rw [BitVec.getLsbD_of_ge a (r + i) (by omega), Bool.and_false]
  rw [hor]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateLeft, decide_eq_true hi, Bool.true_and, Nat.mod_eq_of_lt hlt]
  by_cases h : i < sh
  · have heq : r + i = 64 - sh + i := by omega
    simp [h, heq]
  · rw [BitVec.getLsbD_of_ge a (r + i) (by omega)]
    simp [h]

@[expose] def smartUsra (d n : KExpr) (r : Nat) : KExpr :=
  match d with
  | .add64 x y =>
      if Nat.beq r 63 && x.beq n && y.beq n then .rotl n 1 else .add64 d (.ushr n r)
  | .shl x sh =>
      if Nat.beq (sh + r) 64 && Nat.blt 0 sh && Nat.blt sh 64 && x.beq n then .rotl n sh
      else .add64 d (.ushr n r)
  | _ => .add64 d (.ushr n r)

theorem eval_smartUsra (env : KEnv) (d n : KExpr) (r : Nat) :
    evalKExpr env (smartUsra d n r) = evalKExpr env d + (evalKExpr env n >>> r) := by
  unfold smartUsra
  cases d with
  | add64 x y =>
      dsimp only
      split
      · next h =>
          simp only [Bool.and_eq_true] at h
          rw [Nat.eq_of_beq_eq_true h.1.1, KExpr.beq_eq_true h.1.2, KExpr.beq_eq_true h.2]
          exact (rotl_1_of_add_usra (evalKExpr env n)).symm
      · rfl
  | shl x sh =>
      dsimp only
      split
      · next h =>
          simp only [Bool.and_eq_true, Nat.blt_eq] at h
          rw [KExpr.beq_eq_true h.2]
          exact (shl_add_ushr_eq_rotl64 (evalKExpr env n)
            (Nat.eq_of_beq_eq_true h.1.1.1) h.1.1.2 h.1.2).symm
      · rfl
  | _ => rfl

/-! ## 3. Symbolic Machine State (`KCfg`, `KState`) & Instruction Stepper (`stepKInst`) -/

structure KCfg where
  offA : Nat
  lenA : Nat
  offB : Nat := 0
  lenB : Nat := 0
  deriving DecidableEq, Repr

structure KState where
  vregs  : BTree (KExpr × KExpr) 5
  gprs   : BTree KExpr 5
  memA   : BTree KExpr 9
  memB   : BTree KExpr 9
  pstate : Option (KExpr × KExpr)
  deriving Repr

inductive KSlot where
  | vreg (r : Nat)
  | spillQ (off : Nat)
  deriving DecidableEq, Repr

@[expose] def resolveByteOff? (st : KState) (addr : AddrMode) : Option Nat :=
  let (base, off64) :=
    match addr with
    | .Offset b off => (some b, off)
    | .UnscaledOffset b off => (some b, off)
    | _ => (none, 0#64)
  match base with
  | some .sp =>
      if Nat.blt off64.toNat 30080 && off64 == BitVec.ofNat 64 off64.toNat then some off64.toNat
      else none
  | some (.gpr r) =>
      if r == 31#5 then none
      else
        match st.gprs.get r.toNat with
        | .spAdd bOff =>
            let tot := bOff + off64
            if Nat.blt tot.toNat 30080 && tot == BitVec.ofNat 64 tot.toNat then some tot.toNat
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
  | .simdThreeSame true true 0x2#2 rm 0x03#5 rn rd =>
      let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
      some { st with vregs := st.vregs.set rd.toNat (.bitOp vd.1 vn.1 vm.1, .bitOp vd.2 vn.2 vm.2) }
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
      match usraShift? immh immb with
      | some r =>
          let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat
          some { st with vregs := st.vregs.set rd.toNat (smartUsra vd.1 vn.1 r, smartUsra vd.2 vn.2 r) }
      | none => none
  | .simdInsDup true false 0x08#5 0x0#4 rn rd =>
      let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.1, vn.1) }
  | .simdInsDup true false 0x18#5 0x0#4 rn rd =>
      let vn := st.vregs.get rn.toNat
      some { st with vregs := st.vregs.set rd.toNat (vn.2, vn.2) }
  | .simdInsDup true false 0x01#5 0x3#4 rn rd =>
      if rn == 31#5 then none
      else
        let vd := st.vregs.get rd.toNat; let gr := st.gprs.get rn.toNat
        some { st with vregs := st.vregs.set rd.toNat (.insByte0 vd.1 gr, vd.2) }
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
      else some { st with pstate := some (st.gprs.get rn.toNat, .const64 (imm12.zeroExtend 64)) }
  | .addSubShift .W64 .SUBS .xzr (.gpr rn) .xzr .LSL 0 =>
      if rn == 31#5 then none
      else some { st with pstate := some (st.gprs.get rn.toNat, .const64 0#64) }
  | .condSelect .W64 .CSEL (.gpr rd) (.gpr rn) (.gpr rm) .HI =>
      if rd == 31#5 || rn == 31#5 || rm == 31#5 then none
      else
        match st.pstate with
        | some (lhs, .const64 255#64) =>
            let v := .selHi255 lhs (st.gprs.get rn.toNat) (st.gprs.get rm.toNat)
            some { st with gprs := st.gprs.set rd.toNat v }
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
      match fetchWordTree05 w with
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
  | m + 1, _, w, st0, _, _, h1, h2 => by
      simp only [runKRange] at h1
      cases hfw : fetchWordTree05 w with
      | none => simp [hfw] at h1
      | some inst =>
          simp only [hfw] at h1
          cases hst : stepKInst cfg inst st0 with
          | none => simp [hst] at h1
          | some stm =>
              simp only [hst] at h1
              have hrec := runKRange_append h1 (by simpa [Nat.add_right_comm, Nat.add_assoc] using h2)
              simpa [Nat.succ_add, runKRange, hfw, hst] using hrec

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
