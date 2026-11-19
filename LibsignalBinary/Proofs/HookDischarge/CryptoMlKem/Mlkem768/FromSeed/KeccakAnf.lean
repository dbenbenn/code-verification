/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs

/-!
# `generate_keypair_compressed` (`B05`) — Canonical $\mathbb{F}_2$ ANF Normalizer (`KeccakAnf`)

Pure canonical $\mathbb{F}_2$ algebraic normal form (`toLin?`, `toAnf?`) deciding equality
between symbolic `KExpr` outputs of 2-lane NEON `keccak_f1600` rounds and `keccakRoundLane`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (KeccakState keccakRhoOffset)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
  (keccakC keccakD keccakTheta keccakRhoPiSrc keccakRhoPi keccakRoundLane
   rotateLeft_xor rotateLeft_zero_64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
  (KExpr KEnv evalKExpr)

@[expose] def xorInsert {α : Type} (eq lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if eq x y then ys
      else if lt x y then x :: y :: ys
      else y :: xorInsert eq lt x ys

@[expose] def xorMerge {α : Type} (eq lt : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => xorInsert eq lt x (xorMerge eq lt xs ys)

@[expose] def evalXorList {α : Type} (ev : α → BitVec 64) : List α → BitVec 64
  | [] => 0#64
  | x :: xs => ev x ^^^ evalXorList ev xs

private theorem xor_left_comm64 (a b c : BitVec 64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem evalXorList_xorInsert {α : Type} (eq lt : α → α → Bool)
    (heq : ∀ {a b : α}, eq a b = true → a = b)
    (ev : α → BitVec 64) (x : α) :
    ∀ (ys : List α), evalXorList ev (xorInsert eq lt x ys) = ev x ^^^ evalXorList ev ys
  | [] => rfl
  | y :: ys => by
      simp only [xorInsert]
      by_cases hxy : eq x y = true
      · simp only [hxy, ↓reduceIte]
        rw [heq hxy, evalXorList, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      · have hxyF : eq x y = false := Bool.eq_false_iff.mpr hxy
        simp only [hxyF, Bool.false_eq_true, ↓reduceIte]
        cases lt x y with
        | true => rfl
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, evalXorList,
              evalXorList_xorInsert eq lt heq ev x ys]
            exact (xor_left_comm64 (ev x) (ev y) _).symm

theorem evalXorList_xorMerge {α : Type} (eq lt : α → α → Bool)
    (heq : ∀ {a b : α}, eq a b = true → a = b)
    (ev : α → BitVec 64) :
    ∀ (xs ys : List α),
      evalXorList ev (xorMerge eq lt xs ys) = evalXorList ev xs ^^^ evalXorList ev ys
  | [], ys => by simp [xorMerge, evalXorList]
  | x :: xs, ys => by
      simp only [xorMerge, evalXorList, evalXorList_xorInsert eq lt heq,
        evalXorList_xorMerge eq lt heq ev xs ys, BitVec.xor_assoc]

private theorem rotl_comp64 (a : BitVec 64) (r k : Nat) :
    (a.rotateLeft r).rotateLeft k = a.rotateLeft ((r + k) % 64) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft]
  by_cases h1 : i < k % 64 <;> simp only [h1, ↓reduceDIte]
  · by_cases h2 : 64 - k % 64 + i < r % 64 <;>
      by_cases h3 : i < (r + k) % 64 % 64 <;>
      simp only [h2, h3, ↓reduceDIte] <;>
      (first | omega | (congr 1; omega))
  · by_cases h2 : i - k % 64 < r % 64 <;>
      by_cases h3 : i < (r + k) % 64 % 64 <;>
      simp only [h2, h3, ↓reduceDIte] <;>
      (first | omega | (congr 1; omega))

private theorem rotl_mod64 (a : BitVec 64) (r : Nat) :
    a.rotateLeft (r % 64) = a.rotateLeft r := by
  have h0 : a.rotateLeft 0 = a := by ext i hi; simp [BitVec.getElem_rotateLeft]
  have hc := (rotl_comp64 a 0 r).symm
  rwa [h0, Nat.zero_add] at hc

@[expose] def linAtomBeq (a b : Nat × Nat) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2 b.2

theorem linAtomBeq_eq_true {a b : Nat × Nat} (h : linAtomBeq a b = true) : a = b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  simp only [linAtomBeq, Bool.and_eq_true] at h
  rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2]

@[expose] def linLt (a b : Nat × Nat) : Bool :=
  if Nat.beq a.1 b.1 then Nat.blt a.2 b.2 else Nat.blt a.1 b.1

@[expose] def linListBeq : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => true
  | a :: as, b :: bs => linAtomBeq a b && linListBeq as bs
  | _, _ => false

theorem linListBeq_eq_true :
    ∀ {xs ys : List (Nat × Nat)}, linListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [linListBeq, Bool.and_eq_true] at h
      rw [linAtomBeq_eq_true h.1, linListBeq_eq_true h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [linListBeq] at h

@[expose] def linListLt : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if linAtomBeq a b then linListLt as bs else linLt a b

@[expose] def quadBeq (a b : List (Nat × Nat) × List (Nat × Nat)) : Bool :=
  linListBeq a.1 b.1 && linListBeq a.2 b.2

theorem quadBeq_eq_true {a b : List (Nat × Nat) × List (Nat × Nat)}
    (h : quadBeq a b = true) : a = b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  simp only [quadBeq, Bool.and_eq_true] at h
  rw [linListBeq_eq_true h.1, linListBeq_eq_true h.2]

@[expose] def quadLt (a b : List (Nat × Nat) × List (Nat × Nat)) : Bool :=
  if linListBeq a.1 b.1 then linListLt a.2 b.2 else linListLt a.1 b.1

@[expose] def quadListBeq :
    List (List (Nat × Nat) × List (Nat × Nat)) →
    List (List (Nat × Nat) × List (Nat × Nat)) → Bool
  | [], [] => true
  | a :: as, b :: bs => quadBeq a b && quadListBeq as bs
  | _, _ => false

theorem quadListBeq_eq_true :
    ∀ {xs ys : List (List (Nat × Nat) × List (Nat × Nat))},
      quadListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [quadListBeq, Bool.and_eq_true] at h
      rw [quadBeq_eq_true h.1, quadListBeq_eq_true h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [quadListBeq] at h

@[expose] def anfBeq
    (p q : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat))) : Bool :=
  linListBeq p.1 q.1 && quadListBeq p.2 q.2

theorem anfBeq_eq_true
    {p q : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat))}
    (h : anfBeq p q = true) : p = q := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [anfBeq, Bool.and_eq_true] at h
  rw [linListBeq_eq_true h.1, quadListBeq_eq_true h.2]

@[expose] def evalLinAtom (env : KEnv) (p : Nat × Nat) : BitVec 64 :=
  (if Nat.beq p.1 50 then keccakRcAt env.rLoop else env.vars p.1).rotateLeft p.2

@[expose] def evalQuadTerm (env : KEnv) (q : List (Nat × Nat) × List (Nat × Nat)) : BitVec 64 :=
  ~~~(evalXorList (evalLinAtom env) q.1) &&& evalXorList (evalLinAtom env) q.2

@[expose] def toLin? (rot : Nat) : KExpr → Option (List (Nat × Nat))
  | .var id => if Nat.beq id 50 then none else some [(id, rot % 64)]
  | .rcLoopVal => some [(50, rot % 64)]
  | .rotl e k => toLin? ((rot + k) % 64) e
  | .xor a b => do
      let la ← toLin? rot a
      let lb ← toLin? rot b
      pure (xorMerge linAtomBeq linLt la lb)
  | _ => none

theorem eval_toLin (env : KEnv) :
    ∀ (e : KExpr) (rot : Nat) {xs : List (Nat × Nat)},
      toLin? rot e = some xs →
      evalXorList (evalLinAtom env) xs = (evalKExpr env e).rotateLeft rot
  | .var id, rot, xs, h => by
      simp only [toLin?] at h
      split at h
      · simp at h
      · next hne =>
          simp only [Option.some.injEq] at h; subst h
          have hneF : Nat.beq id 50 = false := Bool.eq_false_iff.mpr hne
          simp only [evalXorList, evalLinAtom, hneF, Bool.false_eq_true, ↓reduceIte,
            BitVec.xor_zero, evalKExpr]
          exact rotl_mod64 _ _
  | .rcLoopVal, rot, xs, h => by
      simp only [toLin?, Option.some.injEq] at h; subst h
      simp only [evalXorList, evalLinAtom, Nat.beq_refl, ↓reduceIte, BitVec.xor_zero, evalKExpr]
      exact rotl_mod64 _ _
  | .rotl e k, rot, xs, h => by
      simp only [toLin?] at h
      rw [eval_toLin env e ((rot + k) % 64) h]
      simp [evalKExpr, rotl_comp64, Nat.add_comm]
  | .xor a b, rot, xs, h => by
      simp only [toLin?, bind, Option.bind] at h
      cases ha : toLin? rot a with
      | none => simp [ha] at h
      | some la =>
          simp only [ha] at h
          cases hb : toLin? rot b with
          | none => simp [hb] at h
          | some lb =>
              simp only [hb, pure, Option.some.injEq] at h; subst h
              rw [evalXorList_xorMerge linAtomBeq linLt linAtomBeq_eq_true,
                eval_toLin env a rot ha, eval_toLin env b rot hb,
                evalKExpr, rotateLeft_xor]
  | .const64 _, _, _, h | .spAdd _, _, _, h | .rcAdd _, _, _, h | .rcVal _, _, _, h
  | .rcLoopOff, _, _, h | .rcLoopPtr, _, _, h | .rcLoopNext, _, _, h
  | .bic _ _, _, _, h | .and64 _ _, _, _, h | .or64 _ _, _, _, h
  | .bsl _ _ _, _, _, h | .bitOp _ _ _, _, _, h | .add64 _ _, _, _, h
  | .shl _ _, _, _, h | .ushr _ _, _, _, h | .insByte0 _ _, _, _, h
  | .selHi255 _ _ _, _, _, h => by simp [toLin?] at h

@[expose] def toAnf? : KExpr → Option (List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat)))
  | .var id => if Nat.beq id 50 then none else some ([(id, 0)], [])
  | .rcLoopVal => some ([(50, 0)], [])
  | .rotl e k => do
      let l ← toLin? (k % 64) e
      pure (l, [])
  | .xor a b => do
      let (l1, q1) ← toAnf? a
      let (l2, q2) ← toAnf? b
      pure (xorMerge linAtomBeq linLt l1 l2, xorMerge quadBeq quadLt q1 q2)
  | .bic a b => do
      let la ← toLin? 0 a
      let lb ← toLin? 0 b
      pure ([], [(lb, la)])
  | _ => none

@[expose] def evalAnf (env : KEnv)
    (pq : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat))) : BitVec 64 :=
  evalXorList (evalLinAtom env) pq.1 ^^^ evalXorList (evalQuadTerm env) pq.2

theorem eval_toAnf (env : KEnv) :
    ∀ (e : KExpr) {pq : List (Nat × Nat) × List (List (Nat × Nat) × List (Nat × Nat))},
      toAnf? e = some pq → evalAnf env pq = evalKExpr env e
  | .var id, pq, h => by
      simp only [toAnf?] at h
      split at h
      · simp at h
      · next hne =>
          simp only [Option.some.injEq] at h; subst h
          have hneF : Nat.beq id 50 = false := Bool.eq_false_iff.mpr hne
          simp [evalAnf, evalXorList, evalLinAtom, hneF, evalKExpr, rotateLeft_zero_64]
  | .rcLoopVal, pq, h => by
      simp only [toAnf?, Option.some.injEq] at h; subst h
      simp [evalAnf, evalXorList, evalLinAtom, evalKExpr, rotateLeft_zero_64]
  | .rotl e k, pq, h => by
      simp only [toAnf?, bind, Option.bind] at h
      cases hl : toLin? (k % 64) e with
      | none => simp [hl] at h
      | some l =>
          simp only [hl, pure, Option.some.injEq] at h; subst h
          simp only [evalAnf, evalXorList, BitVec.xor_zero, eval_toLin env e (k % 64) hl, evalKExpr]
          exact rotl_mod64 _ _
  | .xor a b, pq, h => by
      simp only [toAnf?, bind, Option.bind] at h
      cases ha : toAnf? a with
      | none => simp [ha] at h
      | some pq1 =>
          simp only [ha] at h
          cases hb : toAnf? b with
          | none => simp [hb] at h
          | some pq2 =>
              simp only [hb, pure, Option.some.injEq] at h; subst h
              have ea := eval_toAnf env a ha
              have eb := eval_toAnf env b hb
              simp only [evalAnf,
                evalXorList_xorMerge linAtomBeq linLt linAtomBeq_eq_true,
                evalXorList_xorMerge quadBeq quadLt quadBeq_eq_true,
                evalKExpr, ← ea, ← eb]
              rw [BitVec.xor_assoc, ← BitVec.xor_assoc (evalXorList (evalLinAtom env) pq2.1),
                BitVec.xor_comm (evalXorList (evalLinAtom env) pq2.1),
                BitVec.xor_assoc, ← BitVec.xor_assoc]
  | .bic a b, pq, h => by
      simp only [toAnf?, bind, Option.bind] at h
      cases ha : toLin? 0 a with
      | none => simp [ha] at h
      | some la =>
          simp only [ha] at h
          cases hb : toLin? 0 b with
          | none => simp [hb] at h
          | some lb =>
              simp only [hb, pure, Option.some.injEq] at h; subst h
              simp [evalAnf, evalXorList, evalQuadTerm, eval_toLin env a 0 ha,
                eval_toLin env b 0 hb, evalKExpr, rotateLeft_zero_64]
  | .const64 _, _, h | .spAdd _, _, h | .rcAdd _, _, h | .rcVal _, _, h
  | .rcLoopOff, _, h | .rcLoopPtr, _, h | .rcLoopNext, _, h
  | .and64 _ _, _, h | .or64 _ _, _, h | .bsl _ _ _, _, h | .bitOp _ _ _, _, h
  | .add64 _ _, _, h | .shl _ _, _, h | .ushr _ _, _, h | .insByte0 _ _, _, h
  | .selHi255 _ _ _, _, h => by
      simp [toAnf?] at h

@[expose] def keccakCExpr (baseVar x : Nat) : KExpr :=
  .xor (.xor (.xor (.xor (.var (baseVar + x)) (.var (baseVar + 5 + x)))
    (.var (baseVar + 10 + x))) (.var (baseVar + 15 + x))) (.var (baseVar + 20 + x))

@[expose] def keccakDExpr (baseVar x : Nat) : KExpr :=
  .xor (keccakCExpr baseVar ((x + 4) % 5)) (.rotl (keccakCExpr baseVar ((x + 1) % 5)) 1)

@[expose] def keccakRhoPiExpr (baseVar k : Nat) : KExpr :=
  let src := keccakRhoPiSrc k
  .rotl (.xor (.var (baseVar + src)) (keccakDExpr baseVar (src % 5))) (keccakRhoOffset src)

@[expose] def keccakSpecRoundExpr (baseVar : Nat) (idx : Nat) : KExpr :=
  let x := idx % 5
  let y := idx / 5
  let chi := .xor (keccakRhoPiExpr baseVar (5 * y + x))
    (.bic (keccakRhoPiExpr baseVar (5 * y + (x + 2) % 5))
          (keccakRhoPiExpr baseVar (5 * y + (x + 1) % 5)))
  if idx == 0 then .xor chi .rcLoopVal else chi

theorem eval_keccakSpecRoundExpr (env : KEnv) (baseVar : Nat) (s : KeccakState)
    (hvars : ∀ i, i < 25 → env.vars (baseVar + i) = s.getD i 0#64) (idx : Nat) :
    evalKExpr env (keccakSpecRoundExpr baseVar idx) =
      keccakRoundLane s (keccakRcAt env.rLoop) idx := by
  have hc : ∀ x, x < 5 → evalKExpr env (keccakCExpr baseVar x) = keccakC s x := by
    intro x hx
    simp only [keccakCExpr, evalKExpr, keccakC]
    rw [hvars x (by omega),
        show baseVar + 5 + x = baseVar + (5 + x) by omega, hvars (5 + x) (by omega),
        show baseVar + 10 + x = baseVar + (10 + x) by omega, hvars (10 + x) (by omega),
        show baseVar + 15 + x = baseVar + (15 + x) by omega, hvars (15 + x) (by omega),
        show baseVar + 20 + x = baseVar + (20 + x) by omega, hvars (20 + x) (by omega)]
  have hsrc : ∀ k, keccakRhoPiSrc k < 25 := by
    intro k; unfold keccakRhoPiSrc; dsimp only; omega
  have hrp : ∀ k, evalKExpr env (keccakRhoPiExpr baseVar k) = keccakRhoPi s k := by
    intro k
    simp only [keccakRhoPiExpr, keccakDExpr, evalKExpr, keccakRhoPi, keccakTheta, keccakD,
      hvars (keccakRhoPiSrc k) (hsrc k),
      hc ((keccakRhoPiSrc k % 5 + 4) % 5) (by omega),
      hc ((keccakRhoPiSrc k % 5 + 1) % 5) (by omega)]
  unfold keccakSpecRoundExpr keccakRoundLane
  dsimp only
  split <;> simp only [evalKExpr, hrp]

theorem anf_eq_keccakRoundLane {env : KEnv} {e : KExpr} {baseVar idx : Nat} {s : KeccakState}
    (hvars : ∀ i, i < 25 → env.vars (baseVar + i) = s.getD i 0#64)
    (hchk : (match toAnf? e, toAnf? (keccakSpecRoundExpr baseVar idx) with
             | some p, some q => anfBeq p q
             | _, _ => false) = true) :
    evalKExpr env e = keccakRoundLane s (keccakRcAt env.rLoop) idx := by
  cases he : toAnf? e with
  | none => simp [he] at hchk
  | some p =>
      simp only [he] at hchk
      cases hs : toAnf? (keccakSpecRoundExpr baseVar idx) with
      | none => simp [hs] at hchk
      | some q =>
          simp only [hs] at hchk
          rw [anfBeq_eq_true hchk] at he
          rw [← eval_toAnf env e he, eval_toAnf env _ hs, eval_keccakSpecRoundExpr env baseVar s hvars]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf
