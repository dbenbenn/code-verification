/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import

/-!
# Shallow `la = true` Ideal-Cutoff Hoare Proof for `redFSAuthMultiBucket`

Proves that `BucketFSAuthShallowBase.redFSAuthMultiBucket` outputs `false` on every supported
execution under lookahead (`la = true`, `FSLaSemantics`) ideal-cutoff multi-session FS-AEAD
semantics.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndTrue

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (Record healedBy)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header
  FSMultiSpec FSMultiBook sampleT)
open _root_.CryptoGames.SM.Engine (VP Ctx EState liftH abortE commitE vSend vRecv deliverE injectE)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (postLeak bucketAuthCfg)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState FSMultiBucketAuthEState liftFSMultiBucket lookupMultiBucketF
  regSessMultiBucket regSessOptMultiBucket rootFSMultiBucketAuth
  isHonestHdrMultiBucket hooksFSMultiBucketAuth initFSMultiBucketAuth implFSMultiBucketAuth
  redFSAuthMultiBucket)

structure FSLaSemantics (SS RS T M C : Type) where
  Safe : ∀ {α : Type}, (α → Prop) → OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α → Prop
  pure : ∀ {α : Type} {P : α → Prop} {a : α}, P a → Safe P (Pure.pure a)
  bind : ∀ {α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α}
    {f : α → OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) β},
    Safe P x → (∀ a, P a → Safe Q (f a)) → Safe Q (x >>= f)
  any : ∀ {α : Type} (x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α),
    Safe (fun _ => True) x
  ij_not_accepted : ∀ {RSt K I : Type} (sIdx : ℕ) (hdr : Header T) (e : ℕ × C)
    (hs : FSMultiBucketAuthState T RSt K I (ℕ × C)),
    Safe (fun p : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M) ×
        FSMultiBucketAuthState T RSt K I (ℕ × C) =>
      p.2 = hs ∧ ∀ i mo', p.1 ≠ some (.accepted i mo'))
      ((liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.injectQuery
          (SenderState := SS) (ReceiverState := RS) hdr e)).run hs)

section LaTrue

private theorem stateT_lift_laSafe {SS RS T M C : Type} (S : FSLaSemantics SS RS T M C)
    {St α : Type} (P : St → Prop) (s : St) (hs : P s)
    (x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α) :
    S.Safe (fun p : α × St => P p.2) ((StateT.lift x).run s) := by
  rw [StateT.run_lift]
  exact S.bind (S.any x) fun _ _ => S.pure hs

private theorem liftH_laSafe {SS RS T M C : Type} (S : FSLaSemantics SS RS T M C)
    {Γ RSt SS' RS' M' E' HS α : Type} (Q : HS → Prop)
    (es : EState (VP Γ T RSt SS' RS') M' (Header T × E') HS)
    (x : StateT HS (OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C))) α)
    (hx : S.Safe (fun p : α × HS => Q p.2) (x.run es.h)) :
    S.Safe (fun p : α × EState (VP Γ T RSt SS' RS') M' (Header T × E') HS => Q p.2.h)
      ((liftH x).run es) := by
  change S.Safe (fun p : α × EState (VP Γ T RSt SS' RS') M' (Header T × E') HS => Q p.2.h)
    (x.run es.h >>= fun r => Pure.pure (r.1, { es with h := r.2 }))
  exact S.bind hx fun ⟨_, _⟩ ha => S.pure ha

private theorem regSessMultiBucket_lfWin {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (h : FSMultiBucketAuthState T RSt K I E) :
    (regSessMultiBucket L gMain tL t0 ik h).2.lfWin = h.lfWin := by
  unfold regSessMultiBucket; dsimp only; split_ifs <;> rfl

private theorem regSessOptMultiBucket_lfWin {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (sid : Option I)
    (h : FSMultiBucketAuthState T RSt K I E) :
    (regSessOptMultiBucket L gMain tL t0 sid h).2.lfWin = h.lfWin := by
  unfold regSessOptMultiBucket
  cases sid with
  | none => rfl
  | some ik => exact regSessMultiBucket_lfWin L gMain tL t0 ik h

private theorem lookupMultiBucketF_la_safe {SS RS T M C RSt K I : Type}
    [DecidableEq I] [SampleableType K] (S : FSLaSemantics SS RS T M C)
    (t0 : ℕ) (ik : I) (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      ((lookupMultiBucketF (SS := SS) (RS := RS) (T := T) (M := M) (E := ℕ × C) t0 ik).run h) := by
  unfold lookupMultiBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some _ => simp only [StateT.run_pure]; exact S.pure hh
  | none =>
    simp only [StateT.run_bind]
    refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _) fun ⟨_, _⟩ hh1 => ?_
    simp only [StateT.run_modify, pure_bind, StateT.run_pure]
    exact S.pure hh1

private theorem rootFSMultiBucketAuth_la_safe {SS RS T M C KR RSt I K : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K] (S : FSLaSemantics SS RS T M C)
    (prng : PRFPRNG KR RSt I K) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl0 : Bool) (ik0 : I) (σ0 : RSt)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      ((rootFSMultiBucketAuth (SS := SS) (RS := RS) (T := T) (M := M) (E := ℕ × C)
        prng Δcka qep tL par t0 pl0 ik0 σ0).run h) := by
  unfold rootFSMultiBucketAuth; dsimp only
  split_ifs
  · simp only [StateT.run_pure]; exact S.pure hh
  · simp only [StateT.run_bind]
    refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _) fun ⟨_, h1⟩ hh1 => ?_
    refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h1 hh1 _) fun ⟨_, _⟩ hh2 => ?_
    simp only [StateT.run_pure]; exact S.pure hh2
  · simp only [StateT.run_bind]
    refine S.bind (lookupMultiBucketF_la_safe S t0 ik0 h hh) fun ⟨_, _⟩ hh1 => ?_
    simp only [StateT.run_pure]; exact S.pure hh1
  · simp only [StateT.run_bind]
    refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _) fun ⟨_, h1⟩ hh1 => ?_
    refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h1 hh1 _) fun ⟨_, _⟩ hh2 => ?_
    simp only [StateT.run_pure]; exact S.pure hh2
  · simp only [StateT.run_bind]
    refine S.bind (lookupMultiBucketF_la_safe S t0 ik0 h hh) fun ⟨_, _⟩ hh1 => ?_
    simp only [StateT.run_pure]; exact S.pure hh1
  · simp only [StateT.run_pure]; exact S.pure hh

private theorem initFSMultiBucketAuth_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K] (S : FSLaSemantics SS RS T M C)
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (lam : I) (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) :
    S.Safe (fun p => p.2.lfWin = false)
      ((initFSMultiBucketAuth L cka prng fs lam Δcka qep gMain tL par).run
        ({} : FSMultiBucketAuthState T RSt K I (ℕ × C))) := by
  unfold initFSMultiBucketAuth
  simp only [StateT.run_bind]
  refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false)
    ({} : FSMultiBucketAuthState T RSt K I (ℕ × C)) rfl _) fun ⟨kr, h1⟩ hh1 => ?_
  refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h1 hh1 _) fun ⟨_, h2⟩ hh2 => ?_
  refine S.bind (rootFSMultiBucketAuth_la_safe S prng Δcka qep tL par 0 false lam
    (prng.init kr) h2 hh2) fun ⟨⟨_, _, sid⟩, h3⟩ hh3 => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  apply S.pure
  split_ifs
  · rw [regSessOptMultiBucket_lfWin]; exact hh3
  · exact hh3

private theorem hooks_startSend_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (r0 : Option CCoins)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startSend
        ctx P t0 γ0 σ0 r0).run h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  have hcoins : S.Safe (fun p : CCoins × _ => p.2.lfWin = false)
      ((match r0 with | some c => Pure.pure c | none => StateT.lift (sampleT CCoins)).run h) := by
    cases r0 with
    | some _ => simp only [StateT.run_pure]; exact S.pure hh
    | none => exact stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _
  simp only [StateT.run_bind]
  refine S.bind hcoins fun ⟨coins, h1⟩ hh1 => ?_
  refine S.bind (rootFSMultiBucketAuth_la_safe S prng Δcka qep tL par t0 (postLeak tL ctx)
    (cka.send γ0 coins).2.2 σ0 h1 hh1) fun ⟨⟨_, _, sid⟩, h2⟩ hh2 => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  exact S.pure (by simpa [regSessOptMultiBucket_lfWin] using hh2)

private theorem hooks_startRecv_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startRecv
        ctx P t0 γ0 σ0 tn0).run h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hc : h.cache t0 with
  | some val =>
    rcases val with ⟨tCached, σc, kVal, optIdx⟩
    by_cases ht : tCached = tn0
    · simp only [ht, ↓reduceIte]; exact S.pure hh
    · simp only [ht, ↓reduceIte]
      split_ifs
      · exact S.pure hh
      · exact S.pure hh
      · exact S.pure hh
      · exact S.pure hh
      · change S.Safe _ ((do
          let _ ← lookupMultiBucketF t0 (cka.receive γ0 tn0).2
          let s1 ← get
          set (regSessMultiBucket L false tL t0 (cka.receive γ0 tn0).2 s1).2
          return some (some ((cka.receive γ0 tn0).1, (prng.up σ0 (cka.receive γ0 tn0).2).1,
            Sum.inr (regSessMultiBucket L false tL t0 (cka.receive γ0 tn0).2 s1).1))).run h)
        simp only [StateT.run_bind]
        refine S.bind (lookupMultiBucketF_la_safe S t0 (cka.receive γ0 tn0).2 h hh) fun ⟨_, h1⟩ hh1 => ?_
        simp only [StateT.run_get, StateT.run_set, pure_bind]
        exact S.pure (by simpa [regSessMultiBucket_lfWin] using hh1)
      · simp only [StateT.run_bind]
        refine S.bind (lookupMultiBucketF_la_safe S t0 (cka.receive γ0 tn0).2 h hh) fun ⟨_, _⟩ hh1 => ?_
        exact S.pure hh1
      · exact S.pure hh
      · exact S.pure hh
  | none =>
    split_ifs
    · exact S.pure hh
    · exact S.pure hh
    · exact S.pure hh
    · exact S.pure hh
    · change S.Safe _ ((do
        let _ ← lookupMultiBucketF t0 (cka.receive γ0 tn0).2
        let s1 ← get
        set (regSessMultiBucket L false tL t0 (cka.receive γ0 tn0).2 s1).2
        return some (some ((cka.receive γ0 tn0).1, (prng.up σ0 (cka.receive γ0 tn0).2).1,
          Sum.inr (regSessMultiBucket L false tL t0 (cka.receive γ0 tn0).2 s1).1))).run h)
      simp only [StateT.run_bind]
      refine S.bind (lookupMultiBucketF_la_safe S t0 (cka.receive γ0 tn0).2 h hh) fun ⟨_, h1⟩ hh1 => ?_
      simp only [StateT.run_get, StateT.run_set, pure_bind]
      exact S.pure (by simpa [regSessMultiBucket_lfWin] using hh1)
    · simp only [StateT.run_bind]
      refine S.bind (lookupMultiBucketF_la_safe S t0 (cka.receive γ0 tn0).2 h hh) fun ⟨_, _⟩ hh1 => ?_
      exact S.pure hh1
    · exact S.pure hh
    · exact S.pure hh

private theorem hooks_fsSend_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsSend
        ctx P t0 ssv hdr m pair).run h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  cases ssv with
  | inl _ => simp only [StateT.run_pure]; exact S.pure hh
  | inr sIdx =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    refine S.bind (P := fun p : Bool × FSMultiBucketAuthState T RSt K I (ℕ × C) => p.2.lfWin = false)
      (by split_ifs
          · rw [StateT.run_bind]
            refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _)
              fun ⟨csRes, _⟩ hh1 => ?_
            cases csRes <;> exact S.pure hh1
          · exact S.pure hh)
      fun ⟨ok, h1⟩ hh1 => ?_
    cases ok with
    | false => exact S.pure hh1
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine S.bind (P := fun p => p.2.lfWin = false)
        (by cases pair <;> exact stateT_lift_laSafe S (fun st => st.lfWin = false) h1 hh1 _)
        fun ⟨e?, _⟩ hh2 => ?_
      cases e? <;> exact S.pure hh2

private theorem hooks_fsRecv_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (rsv : RS ⊕ ℕ) (hdr : Header T) (e : ℕ × C)
    (rec : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsRecv
        ctx P t0 rsv hdr e rec).run h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  cases rsv with
  | inl _ => simp only [StateT.run_pure]; exact S.pure hh
  | inr sIdx =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    refine S.bind (P := fun p : Bool × FSMultiBucketAuthState T RSt K I (ℕ × C) => p.2.lfWin = false)
      (by split_ifs
          · rw [StateT.run_bind]
            refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _)
              fun ⟨csRes, _⟩ hh1 => ?_
            cases csRes <;> exact S.pure hh1
          · exact S.pure hh)
      fun ⟨ok, h1⟩ hh1 => ?_
    cases ok with
    | false => exact S.pure hh1
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      split
      · rename_i his
        rcases Option.isSome_iff_exists.mp his with ⟨_, hm⟩
        refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h1 hh1 _)
          fun ⟨res, _⟩ hh2 => ?_
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · exact S.pure hh2
        · exact S.pure hh2
        · dsimp only
          simp only [hm, Option.isNone_some, Bool.and_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
          refine S.bind (P := fun p => p.2.lfWin = false) (S.pure hh2) fun ⟨_, _⟩ hh3 => ?_
          cases mo' <;> cases rec <;> exact S.pure hh3
      · refine S.bind (S.ij_not_accepted sIdx hdr e h1) fun ⟨res, h2⟩ ⟨hh2_eq, hnotacc⟩ => ?_
        subst hh2_eq
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · exact S.pure hh1
        · exact S.pure hh1
        · exact False.elim (hnotacc i mo' rfl)

private theorem hooks_reveal_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).reveal
        ctx P vp).run h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  split
  · exact S.pure hh
  · rw [StateT.run_bind]
    rcases vp.vS with _ | (_ | sIdx)
    · dsimp only; split_ifs <;> exact S.pure hh
    · dsimp only; split_ifs <;> exact S.pure hh
    · simp only [StateT.run_bind, bind_assoc]
      refine S.bind (stateT_lift_laSafe S (fun st => st.lfWin = false) h hh _)
        fun ⟨csRes, _⟩ hh1 => ?_
      cases csRes with
      | none => exact S.pure hh1
      | some _ => dsimp only; split_ifs <;> exact S.pure hh1

private theorem vSend_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (m : M) (pair : Option (M × M))
    (r : Option CCoins) (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      ((vSend (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
        ctx P vp m pair r).run h) := by
  unfold vSend; dsimp only
  split_ifs
  · simp only [StateT.run_bind]
    refine S.bind (hooks_startSend_la_safe S L cka prng fs Δcka qep gMain tL par la
      ctx P (vp.tcur + 1) vp.γ vp.root r h hh) fun ⟨res, h1⟩ hh1 => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · exact S.pure hh1
    · simp only [pure_bind]; rw [StateT.run_bind]
      refine S.bind (hooks_fsSend_la_safe S L cka prng fs Δcka qep gMain tL par la
        ctx P (vp.tcur + 1) ss (vp.tcur + 1, some T') m pair h1 hh1) fun ⟨res2, _⟩ hh2 => ?_
      cases res2 <;> exact S.pure hh2
  · simp only [pure_bind]
    cases vp.vS with
    | none => exact S.pure hh
    | some v =>
      dsimp only; rw [StateT.run_bind]
      refine S.bind (hooks_fsSend_la_safe S L cka prng fs Δcka qep gMain tL par la
        ctx P vp.tcur v (vp.tcur, vp.curCkaMsg) m pair h hh) fun ⟨res2, _⟩ hh2 => ?_
      cases res2 <;> exact S.pure hh2

private theorem vRecv_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (c : Header T × (ℕ × C))
    (rec : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) (hh : h.lfWin = false) :
    S.Safe (fun p => p.2.lfWin = false)
      ((vRecv (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
        ctx P vp c rec).run h) := by
  unfold vRecv; dsimp only
  split_ifs with hbad heq
  · exact S.pure hh
  · cases c.1.2 with
    | none => exact S.pure hh
    | some Tn =>
      simp only [StateT.run_bind]
      refine S.bind (hooks_startRecv_la_safe S L cka prng fs Δcka qep gMain tL par la
        ctx P c.1.1 vp.γ vp.root Tn h hh) fun ⟨res, h1⟩ hh1 => ?_
      rcases res with _ | (_ | ⟨γ', σ', rs⟩)
      · exact S.pure hh1
      · exact S.pure hh1
      · simp only [pure_bind, Function.update_self]; rw [StateT.run_bind]
        refine S.bind (hooks_fsRecv_la_safe S L cka prng fs Δcka qep gMain tL par la
          ctx P c.1.1 rs c.1 c.2 rec h1 hh1) fun ⟨res2, _⟩ hh2 => ?_
        rcases res2 with _ | (_ | ⟨_, _, _⟩) <;> exact S.pure hh2
  · simp only [pure_bind]
    cases vp.vR c.1.1 with
    | none => exact S.pure hh
    | some v =>
      dsimp only; rw [StateT.run_bind]
      refine S.bind (hooks_fsRecv_la_safe S L cka prng fs Δcka qep gMain tL par la
        ctx P c.1.1 v c.1 c.2 rec h hh) fun ⟨res2, _⟩ hh2 => ?_
      rcases res2 with _ | (_ | ⟨_, _, _⟩) <;> exact S.pure hh2

private theorem commitE_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)) (P : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (hes : es.h.lfWin = false) :
    S.Safe (fun p => p.2.h.lfWin = false)
      ((commitE (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la) s P old new pos).run es) := by
  unfold commitE; rw [StateT.run_bind]
  refine S.bind (liftH_laSafe S (fun h => h.lfWin = false) es _ (by
    dsimp only [hooksFSMultiBucketAuth]; exact S.pure hes)) fun ⟨o, _⟩ hes1 => ?_
  cases o <;> exact S.pure hes1

private theorem deliverE_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (cfg : _root_.CryptoGames.SM.Config M) (P : Party) (c : Header T × (ℕ × C))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (hes : es.h.lfWin = false) :
    S.Safe (fun p => p.2.h.lfWin = false)
      ((deliverE (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la) maxSkip cfg (P, c)).run es) := by
  unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact S.pure hes
  · cases es.g.inTransit P.other c with
    | none => exact S.pure hes
    | some r =>
      dsimp only; rw [StateT.run_bind]
      refine S.bind (liftH_laSafe S (fun h => h.lfWin = false) es _
        (vRecv_la_safe S L cka prng fs Δcka qep gMain tL par la es.g P (es.g.st P) c (some r) es.h hes))
        fun ⟨vr, es1⟩ hes1 => ?_
      rcases vr with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind]; exact S.pure hes1
      · dsimp only; split <;> exact S.pure hes1
      · dsimp only; rw [StateT.run_bind]
        refine S.bind (commitE_la_safe S L cka prng fs Δcka qep gMain tL par la
          es.g P (es.g.st P) st' r.pos es1 hes1) fun ⟨s1?, _⟩ hes2 => ?_
        cases s1? <;> exact S.pure hes2

private theorem injectE_la_safe {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (Δ : ℕ) (cfg : _root_.CryptoGames.SM.Config M) (P : Party) (c : Header T × (ℕ × C))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (hes : es.h.lfWin = false) :
    S.Safe (fun p => p.2.h.lfWin = false)
      ((injectE (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la) Δ qep cfg (P, c)).run es) := by
  unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact S.pure hes
  · rw [StateT.run_bind]
    refine S.bind (liftH_laSafe S (fun h => h.lfWin = false) es _
      (vRecv_la_safe S L cka prng fs Δcka qep gMain tL par la es.g P (es.g.st P) c none es.h hes))
      fun ⟨vr, es1⟩ hes1 => ?_
    rcases vr with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind]; exact S.pure hes1
    · exact S.pure hes1
    · dsimp only; split
      · exact S.pure hes1
      · split
        · rw [StateT.run_bind]
          refine S.bind (commitE_la_safe S L cka prng fs Δcka qep gMain tL par la
            es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ es1 hes1) fun ⟨s1?, _⟩ hes2 => ?_
          cases s1? <;> exact S.pure hes2
        · split <;> exact S.pure hes1

private theorem implFSMultiBucketAuth_step_la_safe
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (t : (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
      (Header T × (ℕ × C))).Domain)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I)
    (hst : st.1.h.lfWin = false) :
    let hk := hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la
    S.Safe (fun p => p.2.1.h.lfWin = false)
      ((implFSMultiBucketAuth hk Δcka qep maxSkip gMain tL t).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  dsimp only at hst
  unfold implFSMultiBucketAuth
  rcases t with u | ((((⟨P, m, r⟩ | _) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · exact stateT_lift_laSafe S (fun s => s.1.h.lfWin = false) (es0, winEp0) hst _
  · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact S.pure hst
    · cases es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => exact S.pure hst
      | some s₁ =>
        dsimp only; simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
        refine S.bind (vSend_la_safe S L cka prng fs Δcka qep gMain tL par la
          s₁ P (s₁.st P) m none r es0.h hst) fun ⟨res, _⟩ hh' => ?_
        cases res <;> exact S.pure hh'
  · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]; exact S.pure hst
  · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_lift, bind_assoc]
    exact S.bind (deliverE_la_safe S L cka prng fs Δcka qep maxSkip gMain tL par la
      (bucketAuthCfg Δcka tL) P c es0 hst) fun ⟨_, _⟩ hes' => S.pure hes'
  · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_lift, bind_assoc]
    exact S.bind (injectE_la_safe S L cka prng fs Δcka qep gMain tL par la
      (2 + Δcka) (bucketAuthCfg Δcka tL) P c es0 hst) fun ⟨_, _⟩ hes' => S.pure hes'
  · simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact S.pure hst
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
      refine S.bind (hooks_reveal_la_safe S L cka prng fs Δcka qep gMain tL par la
        es0.g P (es0.g.st P) es0.h hst) fun ⟨res, _⟩ hh' => ?_
      cases res <;> exact S.pure hh'

private theorem simulateQ_implFSMultiBucketAuth_la_safe
    {KC Γ CCoins T I KR RSt K SS RS M C α : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (oa : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
      (Header T × (ℕ × C))) α) :
    ∀ (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I),
      st.1.h.lfWin = false →
      S.Safe (fun p => p.2.1.h.lfWin = false)
        ((simulateQ
          (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
            Δcka qep maxSkip gMain tL) oa).run st) := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro st hst
    simp only [simulateQ_pure, StateT.run_pure]
    exact S.pure hst
  | query_bind t _ ih =>
    intro st hst
    simp only [simulateQ_query_bind, StateT.run_bind]
    exact S.bind (implFSMultiBucketAuth_step_la_safe S L cka prng fs Δcka qep maxSkip
      gMain tL par la t st hst) fun ⟨a, st'⟩ hst' => ih a st' hst'

theorem redFSAuthMultiBucket_true_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (S : FSLaSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (lam : I) (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins (ℕ × C)) :
    S.Safe (fun b => b = false)
      (redFSAuthMultiBucket L cka prng fs lam Δcka qep gMain true tL par A) := by
  unfold redFSAuthMultiBucket
  refine S.bind (initFSMultiBucketAuth_la_safe S L cka prng fs lam Δcka qep gMain tL par)
    fun ⟨⟨vA, vB⟩, h0⟩ hh0 => ?_
  dsimp only
  refine S.bind (simulateQ_implFSMultiBucketAuth_la_safe S L cka prng fs Δcka qep fs.maxSkip
    gMain tL par true A
    ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false },
       h := h0, abort := false }, none) hh0) fun ⟨_, es, _⟩ hes => ?_
  simp only [↓reduceIte]
  exact S.pure hes

end LaTrue

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndTrue
