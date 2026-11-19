/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthMac
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Final

/-!
# Output-mode ideal endpoint for the FS-AEAD session hybrid

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

Characterizes the ideal endpoint (`hp N N la`) of the linear multi-session MAC-hop hybrid over
FS-AEAD sessions:

* `fsIdeal_eq_multiOtBranch_true`, `fsIdeal_mix_eq`: Bridge B (`multiOtBranch_true_eq_hybAOut`)
  identifies `multiOtBranch true N (multiSlotOtccaReductionOut … advBit B)` with a fresh session of
  `fsImpl … (hp N N la)` (exact distribution equality, `post j = 0`, so no reversed chain-PRG hops
  are needed on the wire side).
* `hpIdeal N la := ⟨N, none, la⟩` sets `Params.t := none` so every uncompromised index is `.ideal`.
* `fsImpl_step_main`, `fsImpl_step_la`, `allSessions_hp_eq_hpIdeal_main`,
  `allSessions_hp_eq_hpIdeal_la`: when each session makes at most `qs s` queries (`qs s ≤ N` for
  `la = false`, `qs s + (maxSkip + 1) ≤ N` for `la = true`), `fsImpl … (hp N N la)` equals
  `fsImpl … (hpIdeal N la)` across all lazily initialised sessions simultaneously, and every
  initialised session ends with `win = false` (`la = false`) or
  `lf = false ∧ senderCorruptedAt = none` (`la = true`).

The symmetric wire-side router hybrid (`fsWireHyb`) and combined libsignal session-hybrid bounds
live in `E2E/SessionAuthWire.lean`.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames.Lazy
open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5 CryptoGames.FSAEAD.Thm5.Ends

namespace CryptoVerification.E2E.Signed.SessionWire

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

open CryptoVerification.E2E.Signed CryptoVerification.E2E.Signed.SessionRouter
open CryptoVerification.E2E.Signed.SessionFS CryptoVerification.E2E.Signed.SessionFSMix
open CryptoVerification.E2E.Signed.SessionMac

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. Output-mode final endpoint: `hp N N la` = ideal FS-AEAD -/

/-- Ideal FS-AEAD parameters: `t = none` makes every uncompromised index `.ideal` regardless of
its index, while `j = N` keeps the chain slot `.unknown` up to `N` so the first corruption reveals a
fresh uniform chain key. -/
@[expose] def hpIdeal (N : ℕ) (la : Bool) : Params := ⟨N, none, la⟩

@[simp] theorem hpIdeal_j (N : ℕ) (la : Bool) : (hpIdeal N la).j = N := rfl
@[simp] theorem hpIdeal_t (N : ℕ) (la : Bool) : (hpIdeal N la).t = none := rfl
@[simp] theorem hpIdeal_la (N : ℕ) (la : Bool) : (hpIdeal N la).la = la := rfl

/-- Multi-session query predicate selecting queries addressed to session `s`. -/
@[expose] def sessQueryAt {ι : Type} (s : ℕ) : ℕ ⊕ ((_ : ℕ) × ι) → Bool
  | .inl _ => false
  | .inr t => decide (t.1 = s)

section FinalEndpoint

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Under `hpIdeal N la`, every uncompromised index is `.ideal` and every compromised index is
`.real`. -/
@[simp] theorem kind_hpIdeal (N : ℕ) (la : Bool) (st : HState CK MK AD M C) (i : ℕ) :
    kind (hpIdeal N la) (none : Option (SpecialOps AD M C ProbComp)) st i =
      if !st.isCompromised i then .ideal else .real := by
  simp [kind, hpIdeal]

/-- `hp N N la` and `hpIdeal N la` assign the same `Kind` whenever `i ≤ N` or `i` is compromised. -/
theorem kind_hp_eq_hpIdeal {N : ℕ} {la : Bool} {st : HState CK MK AD M C} {i : ℕ}
    (h : i ≤ N ∨ st.isCompromised i = true) :
    kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i =
      kind (hpIdeal N la) (none : Option (SpecialOps AD M C ProbComp)) st i := by
  rcases h with hi | hc
  · simp [kind, hp, hpIdeal, hi]
  · simp [kind, hp, hpIdeal, hc]

/-- Bridge B on `fsImpl`. Running `multiSlotOtccaReductionOut … advBit B` in the ideal
multi-slot OT-CCA world (`b = true`) has the exact same distribution as a fresh session of
`fsImpl … (hp N N la)`. -/
theorem fsIdeal_eq_multiOtBranch_true (N : ℕ) (la : Bool)
    (B : RatchetAdversary CK MK AD M C) :
    𝒟[multiOtBranch ideal ae true N
        (multiSlotOtccaReductionOut ideal ae G maxSkip N la advBit B)] =
      𝒟[fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsImpl ideal ae G maxSkip (hp N N la))) B).run s] := by
  rw [multiOtBranch_true_eq_hybAOut, hybridAOut, ← fsInit_bind_run]

/-- Bridge B on `oa`-mixtures (`post j = 0` on the wire side). -/
theorem fsIdeal_mix_eq {α : Type} (oa : ProbComp α)
    (aeO : α → AEADScheme MK (ℕ × AD) M C) (N : ℕ) (la : Bool)
    (B : α → RatchetAdversary CK MK AD M C) :
    𝒟[oa >>= fun o => multiOtBranch ideal (aeO o) true N
        (multiSlotOtccaReductionOut ideal (aeO o) G maxSkip N la advBit (B o))] =
      𝒟[oa >>= fun o => fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsImpl ideal (aeO o) G maxSkip (hp N N la))) (B o)).run s] :=
  evalDist_bind_congr oa _ _ fun o => fsIdeal_eq_multiOtBranch_true ideal (aeO o) G maxSkip N la (B o)

/-! ### Output-mode single-session properties at `hp N N la` -/

/-! ### Equivalence of `hp N N la` and unbounded-cutoff `hpIdeal N la` (`t = none`) -/

private theorem genN_hp_eq_hpIdeal {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (D : ℕ → ProbComp (CK × MK)) (N : ℕ) (la : Bool) :
    ∀ n : ℕ,
      (genN G (hp N N la) D n : StateT (HSt CK MK AD M C) m Unit) =
        genN G (hpIdeal N la) D n
  | 0 => rfl
  | n + 1 => by
    have hs : (genStep G (hp N N la) D : StateT (HSt CK MK AD M C) m Unit) =
        genStep G (hpIdeal N la) D := rfl
    simp only [genN, hs, genN_hp_eq_hpIdeal D N la n]

private theorem genUpTo_hp_eq_hpIdeal {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (D : ℕ → ProbComp (CK × MK)) (N : ℕ) (la : Bool) (i : ℕ) :
    (genUpTo G (hp N N la) D i : StateT (HSt CK MK AD M C) m Unit) =
      genUpTo G (hpIdeal N la) D i := by
  unfold genUpTo
  simp only [genN_hp_eq_hpIdeal]

private theorem encIdxWith_hp_eq_hpIdeal {N : ℕ} {la : Bool} {i : ℕ} (hi : i ≤ N)
    (a : AD) (msg : M) :
    (encIdxWith ideal ae (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) i a msg :
      StateT (HSt CK MK AD M C) ProbComp C) =
      encIdxWith ideal ae (hpIdeal N la) (none : Option (SpecialOps AD M C ProbComp)) i a msg := by
  ext s
  simp only [encIdxWith, StateT.run_bind, getH_run, pure_bind,
    kind_hp_eq_hpIdeal (Or.inl hi)]

private theorem decIdx_none_hp_eq_hpIdeal {N : ℕ} {la : Bool} {i : ℕ}
    (a : AD) (e : C) (s : HSt CK MK AD M C) (h : i ≤ N ∨ s.1.isCompromised i = true) :
    (decIdx ae (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s =
      (decIdx ae (hpIdeal N la) (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s := by
  simp only [decIdx, StateT.run_bind, getH_run, pure_bind, kind_hp_eq_hpIdeal h]

private theorem transmitHWith_hp_eq_hpIdeal {N : ℕ} {la : Bool} {s : HSt CK MK AD M C}
    (hi : s.1.lastSentIdx + 1 ≤ N) (q : AD × M) :
    (transmitHWith ideal ae G (hp N N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      (transmitHWith ideal ae G (hpIdeal N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s := by
  unfold transmitHWith
  simp only [StateT.run_bind, getH_run, pure_bind]
  split
  · rfl
  · rw [genUpTo_hp_eq_hpIdeal, encIdxWith_hp_eq_hpIdeal ideal ae hi]

private theorem challengeHWith_hp_eq_hpIdeal {N : ℕ} {la : Bool} {s : HSt CK MK AD M C}
    (hi : s.1.lastSentIdx + 1 ≤ N) (q : AD × M × M) :
    (challengeHWith ideal ae G (hp N N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      (challengeHWith ideal ae G (hpIdeal N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s := by
  unfold challengeHWith
  simp only [StateT.run_bind, getH_run, pure_bind]
  split
  · rfl
  · rw [genUpTo_hp_eq_hpIdeal, encIdxWith_hp_eq_hpIdeal ideal ae hi]

private theorem decIdx_some_eq (P : Params) (msg : M) (i : ℕ) (a : AD) (e : C) :
    (decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) (some msg) i a e :
      StateT (HSt CK MK AD M C) ProbComp (Option M)) = pure (some msg) := rfl

private theorem receiveH_some_hp_eq_hpIdeal (N : ℕ) (la : Bool) (msg : M) (a : AD) (c : ℕ × C) :
    (receiveH ae G maxSkip (hp N N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (some msg) a c :
      StateT (HSt CK MK AD M C) ProbComp (Option (ℕ × M))) =
      receiveH ae G maxSkip (hpIdeal N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (some msg) a c := by
  rcases c with ⟨i, e⟩
  ext s
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, decIdx_some_eq, hp_la, hpIdeal_la]
  by_cases h1 : s.1.skipped.contains i = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1
    · simp only [h2, ↓reduceIte]
    · simp only [h2, ↓reduceIte]
      by_cases h3 : (!la && decide (s.1.lastSentIdx < i) && !s.1.isCompromised i) = true
      · simp only [h3, ↓reduceIte]
      · simp only [h3, ↓reduceIte, genUpTo_hp_eq_hpIdeal G (m := ProbComp) (DG G) N la i]

private theorem deliverH_hp_eq_hpIdeal (N : ℕ) (la : Bool) (q : AD × (ℕ × C))
    (s : HSt CK MK AD M C) :
    (deliverH ae G maxSkip (hp N N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      (deliverH ae G maxSkip (hpIdeal N la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s := by
  have h : (deliverH ae G maxSkip (hp N N la) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) q :
        StateT (HSt CK MK AD M C) ProbComp (Option (ReceiveResult M))) =
    deliverH ae G maxSkip (hpIdeal N la) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) q := by
    unfold deliverH
    simp only [receiveH_some_hp_eq_hpIdeal]
  rw [h]

private theorem genStep_bind_congr_corr {P : Params} {D : ℕ → ProbComp (CK × MK)}
    {β : Type} {f g : Unit × HSt CK MK AD M C → ProbComp β} (s : HSt CK MK AD M C)
    (hfg : ∀ z : Unit × HSt CK MK AD M C,
      z.2.1.senderCorruptedAt = s.1.senderCorruptedAt → f z = g z) :
    ((genStep G P D : StateT (HSt CK MK AD M C) ProbComp Unit).run s >>= f) =
      ((genStep G P D : StateT (HSt CK MK AD M C) ProbComp Unit).run s >>= g) := by
  rcases s with ⟨st, sl⟩
  cases sl with
  | seed w =>
    simp only [genStep, StateT.run_mk, pure_bind]
    exact hfg _ rfl
  | mat pos mt =>
    simp only [genStep, StateT.run_mk]
    split
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun _ => hfg _ rfl
    · simp only [pure_bind]
      exact hfg _ rfl
  | unknown =>
    simp only [genStep, StateT.run_mk]
    split
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun _ => hfg _ rfl
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun _ => hfg _ rfl

private theorem genN_bind_congr_corr {P : Params} {D : ℕ → ProbComp (CK × MK)}
    {β : Type} :
    ∀ (n : ℕ) (s : HSt CK MK AD M C) {f g : Unit × HSt CK MK AD M C → ProbComp β},
      (∀ z : Unit × HSt CK MK AD M C,
        z.2.1.senderCorruptedAt = s.1.senderCorruptedAt → f z = g z) →
      ((genN G P D n : StateT (HSt CK MK AD M C) ProbComp Unit).run s >>= f) =
        ((genN G P D n : StateT (HSt CK MK AD M C) ProbComp Unit).run s >>= g)
  | 0, s, _, _, hfg => by
    simp only [genN, StateT.run_pure, pure_bind]
    exact hfg _ rfl
  | n + 1, s, f, g, hfg => by
    simp only [genN, StateT.run_bind, bind_assoc]
    exact genStep_bind_congr_corr G s fun z₁ hz₁ =>
      genN_bind_congr_corr n z₁.2 fun z₂ hz₂ => hfg z₂ (hz₂.trans hz₁)

private theorem receiveH_none_hp_eq_hpIdeal_main {b : Bool} {N rem : ℕ} (hrem : 0 < rem)
    {s : HSt CK MK AD M C} (hinv : InvWin b maxSkip N rem s.1) (a : AD) (c : ℕ × C) :
    (receiveH ae G maxSkip (hp N N false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) none a c).run s =
      (receiveH ae G maxSkip (hpIdeal N false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) none a c).run s := by
  rcases c with ⟨i, e⟩
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hp_la, hpIdeal_la]
  split
  · rename_i hskip
    have hi_cond : i ≤ N ∨ s.1.isCompromised i = true := by
      by_cases hc : s.1.isCompromised i = true
      · exact Or.inr hc
      · left
        simp only [Bool.not_eq_true] at hc
        have hle_rcv := hinv.skipped_le i (List.contains_iff_mem.mp hskip)
        cases hcorr : s.1.senderCorruptedAt with
        | none =>
          have := hinv.rcv_le_sent hcorr
          have := hinv.sent_bound
          omega
        | some c₀ =>
          have := hinv.corr_le c₀ hcorr
          have := hinv.sent_bound
          simp only [HState.isCompromised, hcorr, decide_eq_false_iff_not] at hc
          omega
    simp only [StateT.run_bind]
    rw [decIdx_none_hp_eq_hpIdeal ae a e s hi_cond]
  · split
    · rfl
    · by_cases hlook : (!false && decide (s.1.lastSentIdx < i) && !s.1.isCompromised i) = true
      · simp only [hlook, ↓reduceIte]
      · simp only [hlook, ↓reduceIte]
        have hi_cond : i ≤ N ∨ s.1.isCompromised i = true := by
          by_cases hc : s.1.isCompromised i = true
          · exact Or.inr hc
          · left
            simp only [Bool.not_eq_true] at hc
            simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
              decide_eq_true_eq, hc, Bool.and_true, not_lt] at hlook
            have := hinv.sent_bound
            omega
        rw [genUpTo_hp_eq_hpIdeal]
        simp only [genUpTo, StateT.run_bind, getH_run, pure_bind, bind_assoc]
        refine genN_bind_congr_corr G _ s fun z hz => ?_
        rcases z with ⟨_, s₁⟩
        dsimp only at hz
        have hi_cond' : i ≤ N ∨ s₁.1.isCompromised i = true := by
          simpa only [HState.isCompromised, hz] using hi_cond
        change ((do
            let msg? ← decIdx ae (hp N N false)
              (none : Option (SpecialOps AD M C ProbComp)) none i a e
            match msg? with
            | some msg =>
              modifyH fun st' => { st' with skipped := newSkipped s.1.receiverIdx i ++ st'.skipped }
              pure (some (i, msg))
            | none => pure none).run s₁) =
          ((do
            let msg? ← decIdx ae (hpIdeal N false)
              (none : Option (SpecialOps AD M C ProbComp)) none i a e
            match msg? with
            | some msg =>
              modifyH fun st' => { st' with skipped := newSkipped s.1.receiverIdx i ++ st'.skipped }
              pure (some (i, msg))
            | none => pure none).run s₁)
        simp only [StateT.run_bind]
        rw [decIdx_none_hp_eq_hpIdeal ae a e s₁ hi_cond']

private theorem receiveH_none_hp_eq_hpIdeal_la {N rem : ℕ} (hrem : 0 < rem)
    {s : HSt CK MK AD M C} (hinv : InvLA maxSkip N rem s.1) (a : AD) (c : ℕ × C) :
    (receiveH ae G maxSkip (hp N N true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) none a c).run s =
      (receiveH ae G maxSkip (hpIdeal N true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) none a c).run s := by
  rcases c with ⟨i, e⟩
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hp_la, hpIdeal_la]
  split
  · rename_i hskip
    have hi : i ≤ N := by
      have := hinv.skipped_le i (List.contains_iff_mem.mp hskip)
      have := hinv.rcv_le_sent
      have := hinv.sent_bound
      omega
    simp only [StateT.run_bind]
    rw [decIdx_none_hp_eq_hpIdeal ae a e s (Or.inl hi)]
  · split
    · rfl
    · rename_i hskip hout
      simp only [Bool.not_true, Bool.false_and, reduceCtorEq, ↓reduceIte]
      have hi : i ≤ N := by
        have := hinv.rcv_le_sent
        have := hinv.sent_bound
        omega
      rw [genUpTo_hp_eq_hpIdeal]
      simp only [StateT.run_bind]
      refine bind_congr fun z => ?_
      rw [decIdx_none_hp_eq_hpIdeal ae a e z.2 (Or.inl hi)]

/-- Single-query step in main mode (`la = false`): under `InvWin` with `0 < rem`, `hp N N false`
and `hpIdeal N false` produce the exact same state-and-answer distribution, and `InvWin` steps to
`rem - 1`. -/
theorem fsImpl_step_main {b : Bool} {N rem : ℕ} (hrem : 0 < rem) {s : HSt CK MK AD M C}
    (hinv : InvWin b maxSkip N rem s.1) (q : (fsSpec CK MK AD M C).Domain) :
    (fsImpl ideal ae G maxSkip (hp N N false) q).run s =
        (fsImpl ideal ae G maxSkip (hpIdeal N false) q).run s ∧
      ∀ z ∈ support ((fsImpl ideal ae G maxSkip (hp N N false) q).run s),
        InvWin b maxSkip N (rem - 1) z.2.1 := by
  have hi : s.1.lastSentIdx + 1 ≤ N := by have := hinv.sent_bound; omega
  rcases q with (((((q | q) | q) | q) | q) | q)
  · exact ⟨transmitHWith_hp_eq_hpIdeal ideal ae G hi q,
      fun z hz => invWin_transmitH ideal ae G maxSkip hrem hinv hz⟩
  · exact ⟨challengeHWith_hp_eq_hpIdeal ideal ae G hi q,
      fun z hz => invWin_challengeH ideal ae G maxSkip hrem hinv hz⟩
  · exact ⟨rfl, fun z hz => invWin_corruptSenderH G maxSkip q hinv hz⟩
  · exact ⟨rfl, fun z hz => invWin_corruptReceiverH G maxSkip q hinv hz⟩
  · exact ⟨deliverH_hp_eq_hpIdeal ae G maxSkip N false q s,
      fun z hz => invWin_deliverH ae G maxSkip hrem hinv hz⟩
  · refine ⟨?_, fun z hz => invWin_injectH ae G maxSkip hrem hinv hz⟩
    change (injectH ae G maxSkip (hp N N false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      (injectH ae G maxSkip (hpIdeal N false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s
    unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hp_la, hpIdeal_la]
    split
    · rfl
    · simp only [StateT.run_bind]
      rw [receiveH_none_hp_eq_hpIdeal_main ae G maxSkip hrem hinv q.1 q.2]

/-- Single-query step in lookahead mode (`la = true`): under `InvLA` with `0 < rem`, `hp N N true`
and `hpIdeal N true` produce the exact same state-and-answer distribution, and `InvLA` steps to
`rem - 1`. -/
theorem fsImpl_step_la {N rem : ℕ} (hrem : 0 < rem) {s : HSt CK MK AD M C}
    (hinv : InvLA maxSkip N rem s.1) (q : (fsSpec CK MK AD M C).Domain) :
    (fsImpl ideal ae G maxSkip (hp N N true) q).run s =
        (fsImpl ideal ae G maxSkip (hpIdeal N true) q).run s ∧
      ∀ z ∈ support ((fsImpl ideal ae G maxSkip (hp N N true) q).run s),
        InvLA maxSkip N (rem - 1) z.2.1 := by
  have hi : s.1.lastSentIdx + 1 ≤ N := by have := hinv.sent_bound; omega
  rcases q with (((((q | q) | q) | q) | q) | q)
  · exact ⟨transmitHWith_hp_eq_hpIdeal ideal ae G hi q,
      fun z hz => invLA_transmitH ideal ae G maxSkip hrem hinv hz⟩
  · exact ⟨challengeHWith_hp_eq_hpIdeal ideal ae G hi q,
      fun z hz => invLA_challengeH ideal ae G maxSkip hrem hinv hz⟩
  · exact ⟨rfl, fun z hz => invLA_corruptSenderH G maxSkip q hinv hz⟩
  · exact ⟨rfl, fun z hz => invLA_corruptReceiverH G maxSkip q hinv hz⟩
  · exact ⟨deliverH_hp_eq_hpIdeal ae G maxSkip N true q s,
      fun z hz => invLA_deliverH ae G maxSkip hrem hinv hz⟩
  · refine ⟨?_, fun z hz => invLA_injectH ae G maxSkip hrem hinv hz⟩
    change (injectH ae G maxSkip (hp N N true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      (injectH ae G maxSkip (hpIdeal N true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run s
    unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hp_la, hpIdeal_la]
    split
    · rfl
    · simp only [StateT.run_bind]
      rw [receiveH_none_hp_eq_hpIdeal_la ae G maxSkip hrem hinv q.1 q.2]

/-- Helper: `ProbComp` `bind` congruence from support-guarded equality (every uniform query in
`unifSpec` has full support). -/
private theorem probComp_bind_congr_support {α β : Type} (p : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a ∈ support p, f a = g a) : (p >>= f) = (p >>= g) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc]
    exact congrArg (query t >>= ·) (funext fun u => ih u fun a ha =>
      h a (MonadAttach.mem_support_bind.mpr ⟨u, mem_support_query t u, ha⟩))

/-! ### All-sessions ideal endpoint (`sessLift` over `lazyInit fsInit`) -/

/-- Multi-session invariant in main mode (`la = false`) tracking remaining query budget `rem s` per
session: uninitialised sessions satisfy `rem s ≤ N`, and initialised sessions satisfy `InvWin`. -/
private def AllSessInvMain (N : ℕ) (rem : ℕ → ℕ)
    (σ : ℕ → Option (HSt CK MK AD M C)) : Prop :=
  ∀ s, match σ s with
    | none => rem s ≤ N
    | some st => ∃ b, InvWin b maxSkip N (rem s) st.1

/-- Multi-session invariant in lookahead mode (`la = true`) tracking remaining query budget `rem s`
per session: uninitialised sessions satisfy `rem s + (maxSkip + 1) ≤ N`, and initialised sessions
satisfy `InvLA`. -/
private def AllSessInvLA (N : ℕ) (rem : ℕ → ℕ)
    (σ : ℕ → Option (HSt CK MK AD M C)) : Prop :=
  ∀ s, match σ s with
    | none => rem s + (maxSkip + 1) ≤ N
    | some st => InvLA maxSkip N (rem s) st.1

/-- All-sessions ideal equivalence & no-forgery invariant, main mode (`la = false`). When a
multi-session computation `Adv` makes at most `qs s ≤ N` queries to each session `s`, running all
sessions on `fsImpl … (hp N N false)` equals running all sessions on `fsImpl … (hpIdeal N false)`
(`t = none`, every uncompromised index ideal), and every initialised session ends with
`win = false`. -/
theorem allSessions_hp_eq_hpIdeal_main {β : Type}
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β)
    (qs : ℕ → ℕ) {N : ℕ}
    (hq : ∀ s, Adv.IsQueryBoundP (fun t => sessQueryAt s t = true) (qs s))
    (hN : ∀ s, qs s ≤ N) :
    (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)))) Adv).run
        (fun _ => none) =
      (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N false)))) Adv).run
        (fun _ => none) ∧
    ∀ z ∈ support
      ((simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)))) Adv).run
        (fun _ => none)),
      ∀ s st, z.2 s = some st → st.1.win = false := by
  suffices ∀ (rem : ℕ → ℕ) (σ : ℕ → Option (HSt CK MK AD M C)),
      (∀ s, Adv.IsQueryBoundP (fun t => sessQueryAt s t = true) (rem s)) →
      AllSessInvMain maxSkip N rem σ →
      (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)))) Adv).run
          σ =
        (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N false))))
          Adv).run σ ∧
      ∀ z ∈ support
        ((simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false))))
          Adv).run σ),
        AllSessInvMain maxSkip N (fun _ => 0) z.2 by
    rcases this qs (fun _ => none) hq (fun s => hN s) with ⟨heq, hsupp⟩
    refine ⟨heq, fun z hz s st hst => ?_⟩
    have hs := hsupp z hz s
    rw [hst] at hs
    rcases hs with ⟨_, hinv⟩
    exact hinv.win_false
  clear hq hN
  induction Adv using OracleComp.inductionOn with
  | pure a =>
    intro rem σ _ hinv
    refine ⟨by simp only [simulateQ_pure, StateT.run_pure], fun z hz s => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only [AllSessInvMain]
    have hs := hinv s
    cases hσ : σ s with
    | none => exact Nat.zero_le N
    | some st =>
      rw [hσ] at hs
      rcases hs with ⟨b, hb⟩
      exact ⟨b, hb.mono (Nat.zero_le _)⟩
  | query_bind t r ih =>
    intro rem σ hqb hinv
    rcases t with n | ⟨s₀, q⟩
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      have hqb' : ∀ u s, (r u).IsQueryBoundP (fun t => sessQueryAt s t = true) (rem s) := by
        intro u s
        have hs := hqb s
        rw [isQueryBoundP_query_bind_iff] at hs
        have h0 : sessQueryAt s (.inl n :
          (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = false := rfl
        simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h0,
          Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hs.2 u
      refine ⟨bind_congr fun u => (ih u rem σ (hqb' u) hinv).1, fun z hz => ?_⟩
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨u, _, hzu⟩
      exact (ih u rem σ (hqb' u) hinv).2 z hzu
    · have hqb_s₀ := hqb s₀
      rw [isQueryBoundP_query_bind_iff] at hqb_s₀
      have hrem_pos : 0 < rem s₀ := by simpa [sessQueryAt] using hqb_s₀.1
      let rem' : ℕ → ℕ := Function.update rem s₀ (rem s₀ - 1)
      have hqb' : ∀ u s, (r u).IsQueryBoundP (fun t => sessQueryAt s t = true) (rem' s) := by
        intro u s
        have hs := hqb s
        rw [isQueryBoundP_query_bind_iff] at hs
        by_cases hss : s₀ = s
        · subst hss
          have h1 : sessQueryAt s₀ (.inr ⟨s₀, q⟩ :
            (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = true := by
            simp [sessQueryAt]
          simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h1, ↓reduceIte,
            rem', Function.update_self] using hs.2 u
        · have hss' : s ≠ s₀ := Ne.symm hss
          have h0 : sessQueryAt s (.inr ⟨s₀, q⟩ :
            (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = false := by
            simp [sessQueryAt, hss]
          simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h0,
            Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, rem', Function.update_of_ne hss'] using
            hs.2 u
      have hstep_lazy :
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)) q).run (σ s₀) =
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N false)) q).run (σ s₀) ∧
          ∀ w ∈ support
            ((lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)) q).run (σ s₀)),
            match w.2 with
            | none => rem' s₀ ≤ N
            | some st' => ∃ b, InvWin b maxSkip N (rem' s₀) st'.1 := by
        have hinv_s₀ := hinv s₀
        cases hσ : σ s₀ with
        | none =>
          rw [hσ] at hinv_s₀
          simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind]
          have hinit_inv : ∀ b : Bool,
              InvWin b maxSkip N (rem s₀)
                (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown).1 :=
            fun b => ⟨rfl, rfl, by simpa [hInit] using hinv_s₀, by simp [hInit], by simp [hInit],
              by simp [hInit], by simp [hInit]⟩
          refine ⟨bind_congr fun b => by
              rw [(fsImpl_step_main ideal ae G maxSkip hrem_pos (hinit_inv b) q).1],
            fun w hw => ?_⟩
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
          rcases hw with ⟨b, _, z, hz, rfl⟩
          exact ⟨b, by
            simpa [rem'] using (fsImpl_step_main ideal ae G maxSkip hrem_pos (hinit_inv b) q).2 z hz⟩
        | some st =>
          rw [hσ] at hinv_s₀
          rcases hinv_s₀ with ⟨b, hb⟩
          rcases fsImpl_step_main ideal ae G maxSkip hrem_pos hb q with ⟨heq_q, hst_q⟩
          simp only [lazyInit_run_some']
          refine ⟨by rw [heq_q], fun w hw => ?_⟩
          simp only [map_eq_bind_pure_comp, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff] at hw
          rcases hw with ⟨z, hz, rfl⟩
          exact ⟨b, by simpa [rem'] using hst_q z hz⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, sessLift_inr, sessLiftCore, StateT.run_bind, StateT.run_mk, bind_map_left]
      have hall_inv : ∀ w ∈ support
          ((lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N false)) q).run (σ s₀)),
          AllSessInvMain maxSkip N rem' (Function.update σ s₀ w.2) := by
        intro w hw s
        by_cases hss : s = s₀
        · subst hss
          simpa [Function.update_self] using hstep_lazy.2 w hw
        · simpa [rem', Function.update_of_ne hss] using hinv s
      refine ⟨?_, fun z hz => ?_⟩
      · rw [← hstep_lazy.1]
        exact probComp_bind_congr_support _ _ _ fun w hw =>
          (ih w.1 rem' (Function.update σ s₀ w.2) (hqb' w.1) (hall_inv w hw)).1
      · rw [MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨w, hw, hzw⟩
        exact (ih w.1 rem' (Function.update σ s₀ w.2) (hqb' w.1) (hall_inv w hw)).2 z hzw

/-- All-sessions ideal equivalence & no-forgery invariant, lookahead mode (`la = true`). When a
multi-session computation `Adv` makes at most `qs s` queries to each session `s` with
`qs s + (maxSkip + 1) ≤ N`, running all sessions on `fsImpl … (hp N N true)` equals running all
sessions on `fsImpl … (hpIdeal N true)` (`t = none`), and every initialised session ends with
`lf = false ∧ senderCorruptedAt = none`. -/
theorem allSessions_hp_eq_hpIdeal_la {β : Type}
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β)
    (qs : ℕ → ℕ) {N : ℕ}
    (hq : ∀ s, Adv.IsQueryBoundP (fun t => sessQueryAt s t = true) (qs s))
    (hN : ∀ s, qs s + (maxSkip + 1) ≤ N) :
    (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)))) Adv).run
        (fun _ => none) =
      (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N true)))) Adv).run
        (fun _ => none) ∧
    ∀ z ∈ support
      ((simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)))) Adv).run
        (fun _ => none)),
      ∀ s st, z.2 s = some st → st.1.lf = false ∧ st.1.senderCorruptedAt = none := by
  suffices ∀ (rem : ℕ → ℕ) (σ : ℕ → Option (HSt CK MK AD M C)),
      (∀ s, Adv.IsQueryBoundP (fun t => sessQueryAt s t = true) (rem s)) →
      AllSessInvLA maxSkip N rem σ →
      (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)))) Adv).run
          σ =
        (simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N true))))
          Adv).run σ ∧
      ∀ z ∈ support
        ((simulateQ (sessLift (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true))))
          Adv).run σ),
        AllSessInvLA maxSkip N (fun _ => 0) z.2 by
    rcases this qs (fun _ => none) hq (fun s => hN s) with ⟨heq, hsupp⟩
    refine ⟨heq, fun z hz s st hst => ?_⟩
    have hs := hsupp z hz s
    rw [hst] at hs
    exact ⟨hs.lf_false, hs.corr_none⟩
  clear hq hN
  induction Adv using OracleComp.inductionOn with
  | pure a =>
    intro rem σ _ hinv
    refine ⟨by simp only [simulateQ_pure, StateT.run_pure], fun z hz s => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only [AllSessInvLA]
    have hs := hinv s
    cases hσ : σ s with
    | none =>
      rw [hσ] at hs
      omega
    | some st =>
      rw [hσ] at hs
      exact hs.mono (Nat.zero_le _)
  | query_bind t r ih =>
    intro rem σ hqb hinv
    rcases t with n | ⟨s₀, q⟩
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      have hqb' : ∀ u s, (r u).IsQueryBoundP (fun t => sessQueryAt s t = true) (rem s) := by
        intro u s
        have hs := hqb s
        rw [isQueryBoundP_query_bind_iff] at hs
        have h0 : sessQueryAt s (.inl n :
          (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = false := rfl
        simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h0,
          Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hs.2 u
      refine ⟨bind_congr fun u => (ih u rem σ (hqb' u) hinv).1, fun z hz => ?_⟩
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨u, _, hzu⟩
      exact (ih u rem σ (hqb' u) hinv).2 z hzu
    · have hqb_s₀ := hqb s₀
      rw [isQueryBoundP_query_bind_iff] at hqb_s₀
      have hrem_pos : 0 < rem s₀ := by simpa [sessQueryAt] using hqb_s₀.1
      let rem' : ℕ → ℕ := Function.update rem s₀ (rem s₀ - 1)
      have hqb' : ∀ u s, (r u).IsQueryBoundP (fun t => sessQueryAt s t = true) (rem' s) := by
        intro u s
        have hs := hqb s
        rw [isQueryBoundP_query_bind_iff] at hs
        by_cases hss : s₀ = s
        · subst hss
          have h1 : sessQueryAt s₀ (.inr ⟨s₀, q⟩ :
            (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = true := by
            simp [sessQueryAt]
          simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h1, ↓reduceIte,
            rem', Function.update_self] using hs.2 u
        · have hss' : s ≠ s₀ := Ne.symm hss
          have h0 : sessQueryAt s (.inr ⟨s₀, q⟩ :
            (unifSpec + multiSessSpec (fsSpec CK MK AD M C)).Domain) = false := by
            simp [sessQueryAt, hss]
          simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map, h0,
            Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, rem', Function.update_of_ne hss'] using
            hs.2 u
      have hstep_lazy :
          (lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)) q).run (σ s₀) =
            (lazyInit fsInit (fsImpl ideal ae G maxSkip (hpIdeal N true)) q).run (σ s₀) ∧
          ∀ w ∈ support
            ((lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)) q).run (σ s₀)),
            match w.2 with
            | none => rem' s₀ + (maxSkip + 1) ≤ N
            | some st' => InvLA maxSkip N (rem' s₀) st'.1 := by
        have hinv_s₀ := hinv s₀
        cases hσ : σ s₀ with
        | none =>
          rw [hσ] at hinv_s₀
          simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind]
          have hinit_inv : ∀ b : Bool,
              InvLA maxSkip N (rem s₀)
                (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown).1 :=
            fun b => ⟨rfl, rfl, by simpa [hInit] using hinv_s₀, by simp [hInit], by simp [hInit],
              by simp [hInit]⟩
          refine ⟨bind_congr fun b => by
              rw [(fsImpl_step_la ideal ae G maxSkip hrem_pos (hinit_inv b) q).1],
            fun w hw => ?_⟩
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
          rcases hw with ⟨b, _, z, hz, rfl⟩
          simpa [rem'] using (fsImpl_step_la ideal ae G maxSkip hrem_pos (hinit_inv b) q).2 z hz
        | some st =>
          rw [hσ] at hinv_s₀
          rcases fsImpl_step_la ideal ae G maxSkip hrem_pos hinv_s₀ q with ⟨heq_q, hst_q⟩
          simp only [lazyInit_run_some']
          refine ⟨by rw [heq_q], fun w hw => ?_⟩
          simp only [map_eq_bind_pure_comp, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff] at hw
          rcases hw with ⟨z, hz, rfl⟩
          simpa [rem'] using hst_q z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, sessLift_inr, sessLiftCore, StateT.run_bind, StateT.run_mk, bind_map_left]
      have hall_inv : ∀ w ∈ support
          ((lazyInit fsInit (fsImpl ideal ae G maxSkip (hp N N true)) q).run (σ s₀)),
          AllSessInvLA maxSkip N rem' (Function.update σ s₀ w.2) := by
        intro w hw s
        by_cases hss : s = s₀
        · subst hss
          simpa [Function.update_self] using hstep_lazy.2 w hw
        · simpa [rem', Function.update_of_ne hss] using hinv s
      refine ⟨?_, fun z hz => ?_⟩
      · rw [← hstep_lazy.1]
        exact probComp_bind_congr_support _ _ _ fun w hw =>
          (ih w.1 rem' (Function.update σ s₀ w.2) (hqb' w.1) (hall_inv w hw)).1
      · rw [MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨w, hw, hzw⟩
        exact (ih w.1 rem' (Function.update σ s₀ w.2) (hqb' w.1) (hall_inv w hw)).2 z hzw

end FinalEndpoint


end CryptoVerification.E2E.Signed.SessionWire
