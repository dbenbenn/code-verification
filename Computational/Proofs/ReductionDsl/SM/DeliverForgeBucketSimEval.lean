/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation

set_option autoImplicit false

namespace CryptoGames.SM.Engine

public section

open ReductionDsl OracleSpec OracleComp Prod Sum
open scoped ENNReal Computational.Proofs.ReductionDsl.Notation
open Construction CKA DeliverForge

section BucketEngineLemmas

variable {Γ T RSt SS RS M E CCoins : Type}

/-- Trivial doom-free `Policy` (`tStar = 0`, `auth = false`) under which `leakDoom` and `corrDoom`
are identically `false`, so `transmitE`, `corrE`, and `corrEPaper` reduce to `transmitEBucket`,
`corrEBucket`, and `corrEPaperBucket`. -/
@[expose] def noDoomPolicy : Policy := ⟨false, none, 0⟩

@[simp] private theorem noDoomPolicy_leakDoom {VPt M C : Type}
    (s₀ s₁ : GameState VPt M C) : noDoomPolicy.leakDoom s₀ s₁ = false := by
  simp [noDoomPolicy, Policy.leakDoom]

@[simp] private theorem noDoomPolicy_corrDoom {VPt M C : Type}
    (s : GameState VPt M C) (P : Party) : noDoomPolicy.corrDoom s P = false := by
  simp [noDoomPolicy, Policy.corrDoom]

theorem transmitEBucket_eq_transmitE {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} [Inhabited E]
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV) (Δ qep : ℕ) :
    DeliverForge.transmitEBucket hk Δ qep = transmitE hk Δ qep noDoomPolicy := by
  funext ⟨P, m, r⟩
  apply StateT.ext; intro es
  unfold DeliverForge.transmitEBucket transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win)
  · simp [hab]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · rfl
    · simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]; rfl

theorem corrEBucket_eq_corrE {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV) :
    DeliverForge.corrEBucket hk = corrE hk noDoomPolicy := by
  funext P
  apply StateT.ext; intro es
  unfold DeliverForge.corrEBucket corrE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, noDoomPolicy_leakDoom,
      noDoomPolicy_corrDoom, Bool.or_self]; rfl

theorem corrEPaperBucket_eq_corrEPaper {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV) :
    DeliverForge.corrEPaperBucket hk = corrEPaper hk noDoomPolicy := by
  funext P
  apply StateT.ext; intro es
  unfold DeliverForge.corrEPaperBucket corrEPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, noDoomPolicy_leakDoom,
      noDoomPolicy_corrDoom, Bool.or_self]; rfl

theorem transmitEBucket_win_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} [Inhabited E]
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV) (Δ qep : ℕ)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × M × Option CCoins) :
    ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep arg).run es),
      res.2.g.win = es.g.win := by
  rcases arg with ⟨P, m, r⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.transmitEBucket abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
      have hw1 : s₁.win = es.g.win := by
        unfold GameState.epMgmt at hep
        by_cases h1 : P.sendsIn (es.g.epoch P + 1)
        · by_cases h2 : qep < es.g.epoch P + 1
          · simp [h1, h2] at hep
          · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hep
            subst hep
            by_cases h3 : (r.isSome && !(es.g.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
        · by_cases h2 : qep < es.g.epoch P
          · simp [h1, h2] at hep
          · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at hep
            subst hep; rfl
      rcases vsRes with _ | ⟨st', ct⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        simp [GameState.record, hw1]

theorem deliverE_win_eq_of_deliverWin_false {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {maxSkip : ℕ} (cfg : Config M) (hCfgWin : cfg.deliverWin = false)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((deliverE hk maxSkip cfg arg).run es),
      res.2.g.win = es.g.win := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hin : es.g.inTransit P.other c with _ | r
    · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hin, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h₁⟩, _, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · dsimp only at hmem
        simp only [hCfgWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · dsimp only at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨cmRes, es₁⟩, hcm, hmem⟩ := hmem
        have hcmWin : es₁.g.win = es.g.win ∧ ∀ s₁, cmRes = some s₁ → s₁.win = es.g.win := by
          unfold commitE abortE at hcm
          rw [run_liftH_bind, mem_support_bind_iff] at hcm
          obtain ⟨⟨ans, h₂⟩, _, hcm⟩ := hcm
          rcases ans with _ | new'
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcm
            obtain ⟨hcm1, hcm2⟩ := hcm; subst hcm2
            exact ⟨rfl, fun _ hs => by rw [hcm1] at hs; cases hs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcm
            obtain ⟨hcm1, hcm2⟩ := hcm; subst hcm2
            refine ⟨rfl, fun _ hs => ?_⟩
            rw [hcm1] at hs; cases hs
            dsimp only
            simp [GameState.accept, GameState.delete]
        rcases cmRes with _ | s₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hcmWin.1
        · simp only [hCfgWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hcmWin.2 s₁ rfl

theorem corrEBucket_win_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS) (P : Party) :
    ∀ res ∈ support ((DeliverForge.corrEBucket hk P).run es),
      res.2.g.win = es.g.win := by
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.corrEBucket abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
    rcases revRes with _ | st
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; simp [GameState.afterCorr, GameState.leak]

theorem corrEPaperBucket_win_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS) (P : Party) :
    ∀ res ∈ support ((DeliverForge.corrEPaperBucket hk P).run es),
      res.2.g.win = es.g.win := by
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.corrEPaperBucket abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
    rcases revRes with _ | st
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; simp [GameState.afterCorr, GameState.leak]

theorem implEDFBucketRaw_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact transmitE_inv hk noDoomPolicy es (P, m, r) hInv
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact hInv.mono (Nat.le_succ q)
  · exact deliverE_inv hk cfg es (P, c) hInv
  · exact injectE_inv hk cfg es (P, c) hInv
  · change ∀ res ∈ support ((DeliverForge.corrEBucket hk P).run es), _
    rw [corrEBucket_eq_corrE]
    exact corrE_inv hk noDoomPolicy es P hInv
  · exact deliverForgeE_inv hk cfg es arg hInv

theorem implEDFPaperBucketRaw_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact transmitE_inv hk noDoomPolicy es (P, m, r) hInv
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact hInv.mono (Nat.le_succ q)
  · exact deliverE_inv hk cfg es (P, c) hInv
  · exact injectE_inv hk cfg es (P, c) hInv
  · change ∀ res ∈ support ((DeliverForge.corrEPaperBucket hk P).run es), _
    rw [corrEPaperBucket_eq_corrEPaper]
    exact corrEPaper_inv hk noDoomPolicy es P hInv
  · exact deliverForgeE_inv hk cfg es arg hInv

theorem implEDFBucketRaw_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact implE_vrInv hk hVRHk (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inl (.inl (.inl (.inl (P, m, r))))) hInv hVR
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) cfg noDoomPolicy es
      (.inl (.inl (.inr (P, c)))) hInv hVR
  · exact implE_vrInv hk hVRHk (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inl (.inr (P, c))) hInv hVR
  · change ∀ res ∈ support ((DeliverForge.corrEBucket hk P).run es), _
    rw [corrEBucket_eq_corrE]
    exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inr P) hInv hVR
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

theorem implEDFPaperBucketRaw_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact implE_vrInv hk hVRHk (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inl (.inl (.inl (.inl (P, m, r))))) hInv hVR
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) cfg noDoomPolicy es
      (.inl (.inl (.inr (P, c)))) hInv hVR
  · exact implE_vrInv hk hVRHk (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inl (.inr (P, c))) hInv hVR
  · change ∀ res ∈ support ((DeliverForge.corrEPaperBucket hk P).run es), _
    rw [corrEPaperBucket_eq_corrEPaper]
    exact implEDFPaper_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg noDoomPolicy es
      (.inl (.inr P)) hInv hVR
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

theorem implEDFBucketRaw_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((DeliverForge.implEDFBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact transmitE_b_eq hk noDoomPolicy es (P, m, r)
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · exact deliverE_b_eq hk cfg es (P, c)
  · exact injectE_b_eq hk cfg es (P, c)
  · change ∀ res ∈ support ((DeliverForge.corrEBucket hk P).run es), _
    rw [corrEBucket_eq_corrE]
    exact corrE_b_eq hk noDoomPolicy es P
  · exact deliverForgeE_b_eq hk cfg es arg

theorem implEDFPaperBucketRaw_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change ∀ res ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es), _
    rw [transmitEBucket_eq_transmitE]
    exact transmitE_b_eq hk noDoomPolicy es (P, m, r)
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · exact deliverE_b_eq hk cfg es (P, c)
  · exact injectE_b_eq hk cfg es (P, c)
  · change ∀ res ∈ support ((DeliverForge.corrEPaperBucket hk P).run es), _
    rw [corrEPaperBucket_eq_corrEPaper]
    exact corrEPaper_b_eq hk noDoomPolicy es P
  · exact deliverForgeE_b_eq hk cfg es arg

end BucketEngineLemmas

/-! ### Generic Bucket Handle / Finish / `simulateQ` Simulation -/

section GenericBucketHandle

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem eval_caseSum_inl {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = .inl v) :
    (Comp.caseSum e lb rb).eval ρ = lb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

private theorem eval_caseSum_inr {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : b.denote} (h : e.eval ρ = .inr v) :
    (Comp.caseSum e lb rb).eval ρ = rb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

private theorem eval_caseOpt_none {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a c : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} (h : e.eval ρ = none) :
    (Comp.caseOpt e nb sb).eval ρ = nb.eval ρ := by
  simp [Comp.eval, h]

private theorem eval_caseOpt_some {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a c : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = some v) :
    (Comp.caseOpt e nb sb).eval ρ = sb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

@[expose, reducible] def bucketHandleDFByCorrC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (corrAllowedFnE : ∀ {Γ'},
      Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
      Expr OO Γ' .bool → Expr OO Γ' .bool)
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))) :=
  rdsl do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw Δ) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC hkC (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))), (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw Δ) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))), (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC hkC L maxSkip cfgC es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC hkC L Δ qep cfgC es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(corrAllowedFnE s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← hkC.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC hkC L Δ qep cfgC es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))

abbrev bucketHandleDFC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :=
  bucketHandleDFByCorrC (fun s0 p0 => cCorrAllowedE L s0 p0) hkC L Δ qep maxSkip cfgC st q

abbrev bucketHandleDFPaperC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :=
  bucketHandleDFByCorrC (fun s0 p0 => cCorrAllowedPaperE L s0 p0) hkC L Δ qep maxSkip cfgC st q

def bucketFinishE
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (L Δ : ℕ) (tL : Option ℕ)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat))) :
    Comp OO I' Γ' .bool :=
  rdsl do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return ((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw Δ) (optNatLit (raw tL)) tWin (esG es0))

theorem bucketFinishE_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq M]
    (hsEncFn : HS → hsT.denote)
    (L Δ : ℕ) (tL : Option ℕ)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ)
    (hLeaks : es.g.leaks.length ≤ L) (hCorrs : es.g.corrs.length ≤ L)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp)) :
    (bucketFinishE (I' := I') L Δ tL st).eval ρ =
      pure (DeliverForge.authOutBucket Δ tL (es, winEp)) := by
  unfold bucketFinishE DeliverForge.authOutBucket authOut
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.snd st)).eval ρ = (esEnc vpTblEnc hsEncFn es, winEp) := by
    simp [Expr.eval, hst]
  rw [h0]; clear h0
  rw [eval_caseOpt]
  rcases winEp with _ | tWin
  · rfl
  · set ρ₂ := Env.cons (t := .nat) tWin
      (Env.cons
        (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))
        (esEnc vpTblEnc hsEncFn es, some tWin) ρ)
    change (Comp.ret _).eval ρ₂ = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval (vpEncFn := vpTblEnc) (O' := OO) L Δ
      (optNatLit tL) .v0 (esG (.fst .v1)) ρ₂ es.g hLeaks hCorrs rfl
    have htL : (optNatLit (O' := OO) tL).eval ρ₂ = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OO) (.fst .v1)).eval ρ₂ = es.abort := rfl
    have hW : (cGsWin (O' := OO) (esG (.fst .v1))).eval ρ₂ = es.g.win := rfl
    have hV0 : (Expr.v0 (O := OO)).eval ρ₂ = tWin := rfl
    simp only [Expr.eval, hAb, hW, hAuth, htL, hV0, Bool.and_assoc]

def bucketFinishPaperE
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (L Δ : ℕ) (tL : Option ℕ)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat))) :
    Comp OO I' Γ' .bool :=
  rdsl do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return (((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw Δ) (optNatLit (raw tL)) tWin (esG es0)) &&
        optNatEqE (cGsTL (esG es0)) (optNatLit (raw tL)))

theorem bucketFinishPaperE_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq M]
    (hsEncFn : HS → hsT.denote)
    (L Δ : ℕ) (tL : Option ℕ)
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ)
    (hLeaks : es.g.leaks.length ≤ L) (hCorrs : es.g.corrs.length ≤ L)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp)) :
    (bucketFinishPaperE (I' := I') L Δ tL st).eval ρ =
      pure (DeliverForge.authOutBucket Δ tL (es, winEp) && (es.g.tL == tL)) := by
  unfold bucketFinishPaperE DeliverForge.authOutBucket authOut
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.snd st)).eval ρ = (esEnc vpTblEnc hsEncFn es, winEp) := by
    simp [Expr.eval, hst]
  rw [h0]; clear h0
  rcases winEp with _ | tWin
  · rw [eval_caseOpt_none rfl]; rfl
  · rw [eval_caseOpt_some rfl]
    set ρ₂ := Env.cons (t := .nat) tWin
      (Env.cons
        (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))
        (esEnc vpTblEnc hsEncFn es, some tWin) ρ)
    change (Comp.ret _).eval ρ₂ = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval (vpEncFn := vpTblEnc) (O' := OO) L Δ
      (optNatLit tL) .v0 (esG (.fst .v1)) ρ₂ es.g hLeaks hCorrs rfl
    have htL : (optNatLit (O' := OO) tL).eval ρ₂ = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OO) (.fst .v1)).eval ρ₂ = es.abort := rfl
    have hW : (cGsWin (O' := OO) (esG (.fst .v1))).eval ρ₂ = es.g.win := rfl
    have hTL : (cGsTL (O' := OO) (esG (.fst .v1))).eval ρ₂ = es.g.tL := rfl
    have hV0 : (Expr.v0 (O := OO)).eval ρ₂ = tWin := rfl
    have hEqTL : (optNatEqE (O' := OO) (cGsTL (esG (.fst .v1))) (optNatLit tL)).eval ρ₂ =
        (es.g.tL == tL) := by
      simp [optNatEqE_eval, hTL, htL]
    simp only [Expr.eval, hAb, hW, hAuth, htL, hV0, hEqTL, Bool.and_assoc]

theorem rdecDF_bucketHandleDFByCorrC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    {L : ℕ}
    (corrAllowedFnE : ∀ {Γ'},
      Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
      Expr OO Γ' .bool → Expr OO Γ' .bool)
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (corrImpl : QueryImpl (Party →ₒ Option (PartyState Γ T RSt SS RS))
      (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS))
    (corrAllowedFn :
      GameState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) →
      Party → Bool)
    (hCorrAllowedE : ∀ {Γ'}
      (gE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (pE : Expr OO Γ' .bool) (ρ : Env Γ')
      (g : GameState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E))
      (P : Party),
      SMStateBoundedEngine L g → gE.eval ρ = cGsEnc vpTblEnc g → pE.eval ρ = partyEnc P →
      (corrAllowedFnE gE pE).eval ρ = corrAllowedFn g P)
    (hCorrImpl : ∀ P, corrImpl P = do
      let es ← get
      if es.abort || es.g.win || !(corrAllowedFn es.g P) then return none
      let s₁ := es.g.afterCorr P
      match ← liftH (hk.reveal es.g P (es.g.st P)) with
      | none =>
        abortE
        return none
      | some st =>
        modify fun es => { es with g := s₁ }
        return some st)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp))
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p =>
      ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (bucketHandleDFByCorrC corrAllowedFnE hkC L Δ qep maxSkip cfgC st qE).eval ρ) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (let i₀ : QueryImpl unifSpec
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) := coinsE
         let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) :=
            DeliverForge.transmitEBucket hk Δ qep
         let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) :=
            DeliverForge.challEBucket
         let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) :=
            deliverE hk maxSkip cfg
         let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) :=
            injectE hk Δ qep cfg
         let iDf : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M))
            (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS) :=
            deliverForgeE hk Δ qep cfg
         (DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1) (fun es => es.g.win)
          (HAdd.hAdd i₀
            (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) corrImpl) iDf)))
          (.inr q)).run (es, winEp) := by
  have hSelfNoFlip : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  unfold bucketHandleDFByCorrC DeliverForge.withWinEpDF
  dsimp only [StateT.run_mk]
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.pair (.snd st) qE)).eval ρ =
      (esEnc vpTblEnc hsEncFn es, winEp,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hst, hq]
  rw [h0]; clear h0
  rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · -- `.transmit`
    rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
      eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_bind_ret, eval_ite, orE_eval]
    change ((fun p => _) <$> (if (es.abort || es.g.win) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (do
          let (r_1, s') ← (DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es
          pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    unfold DeliverForge.transmitEBucket abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rw [eval_caseOpt, cEpMgmtE_eval vpTblEnc (O' := OO) Δ qep _ _ _ _ es.g P rfl rfl]
      have hR : ∀ {Γ''} (e : Expr OO Γ'' (.opt (.base CKASort.ccoins))) (ρ'' : Env Γ''),
          e.eval ρ'' = r → (isSomeE e).eval ρ'' = r.isSome := by
        intro Γ'' e ρ'' hr; unfold isSomeE; dsimp only [Expr.eval]; rw [hr]; cases r <;> rfl
      rw [hR _ _ rfl]; clear hR
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [Option.map_none, eval_ret, StateT.run_pure, pure_bind, map_pure,
          hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · simp only [Option.map_some]
        have hw1 : s₁.win = es.g.win := by
          unfold GameState.epMgmt at hep
          by_cases h1 : P.sendsIn (es.g.epoch P + 1)
          · by_cases h2 : qep < es.g.epoch P + 1
            · simp [h1, h2] at hep
            · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep
              by_cases h3 : (r.isSome && !(es.g.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
          · by_cases h2 : qep < es.g.epoch P
            · simp [h1, h2] at hep
            · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep; rfl
        rw [eval_bind, vSendC_eval hDefaultE hsEncFn HBounded hkC hk hHk
          _ _ _ _ _ _ _ _ es.h s₁ P (s₁.st P) m none r hHB
          rfl rfl rfl (by cases P <;> rfl) rfl rfl rfl]
        rw [bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', ct⟩
        · dsimp only [Option.map_none, Prod.map_apply, id_eq]
          rw [eval_caseOpt_none rfl]
          simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
          rfl
        · dsimp only [Option.map_some, Prod.map_apply, id_eq]
          rw [eval_caseOpt_some rfl]
          have hNoFlip : (!es.g.win &&
              (s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false).win) = false := by
            simp [GameState.record, hw1]
          simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
          rw [cRecordE_eval vpTblEnc (O' := OO) L Δ _ _ _ _ _ _ s₁ P st'
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
            rfl rfl rfl (by cases P <;> rfl)]
          rfl
  · -- `.chall`
    rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
      eval_caseSum_inl rfl, eval_caseSum_inr rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (DeliverForge.challEBucket (P, m₀, m₁, r)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    simp only [DeliverForge.challEBucket, eval_ret, StateT.run_pure, pure_bind, map_pure,
      hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
    rfl
  · -- `.deliver`
    rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
      eval_caseSum_inr rfl, eval_bind]
    rw [deliverEC_eval hsEncFn HBounded hkC hk hHk L maxSkip cfgC cfg hCfg heqT heqM heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (deliverE hk maxSkip cfg (P, c)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine OracleComp.bind_congr_of_forall_mem_support
      ((deliverE hk maxSkip cfg (P, c)).run es) fun ⟨out, es'⟩ hmem => ?_
    have hwinEq := deliverE_win_eq_of_deliverWin_false hk cfg hCfgWin es (P, c) (out, es') hmem
    have hNoFlip : (!es.g.win && es'.g.win) = false := by rw [hwinEq]; cases es.g.win <;> rfl
    rcases out with _ | (_ | m') <;>
      simp only [eval_ret, pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · -- `.inject`
    rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inr rfl, eval_bind]
    rw [injectEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (injectE hk Δ qep cfg (P, c)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then some c.1.1 else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply]; rfl)
  · -- `.corr`
    rw [eval_caseSum_inl rfl, eval_caseSum_inr rfl, eval_ite, orE_eval, orE_eval, not_eval,
      hCorrAllowedE _ _ _ es.g P hBound rfl rfl]
    change ((fun p => _) <$>
      (if (es.abort || (es.g.win || !corrAllowedFn es.g P)) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (do
          let (r_1, s') ← (corrImpl P).run es
          pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    rw [← Bool.or_assoc, hCorrImpl P]
    unfold abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !(corrAllowedFn es.g P))
    · simp only [href, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
      rw [hHk.reveal_eval _ _ _ _ _ es.h es.g P (es.g.st P) hHB rfl rfl rfl (by cases P <;> rfl),
        bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | stOut
      · dsimp only [Option.map_none, Prod.map_apply, id_eq]
        rw [eval_caseOpt_none rfl]
        simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · dsimp only [Option.map_some, Prod.map_apply, id_eq]
        rw [eval_caseOpt_some rfl]
        have hNoFlip : (!es.g.win && (es.g.afterCorr P).win) = false := by
          simp [GameState.afterCorr, GameState.leak]
        simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
        rw [cAfterCorrE_eval vpTblEnc (O' := OO) L _ _ _ es.g P
          hBound.trans_le hBound.comp_u rfl rfl]
        simp [Expr.eval, Expr.v0, Expr.v1, Expr.v4, esAbort, esEnc]
  · -- `.deliverForge`
    rw [eval_caseSum_inr rfl, eval_bind]
    rw [deliverForgeEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c c' hHB hBound (hVR P) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (deliverForgeE hk Δ qep cfg (P, c, c')).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then some c'.1.1 else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply]; rfl)

theorem rdecDF_bucketHandleDFC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop} (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) (.opt .nat)))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ) (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp))
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (bucketHandleDFC hkC L Δ qep maxSkip cfgC st qE).eval ρ) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (DeliverForge.implEDFBucket hk Δ qep maxSkip cfg (.inr q)).run (es, winEp) :=
  rdecDF_bucketHandleDFByCorrC_eval hDefaultE (fun s0 p0 => cCorrAllowedE L s0 p0)
    hkC hk (DeliverForge.corrEBucket hk) GameState.corrAllowed
    (fun gE pE ρ g P hB hg hp =>
      cCorrAllowedE_eval vpTblEnc L gE pE ρ g P hB.trans_le hB.chall_le hB.comp_le hg hp)
    (fun _ => rfl) hsEncFn HBounded hHk Δ qep maxSkip cfgC cfg hCfg hCfgWin
    heqT heqM heqE st qE ρ es winEp q hHB hBound hVR hst hq

theorem rdecDF_bucketHandleDFPaperC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop} (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    {Γ'} (st : Expr OO Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) (.opt .nat)))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ) (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp))
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (bucketHandleDFPaperC hkC L Δ qep maxSkip cfgC st qE).eval ρ) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (DeliverForge.implEDFPaperBucket hk Δ qep maxSkip cfg (.inr q)).run (es, winEp) :=
  rdecDF_bucketHandleDFByCorrC_eval hDefaultE (fun s0 p0 => cCorrAllowedPaperE L s0 p0)
    hkC hk (DeliverForge.corrEPaperBucket hk) GameState.corrAllowedPaper
    (fun gE pE ρ g P hB hg hp =>
      cCorrAllowedPaperE_eval vpTblEnc L gE pE ρ g P hB.chall_le hg hp)
    (fun _ => rfl) hsEncFn HBounded hHk Δ qep maxSkip cfgC cfg hCfg hCfgWin
    heqT heqM heqE st qE ρ es winEp q hHB hBound hVR hst hq

private theorem mem_support_withWinEpDF {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {St Msg Coins C S' : Type} (ctEpoch : C → ℕ) (hasWin : S' → Bool)
    (impl : QueryImpl (unifSpec + SM.specDF St Msg Coins C) (StateT S' (TComp TSpec)))
    (q : (unifSpec + SM.specDF St Msg Coins C).Domain)
    (s : S') (winEp : Option ℕ) (u : (unifSpec + SM.specDF St Msg Coins C).Range q)
    (s₁ : S') (winEp₁ : Option ℕ)
    (hmem : (u, (s₁, winEp₁)) ∈
      support ((DeliverForge.withWinEpDF ctEpoch hasWin impl q).run (s, winEp))) :
    (u, s₁) ∈ support ((impl q).run s) := by
  unfold DeliverForge.withWinEpDF at hmem
  dsimp only [StateT.run_mk] at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨r', s'⟩, hr, hp⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, _⟩
  exact hr

theorem simulateQ_withWinEpDF_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBoundedStep : ℕ → HS → Prop)
    (hHbMono : ∀ {m₁ m₂ : ℕ} {h : HS}, m₁ ≤ m₂ → HBoundedStep m₂ h → HBoundedStep m₁ h)
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B : ℕ) (hVRHk : HooksVRInv VROkStep hk)
    (handleComp : Comp OO I'
      [.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat),
       ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))))
    (rawImpl : QueryImpl
      (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (EM TSpec γvT.denote T svT.denote ssvT.denote rsvT.denote M E HS))
    (hRawInl : ∀ n, rawImpl (.inl n) = coinsE n)
    (hStepEval : ∀ {m : ℕ} es winEp t, HBoundedStep (m + 1) es.h → SMStateBoundedEngine L es.g →
      (∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B v) →
      ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
        handleComp.eval (.cons (esEnc vpTblEnc hsEncFn es, winEp)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        ((DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1) (fun es => es.g.win) rawImpl)
          (.inr t)).run (es, winEp))
    (hRawInv : ∀ {q : ℕ} es t, SMEngineInv L B (q + 1) es.g →
      ∀ res ∈ support ((rawImpl (.inr t)).run es), SMEngineInv L B q res.2.g)
    (hRawVrInv : ∀ {q : ℕ} es t, SMEngineInv L B (q + 1) es.g →
      SMVRInv VROkStep B (q + 1) es.g →
      ∀ res ∈ support ((rawImpl (.inr t)).run es), SMVRInv VROkStep B q res.2.g)
    (hRawBEq : ∀ es t, ∀ res ∈ support ((rawImpl (.inr t)).run es), res.2.g.b = es.g.b)
    (hHbStep : ∀ {m : ℕ} t es, HBoundedStep (m + 1) es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support ((rawImpl (.inr t)).run es), HBoundedStep m res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
        (winEp : Option ℕ),
        HBoundedStep qAdv es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp) oa).run
          (esEnc vpTblEnc hsEncFn es, winEp) =
          (Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
            (simulateQ
              (DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1)
                (fun es => es.g.win) rawImpl) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ
            (DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1)
              (fun es => es.g.win) rawImpl) oa).run (es, winEp)),
          HBoundedStep 0 res.2.1.h ∧ SMEngineInv L B 0 res.2.1.g ∧ res.2.1.g.b = es.g.b := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hHbMono (Nat.zero_le qAdv) hHB, hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inl n)).run (esEnc vpTblEnc hsEncFn es, winEp) =
          (fun u => (u, (esEnc vpTblEnc hsEncFn es, winEp))) <$>
            query (spec := unifSpec + TSpec) (.inl n) := by
        simp [handlerImpl, hU, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          ((DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1)
            (fun es => es.g.win) rawImpl) (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$> query (spec := unifSpec + TSpec) (.inl n) := by
        have hw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
        unfold DeliverForge.withWinEpDF
        dsimp only [StateT.run_mk]
        simp only [hRawInl n, coinsE, StateT.run_lift, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, hw, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B v :=
        fun P t₀ v hv => hVRHk.mono (Nat.sub_le B (m + 1)) (hVR P t₀ v hv)
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inr t)).run (esEnc vpTblEnc hsEncFn es, winEp) =
          Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
            ((DeliverForge.withWinEpDF (fun c : Header T × E => c.1.1)
              (fun es => es.g.win) rawImpl) (.inr t)).run (es, winEp) := by
        simp only [handlerImpl, StateT.run_mk,
          ← hStepEval es winEp t hHB hInv.toBoundedEngine hVRB,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hmemRaw := mem_support_withWinEpDF (fun c : Header T × E => c.1.1)
          (fun es => es.g.win) rawImpl (.inr t) es winEp u es₁ winEp₁ hmem
        exact (ih u (hqm u) es₁ winEp₁
          (hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmemRaw)
          (hRawInv es t hInv (u, es₁) hmemRaw)
          (hRawVrInv es t hInv hVR (u, es₁) hmemRaw)).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hmemRaw := mem_support_withWinEpDF (fun c : Header T × E => c.1.1)
          (fun es => es.g.win) rawImpl (.inr t) es winEp u es₁ winEp₁ hmem₁
        obtain ⟨hHB₂, hInv₂, hb₂⟩ := (ih u (hqm u) es₁ winEp₁
          (hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmemRaw)
          (hRawInv es t hInv (u, es₁) hmemRaw)
          (hRawVrInv es t hInv hVR (u, es₁) hmemRaw)).2 res hmem₂
        exact ⟨hHB₂, hInv₂, hb₂.trans (hRawBEq es t (u, es₁) hmemRaw)⟩

theorem simulateQ_implEDFBucket_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBoundedStep : ℕ → HS → Prop)
    (hHbMono : ∀ {m₁ m₂ : ℕ} {h : HS}, m₁ ≤ m₂ → HBoundedStep m₂ h → HBoundedStep m₁ h)
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B Δ qep maxSkip : ℕ)
    (hHk : ∀ {m : ℕ}, HooksCAgrees hsEncFn (HBoundedStep (m + 1))
      (HBoundedPost := HBoundedStep m) (VROk := VROkStep B) hkC hk)
    (hVRHk : HooksVRInv VROkStep hk)
    (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hHbStep : ∀ {m : ℕ} (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
      (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
      HBoundedStep (m + 1) es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support ((DeliverForge.implEDFBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
        HBoundedStep m res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
        (winEp : Option ℕ),
        HBoundedStep qAdv es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (bucketHandleDFC hkC L Δ qep maxSkip cfgC .v0 .v1)) oa).run
          (esEnc vpTblEnc hsEncFn es, winEp) =
          (Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
            (simulateQ (DeliverForge.implEDFBucket hk Δ qep maxSkip cfg) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFBucket hk Δ qep maxSkip cfg) oa).run
          (es, winEp)),
          HBoundedStep 0 res.2.1.h ∧ SMEngineInv L B 0 res.2.1.g ∧ res.2.1.g.b = es.g.b :=
  simulateQ_withWinEpDF_vr_eq hU hsEncFn HBoundedStep hHbMono hk L B hVRHk
    (bucketHandleDFC hkC L Δ qep maxSkip cfgC .v0 .v1)
    (DeliverForge.implEDFBucketRaw hk Δ qep maxSkip cfg)
    (fun _ => rfl)
    (fun es winEp t hHB hBnd hVRB =>
      rdecDF_bucketHandleDFC_eval hDefaultE hsEncFn _ hkC hk hHk L Δ qep maxSkip
        cfgC cfg hCfg hCfgWin heqT heqM heqE .v0 .v1 _ es winEp t hHB hBnd hVRB rfl rfl)
    (fun es t => implEDFBucketRaw_inv hk cfg es t)
    (fun es t => implEDFBucketRaw_vrInv hk hVRHk cfg es t)
    (fun es t => implEDFBucketRaw_b_eq hk cfg es t)
    hHbStep

theorem simulateQ_implEDFPaperBucket_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBoundedStep : ℕ → HS → Prop)
    (hHbMono : ∀ {m₁ m₂ : ℕ} {h : HS}, m₁ ≤ m₂ → HBoundedStep m₂ h → HBoundedStep m₁ h)
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B Δ qep maxSkip : ℕ)
    (hHk : ∀ {m : ℕ}, HooksCAgrees hsEncFn (HBoundedStep (m + 1))
      (HBoundedPost := HBoundedStep m) (VROk := VROkStep B) hkC hk)
    (hVRHk : HooksVRInv VROkStep hk)
    (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hHbStep : ∀ {m : ℕ} (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
      (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
      HBoundedStep (m + 1) es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
        HBoundedStep m res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
        (winEp : Option ℕ),
        HBoundedStep qAdv es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (bucketHandleDFPaperC hkC L Δ qep maxSkip cfgC .v0 .v1)) oa).run
          (esEnc vpTblEnc hsEncFn es, winEp) =
          (Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
            (simulateQ (DeliverForge.implEDFPaperBucket hk Δ qep maxSkip cfg) oa).run
              (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaperBucket hk Δ qep maxSkip cfg) oa).run
          (es, winEp)),
          HBoundedStep 0 res.2.1.h ∧ SMEngineInv L B 0 res.2.1.g ∧ res.2.1.g.b = es.g.b :=
  simulateQ_withWinEpDF_vr_eq hU hsEncFn HBoundedStep hHbMono hk L B hVRHk
    (bucketHandleDFPaperC hkC L Δ qep maxSkip cfgC .v0 .v1)
    (DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg)
    (fun _ => rfl)
    (fun es winEp t hHB hBnd hVRB =>
      rdecDF_bucketHandleDFPaperC_eval hDefaultE hsEncFn _ hkC hk hHk L Δ qep maxSkip
        cfgC cfg hCfg hCfgWin heqT heqM heqE .v0 .v1 _ es winEp t hHB hBnd hVRB rfl rfl)
    (fun es t => implEDFPaperBucketRaw_inv hk cfg es t)
    (fun es t => implEDFPaperBucketRaw_vrInv hk hVRHk cfg es t)
    (fun es t => implEDFPaperBucketRaw_b_eq hk cfg es t)
    hHbStep

end GenericBucketHandle

end

end CryptoGames.SM.Engine
