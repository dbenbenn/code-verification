/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Generic `Doom13U` and Policy Helpers for Stage-2 Switch-Back Lemma 13U (`SM/Theorem12.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Establishes `evalEng2`, `HasLeakAbove`, `Doom13U` preservation across all SM engine queries, and the
policy comparison lemmas between `polUni12 Δcka tStar` and `⟨false, tL, tStar⟩`.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.PrivL13U

open Engine PrivL14 CryptoGames.Lazy

section GenericDoom13U

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS : Type}
  {Γ T Sig SS RS M E CCoins : Type} {Γv Sv SSv RSv HS : Type}

@[expose] def evalEng2 [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π_eng π_out : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) : ProbComp Bool :=
  runEM oimpl (simulateQ (implE hk Δ qep maxSkip cfg π_eng) oa) s >>=
    fun r => privOutP Δ π_out b r.1 r.2.1

theorem evalEng2_pure [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π_eng π_out : Policy) (b b' : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng2 oimpl hk Δ qep maxSkip cfg π_eng π_out b (pure b') s = privOutP Δ π_out b b' s.1 := by
  simp [evalEng2, runEM_pure]

theorem evalEng2_query_bind [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {α : Type} (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π_eng π_out : Policy) (b : Bool)
    (q : OracleQuery (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (k : α → OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng2 oimpl hk Δ qep maxSkip cfg π_eng π_out b (liftM q >>= k) s =
      runEM oimpl (implE hk Δ qep maxSkip cfg π_eng q.input) s >>=
        fun r => evalEng2 oimpl hk Δ qep maxSkip cfg π_eng π_out b (k (q.cont r.1)) r.2 := by
  simp [evalEng2, simulateQ_bind, simulateQ_query, runEM_bind, bind_assoc]

@[expose] def HasLeakAbove {St Msg C : Type} (tL : Option ℕ) (tStar : ℕ)
    (g : SM.GameState St Msg C) : Prop :=
  ∃ l ∈ g.leaks, ltOpt tL l = true ∧ l < tStar

@[expose] def Doom13U {VPt M C HS : Type} (tL : Option ℕ) (tStar : ℕ)
    (es : EState VPt M C HS) : Prop :=
  Doom tL es ∨ HasLeakAbove tL tStar es.g

theorem canon_ne_of_hasLeakAbove {St Msg C : Type} {tL : Option ℕ} {tStar : ℕ}
    {g : SM.GameState St Msg C} (h : HasLeakAbove tL tStar g) :
    (canon tStar g == tL) = false := by
  rcases h with ⟨l, hl, hltOpt, hlt⟩
  have hmem : l ∈ g.leaks.filter (fun x => decide (x < tStar)) :=
    List.mem_filter.mpr ⟨hl, decide_eq_true hlt⟩
  rw [beq_eq_false_iff_ne]
  unfold canon
  cases tL with
  | none =>
    intro heq
    have hnil := List.max?_eq_none_iff.mp heq
    rw [hnil] at hmem
    contradiction
  | some l₀ =>
    have hl₀ : l₀ < l := by simpa [ltOpt] using hltOpt
    intro heq
    rcases PrivL13.list_le_max?_of_mem hmem with ⟨m, hm, hle⟩
    rw [heq] at hm
    injection hm with hm
    omega

theorem privOutP_of_doom13U [DecidableEq M] {VPt C HS : Type} (Δ : ℕ) (π : Policy)
    (b b' : Bool) (es : EState VPt M C HS) (hd : Doom13U π.tL π.tStar es) :
    privOutP Δ π b b' es = ($ᵗ Bool : ProbComp Bool) := by
  rcases hd with hd | hla
  · exact privOutP_of_doom Δ π b b' es hd
  · simp [privOutP, canon_ne_of_hasLeakAbove hla]

theorem HasLeakAbove.epMgmt {St Msg C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {g s₁ : SM.GameState St Msg C} {tL : Option ℕ} {tStar : ℕ}
    (hla : HasLeakAbove tL tStar g) (hep : g.epMgmt Δ qep P bad = some s₁) :
    HasLeakAbove tL tStar s₁ := by
  rcases hla with ⟨l, hl, h1, h2⟩
  refine ⟨l, ?_, h1, h2⟩
  unfold SM.GameState.epMgmt at hep
  split at hep
  · split at hep
    · contradiction
    · injection hep with hep; subst hep
      dsimp only
      split
      · exact List.mem_cons_of_mem _ hl
      · exact hl
  · split at hep
    · contradiction
    · injection hep with hep; subst hep
      exact hl

theorem HasLeakAbove.record {St Msg C : Type} {Δ : ℕ} {P : Party} {st' : St}
    {rec : Record Msg C} {ch : Bool} {g : SM.GameState St Msg C} {tL : Option ℕ} {tStar : ℕ}
    (hla : HasLeakAbove tL tStar g) :
    HasLeakAbove tL tStar (g.record Δ P st' rec ch) := by
  rcases hla with ⟨l, hl, h1, h2⟩
  exact ⟨l, hl, h1, h2⟩

theorem HasLeakAbove.accept {St Msg C : Type} {P : Party} {st' : St} {pos : Pos}
    {g : SM.GameState St Msg C} {tL : Option ℕ} {tStar : ℕ}
    (hla : HasLeakAbove tL tStar g) :
    HasLeakAbove tL tStar (g.accept P st' pos) := by
  rcases hla with ⟨l, hl, h1, h2⟩
  exact ⟨l, hl, h1, h2⟩

theorem HasLeakAbove.afterCorr {St Msg C : Type} {P : Party}
    {g : SM.GameState St Msg C} {tL : Option ℕ} {tStar : ℕ}
    (hla : HasLeakAbove tL tStar g) :
    HasLeakAbove tL tStar (g.afterCorr P) := by
  rcases hla with ⟨l, hl, h1, h2⟩
  exact ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩

theorem runEM_commitE_hla (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (old new : VP Γv T Sv SSv RSv) (pos : Pos)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    {tL : Option ℕ} {tStar : ℕ} (hla : HasLeakAbove tL tStar s.1.g)
    {r : Option (Ctx Γv T Sv SSv RSv M E) ×
      (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (commitE hk s.1.g P old new pos) s)) :
    (r.1 = none → r.2.1.abort = true) ∧
      (∀ s₁, r.1 = some s₁ → HasLeakAbove tL tStar s₁) := by
  unfold commitE at hr
  rw [runEM_bind, mem_support_bind_iff] at hr
  rcases hr with ⟨r₁, _, hr⟩
  cases hc : r₁.1 with
  | none =>
    rw [hc, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨fun _ => rfl, fun _ h => by contradiction⟩
  | some new' =>
    rw [hc, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨fun h => by contradiction, fun s₁ hs₁ => ?_⟩
    injection hs₁ with hs₁; subst hs₁
    rcases hla with ⟨l, hl, h1, h2⟩
    exact ⟨l, hl, h1, h2⟩

theorem Doom13U.runEM_implE [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (tL : Option ℕ) (tStar : ℕ)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom13U tL tStar s.1)
    {r : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q ×
      (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (implE hk Δ qep maxSkip cfg π q) s)) :
    Doom13U tL tStar r.2.1 := by
  rcases q with n | ⟨⟨⟨⟨⟨P, m, rcoins⟩ | ⟨P, m₀, m₁, rcoins⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩
  · change r ∈ support (runEM oimpl (coinsE n) s) at hr
    rw [runEM_coinsE, support_map] at hr
    rcases hr with ⟨_, -, rfl⟩
    exact hd
  · change r ∈ support (runEM oimpl (transmitE hk Δ qep π ⟨P, m, rcoins⟩) s) at hr
    unfold transmitE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    cases hcond : s.1.abort || s.1.g.win
    · rw [ite_bool_false hcond] at hr
      cases hep : s.1.g.epMgmt Δ qep P rcoins.isSome with
      | none =>
        rw [hep, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hd
      | some s₁ =>
        rw [hep] at hr; dsimp only at hr
        cases hld : π.leakDoom s.1.g s₁
        · rw [ite_bool_false hld, runEM_bind, mem_support_bind_iff] at hr
          rcases hr with ⟨r₁, _, hr⟩
          cases hvs : r₁.1 with
          | none =>
            rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl (Or.inl rfl)
          | some stc =>
            rcases stc with ⟨st', ct⟩
            rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr
            rcases hd with (hab | hm) | hla
            · simp [hab] at hcond
            · exact Or.inl (Or.inr (hm.epMgmt hep).record)
            · exact Or.inr (hla.epMgmt hep).record
        · rw [ite_bool_true hld, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inl (Or.inl rfl)
    · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hd
  · change r ∈ support (runEM oimpl (challE hk Δ qep cfg π ⟨P, m₀, m₁, rcoins⟩) s) at hr
    unfold challE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    cases hcond : s.1.abort || s.1.g.win
    · rw [ite_bool_false hcond] at hr
      cases hep : s.1.g.epMgmt Δ qep P rcoins.isSome with
      | none =>
        rw [hep, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hd
      | some s₁ =>
        rw [hep] at hr; dsimp only at hr
        cases hsc : !(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P))
        · rw [ite_bool_false hsc] at hr
          cases hld : π.leakDoom s.1.g s₁
          · rw [ite_bool_false hld, runEM_bind, mem_support_bind_iff] at hr
            rcases hr with ⟨r₁, _, hr⟩
            cases hvs : r₁.1 with
            | none =>
              rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inl (Or.inl rfl)
            | some stc =>
              rcases stc with ⟨st', ct⟩
              rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              rcases hd with (hab | hm) | hla
              · simp [hab] at hcond
              · exact Or.inl (Or.inr (hm.epMgmt hep).record)
              · exact Or.inr (hla.epMgmt hep).record
          · rw [ite_bool_true hld, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl (Or.inl rfl)
        · rw [ite_bool_true hsc, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hd
    · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hd
  · change r ∈ support (runEM oimpl (deliverE hk maxSkip cfg ⟨P, c⟩) s) at hr
    unfold deliverE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    cases hcond : s.1.abort || s.1.g.win
    · rw [ite_bool_false hcond] at hr
      cases hit : s.1.g.inTransit P.other c with
      | none =>
        rw [hit, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hd
      | some rec =>
        rw [hit] at hr; dsimp only at hr
        rw [runEM_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨r₁, hr₁, hr⟩
        have ⟨_, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
        cases hvr : r₁.1 with
        | none =>
          rw [hvr, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inl (Or.inl rfl)
        | some vr =>
          cases vr with
          | none =>
            rw [hvr] at hr; dsimp only at hr
            split at hr
            · rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              rcases hd with (hab | hm) | hla
              · simp [hab] at hcond
              · rcases hg₁ ▸ hm with ⟨l, htL, hA, hB, hmax, hnl⟩
                exact Or.inl (Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩)
              · rcases hg₁ ▸ hla with ⟨l, hl, h1, h2⟩
                exact Or.inr ⟨l, hl, h1, h2⟩
            · rw [runEM_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              rcases hd with (hab | hm) | hla
              · simp [hab] at hcond
              · exact Or.inl (Or.inr (hg₁ ▸ hm))
              · exact Or.inr (hg₁ ▸ hla)
          | some res =>
            rcases res with ⟨st', t', i', m'⟩
            rw [hvr] at hr; dsimp only at hr
            rw [runEM_bind, mem_support_bind_iff] at hr
            rcases hr with ⟨r₂, hr₂, hr⟩
            rcases hd with (hab | hm) | hla
            · simp [hab] at hcond
            · have ⟨hd₂, hacc₂⟩ := runEM_commitE_missed oimpl hk P (r₁.2.1.g.st P) st' rec.pos r₁.2
                (hg₁ ▸ hm) (hg₁ ▸ hr₂)
              cases hcm : r₂.1 with
              | none =>
                rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact Or.inl hd₂
              | some s₁ =>
                rw [hcm] at hr; dsimp only at hr
                rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                have hm₁ := hacc₂ s₁ hcm
                dsimp only; split
                · rcases hm₁ with ⟨l, htL, hA, hB, hmax, hnl⟩
                  exact Or.inl (Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩)
                · exact Or.inl (Or.inr hm₁)
            · have ⟨hab₂, hacc₂⟩ := runEM_commitE_hla oimpl hk P (r₁.2.1.g.st P) st' rec.pos r₁.2
                (hg₁ ▸ hla) (hg₁ ▸ hr₂)
              cases hcm : r₂.1 with
              | none =>
                rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact Or.inl (Or.inl (hab₂ hcm))
              | some s₁ =>
                rw [hcm] at hr; dsimp only at hr
                rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                have hla₁ := hacc₂ s₁ hcm
                dsimp only; split
                · rcases hla₁ with ⟨l, hl, h1, h2⟩
                  exact Or.inr ⟨l, hl, h1, h2⟩
                · exact Or.inr hla₁
    · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hd
  · change r ∈ support (runEM oimpl (injectE hk Δ qep cfg ⟨P, c⟩) s) at hr
    unfold injectE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    cases hcond :
        s.1.abort || s.1.g.win || (s.1.g.inTransit P.other c).isSome || !(s.1.g.safeInj Δ)
    · rw [ite_bool_false hcond, runEM_bind, mem_support_bind_iff] at hr
      rcases hr with ⟨r₁, hr₁, hr⟩
      have ⟨_, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
      cases hvr : r₁.1 with
      | none =>
        rw [hvr, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inl (Or.inl rfl)
      | some vr =>
        cases vr with
        | none =>
          rw [hvr, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          rcases hd with (hab | hm) | hla
          · simp [hab] at hcond
          · exact Or.inl (Or.inr (hg₁ ▸ hm))
          · exact Or.inr (hg₁ ▸ hla)
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          rw [hvr] at hr; dsimp only at hr
          by_cases hqep : qep + 1 < t'
          · simp [hqep, runEM_pure] at hr; subst hr
            rcases hd with (hab | hm) | hla
            · simp [hab] at hcond
            · exact Or.inl (Or.inr (hg₁ ▸ hm))
            · exact Or.inr (hg₁ ▸ hla)
          · simp only [hqep, ↓reduceIte] at hr
            cases htriv : s.1.g.trivial Δ ⟨P.other, t', i'⟩
            · rw [ite_bool_false htriv] at hr
              split at hr
              · rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                rcases hd with (hab | hm) | hla
                · simp [hab] at hcond
                · rcases hg₁ ▸ hm with ⟨l, htL, hA, hB, hmax, hnl⟩
                  exact Or.inl (Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩)
                · rcases hg₁ ▸ hla with ⟨l, hl, h1, h2⟩
                  exact Or.inr ⟨l, hl, h1, h2⟩
              · rw [runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                rcases hd with (hab | hm) | hla
                · simp [hab] at hcond
                · exact Or.inl (Or.inr (hg₁ ▸ hm))
                · exact Or.inr (hg₁ ▸ hla)
            · rw [ite_bool_true htriv, runEM_bind, mem_support_bind_iff] at hr
              rcases hr with ⟨r₂, hr₂, hr⟩
              rcases hd with (hab | hm) | hla
              · simp [hab] at hcond
              · have ⟨hd₂, hacc₂⟩ := runEM_commitE_missed oimpl hk P (r₁.2.1.g.st P) st'
                  ⟨P.other, t', i'⟩ r₁.2 (hg₁ ▸ hm) (hg₁ ▸ hr₂)
                cases hcm : r₂.1 with
                | none =>
                  rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inl hd₂
                | some s₁ =>
                  rw [hcm, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inl (Or.inr (hacc₂ s₁ hcm))
              · have ⟨hab₂, hacc₂⟩ := runEM_commitE_hla oimpl hk P (r₁.2.1.g.st P) st'
                  ⟨P.other, t', i'⟩ r₁.2 (hg₁ ▸ hla) (hg₁ ▸ hr₂)
                cases hcm : r₂.1 with
                | none =>
                  rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inl (Or.inl (hab₂ hcm))
                | some s₁ =>
                  rw [hcm, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inr (hacc₂ s₁ hcm)
    · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hd
  · change r ∈ support (runEM oimpl (corrE hk π P) s) at hr
    unfold corrE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    cases hcond : s.1.abort || s.1.g.win || !(s.1.g.corrAllowed P)
    · rw [ite_bool_false hcond] at hr
      cases hcd : π.leakDoom s.1.g (s.1.g.afterCorr P) || π.corrDoom s.1.g P
      · rw [ite_bool_false hcd, runEM_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨r₁, _, hr⟩
        cases hrev : r₁.1 with
        | none =>
          rw [hrev, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inl (Or.inl rfl)
        | some st =>
          rw [hrev, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          rcases hd with (hab | hm) | hla
          · simp [hab] at hcond
          · exact Or.inl (Or.inr hm.afterCorr)
          · exact Or.inr hla.afterCorr
      · rw [ite_bool_true hcd, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inl (Or.inl rfl)
    · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hd

theorem Doom13U.runEM_simulateQ [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {α : Type} (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (tL : Option ℕ) (tStar : ℕ)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom13U tL tStar s.1)
    {r : α × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s)) :
    Doom13U tL tStar r.2.1 := by
  induction oa using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp [runEM_pure] at hr; subst hr; exact hd
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, runEM_bind, mem_support_bind_iff] at hr
    rcases hr with ⟨r₁, hr₁, hr⟩
    exact ih r₁.1 r₁.2 (Doom13U.runEM_implE oimpl hk Δ qep maxSkip cfg π tL tStar q s hd hr₁) hr

theorem evalEng2_doom13U [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π_eng π_out : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom13U π_out.tL π_out.tStar s.1) :
    DEq (evalEng2 oimpl hk Δ qep maxSkip cfg π_eng π_out b oa s) ($ᵗ Bool : ProbComp Bool) := by
  unfold evalEng2
  refine (PrivL14.DEq.bind_right_supp _ fun r hr => ?_).trans (DEq.bind_const _ _)
  exact privOutP_of_doom13U Δ π_out b r.1 r.2.1
    (Doom13U.runEM_simulateQ oimpl hk Δ qep maxSkip cfg π_eng π_out.tL π_out.tStar oa s hd hr) ▸
      DEq.refl _

theorem evalEng2_sendCore_of_doom13U [DecidableEq M] [DecidableEq T] [DecidableEq E]
    [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π_eng π_out : Policy) (b : Bool)
    (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M)
    (pair : Option (M × M)) (rcoins : Option CCoins) (isChall : Bool)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : MissedTL π_out.tL s₁ ∨ HasLeakAbove π_out.tL π_out.tStar s₁) :
    DEq (runEM oimpl (sendCore hk Δ s₁ P m pair rcoins isChall) s >>=
          fun r => evalEng2 oimpl hk Δ qep maxSkip cfg π_eng π_out b (k r.1) r.2)
        ($ᵗ Bool : ProbComp Bool) := by
  refine (PrivL14.DEq.bind_right_supp _ fun r hr => ?_).trans (DEq.bind_const _ _)
  apply evalEng2_doom13U
  rcases hd with hm | hla
  · exact Or.inl (runEM_sendCore_doom oimpl hk Δ s₁ P m pair rcoins isChall s hm hr)
  · unfold sendCore at hr
    rw [runEM_bind, mem_support_bind_iff] at hr
    rcases hr with ⟨r₁, _, hr⟩
    cases hvs : r₁.1 with
    | none =>
      rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl (Or.inl rfl)
    | some stc =>
      rcases stc with ⟨st', c⟩
      rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inr hla.record

end GenericDoom13U

section PolicyLemmas

theorem corrDoom_polUni_eq {St Msg C : Type} (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (g : SM.GameState St Msg C) (P : Party) :
    (polUni12 Δcka tStar).corrDoom g P = Policy.corrDoom ⟨false, tL, tStar⟩ g P := rfl

theorem leakDoom_polUni_imp {St Msg C : Type} {Δcka : ℕ} {tL : Option ℕ} {tStar : ℕ}
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (g g' : SM.GameState St Msg C)
    (h : (polUni12 Δcka tStar).leakDoom g g' = true) :
    Policy.leakDoom ⟨false, tL, tStar⟩ g g' = true := by
  unfold polUni12 at h
  unfold Policy.leakDoom at h ⊢
  dsimp only at h ⊢
  rw [Bool.or_eq_true_iff]
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · left
    rw [List.any_eq_true] at h1 ⊢
    rcases h1 with ⟨l, hl, hlt⟩
    rcases Bool.and_eq_true_iff.mp hlt with ⟨hopt, hltS⟩
    refine ⟨l, hl, Bool.and_eq_true_iff.mpr ⟨?_, hltS⟩⟩
    by_cases hge : 2 + Δcka ≤ tStar
    · simp only [hge, ↓reduceIte, ltOpt, decide_eq_true_eq] at hopt
      rcases validGuess_healed hvg with rfl | ⟨l₀, rfl, hH, hle⟩
      · rfl
      · rw [hH] at hle
        exact decide_eq_true (by omega)
    · rcases validGuess_healed hvg with rfl | ⟨l₀, rfl, hH, hle⟩
      · rfl
      · rw [hH] at hle; omega
  · right; exact h2

theorem hasLeakAbove_of_leakDoom_diff {St Msg C : Type} {Δcka : ℕ} {tL : Option ℕ}
    {tStar : ℕ} (g g' : SM.GameState St Msg C)
    (hL : (polUni12 Δcka tStar).leakDoom g g' = false)
    (hR : Policy.leakDoom ⟨false, tL, tStar⟩ g g' = true) :
    HasLeakAbove tL tStar g' := by
  unfold polUni12 at hL
  unfold Policy.leakDoom at hL hR
  dsimp only at hL hR
  rcases Bool.or_eq_false_iff.mp hL with ⟨_, h2f⟩
  rw [h2f, Bool.or_false, List.any_eq_true] at hR
  rcases hR with ⟨l, hl, hand⟩
  rcases Bool.and_eq_true_iff.mp hand with ⟨hopt, hlt⟩
  exact ⟨l, hl, hopt, decide_eq_true_eq.mp hlt⟩

end PolicyLemmas

end CryptoGames.SM.Construction.PrivL13U
