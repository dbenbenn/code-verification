/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import VCVio.OracleComp.EvalDist.Measure

/-!
# `DeliverForgePaper` Lemma 9 and Stage-2 Bucket Game

**Checked by Lean.** Proves Lemma 9 (`lemma9_df_paper`), initial step lemmas of Lemma 10, and the
Stage-2 `(tL, par)` bucket game for `DeliverForge` under `corrAllowedPaper`.-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge.AuthL9DF

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL9

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
  (tL : Option ℕ) (tStar : ℕ)

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

@[expose] def runLDFPaper {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme (Config.auth tStar))
    oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + Δcka) tL tStar res.2)

@[expose] def runRDFPaper {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ
      (implEDFPaper (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩)
      oa).run es)).run sc) >>= fun res => pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ res.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDFPaper_pure {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFPaper cka prng fs lam Δcka qep tL tStar (pure a) s =
      pure (s.win && authLosingConditionsAvoided (2 + Δcka) tL tStar s) := by
  simp [runLDFPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFPaper_pure {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDFPaper cka prng fs Δcka qep tL tStar (pure a) es sc =
      pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ es) := by
  simp [runRDFPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDFPaper_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFPaper cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) s =
      (((fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        (Config.auth tStar)) t).run s >>=
        fun res => runLDFPaper cka prng fs lam Δcka qep tL tStar (k res.1) res.2) := by
  simp [runLDFPaper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFPaper_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDFPaper cka prng fs Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implEDFPaper (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩ t).run es)).run sc) >>=
        fun res => runRDFPaper cka prng fs Δcka qep tL tStar (k res.1.1) res.1.2 res.2) := by
  simp [runRDFPaper, StateT.run_bind]

omit [Inhabited E] in
theorem doomedAuth_simulateQ_DFPaper {Key St Msg Coins : Type}
    [DecidableEq Msg] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) {Δ : ℕ} (hΔ : 0 < Δ)
    {α : Type} (oa : AdversaryCompDF St Msg Coins (Header T × E) α) :
    ∀ {s s' : GameState St Msg (Header T × E)} {a : α},
      DoomedAuth tL tStar s →
      (a, s') ∈ support
        ((simulateQ (fullImplBaseDFPaper sm Δ qep sameHdrScheme (Config.auth tStar)) oa).run s) →
      DoomedAuth tL tStar s' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s s' a' hd hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff] at hmem
    rw [hmem.2]; exact hd
  | query_bind t k ih =>
    intro s s' a' hd hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨u, s₁⟩, h₁, h₂⟩
    rcases t with n | ((q14 | P) | qdf)
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inl n) hd h₁) h₂
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inr (.inl q14)) hd h₁) h₂
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, corrImplPaper] at h₁
      rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
      split_ifs at h₁ with hcond
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rw [← h₁.2] at hd; exact ih u hd h₂
      · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact ih u (h₁.2 ▸ doomedAuth_afterCorr P hd) h₂
    · exact ih u (doomedAuth_deliverForgeBaseImpl qep tL tStar sm hΔ qdf hd h₁) h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem evalDist_runLDFPaper_eq_pure_false_of_doomed
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuth tL tStar s) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hΔ : 0 < 2 + Δcka := by omega
  have hdoom' : DoomedAuth tL tStar s' :=
    doomedAuth_simulateQ_DFPaper qep tL tStar (scheme cka prng fs lam) hΔ oa hdoom hmem
  rw [doomedAuth_not_win (2 + Δcka) tL tStar s' hdoom']

omit [SampleableType CCoins] in
theorem abort_simulateQ_DFPaper {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDFPaper hk Δ qep maxSkip cfg π) oa).run es)).run sc) →
      es'.abort = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro es es' sc sc' a' hab hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff] at hmem
    rw [hmem.1.2]; exact hab
  | query_bind t k ih =>
    intro es es' sc sc' a' hab hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨⟨u, es₁⟩, sc₁⟩, h₁, h₂⟩
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · dsimp only [implEDFPaper, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implEDFPaper, transmitE, challE, deliverE, injectE, corrEPaper, deliverForgeE,
        HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem evalDist_runRDFPaper_eq_pure_false_of_abort
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T)
    (hab : es.abort = true) :
    𝒟[runRDFPaper cka prng fs Δcka qep tL tStar oa es sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ_DFPaper qep (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      (2 + Δcka) fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
      (CKA.oracleImpl cka Δcka (healEpoch tL)) oa hab hmem
  simp [authOut, hab']

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coins_DFPaper {α : Type} (n : unifSpec.Domain)
    (k : (ASpecDF).Range (Sum.inl n) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) (Sum.inl n) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inl n) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [implEDFPaper, fullImplBaseDFPaper]
  simp only [QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [liftTarget_ofLift_unifSpec_run, liftTarget_ofLift_unifSpec_run]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro u
  exact ih u hs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_DFPaper {α : Type} (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
          es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, challImpl, challE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
    cases r with
    | none =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt (2 + Δcka) qep P false <;> cases es.g.epMgmt (2 + Δcka) qep P false <;>
        simp [OracleComp.evalDist_bind_const, ih none hs]
    | some c =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, pure_bind]
      cases s.epMgmt (2 + Δcka) qep P true <;> cases es.g.epMgmt (2 + Δcka) qep P true <;>
        simp [ih none hs]

omit [SampleableType KR] [SampleableType K] in
theorem step_corr_DFPaper {α : Type} (P : Party)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inr P))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, corrImplPaper, corrEPaper]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hca : s.corrAllowedPaper P = es.g.corrAllowedPaper P := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.g.win || !es.g.corrAllowedPaper P) = true
  · simp [hguard, ih none hs]
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hwin_f : es.g.win = false := by
      cases hw : es.g.win
      · rfl
      · simp [hw] at hguard
    by_cases hd : ((Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) ||
        (Policy.mk true tL tStar).corrDoom es.g P) = true
    · simp only [hd, ↓reduceIte, abortE]
      have hdoom : DoomedAuth tL tStar (s.afterCorr P) := hs.doomed_of_corr_doom hwin_f hd
      have hL := evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
        (k (some (s.st P))) (s.afterCorr P) hdoom
      have hR := evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
        (k none) { es with abort := true } sc rfl
      exact hL.trans hR.symm
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hld : (Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) = false := by
        cases h : (Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P)
        · rfl
        · simp [h] at hd
      have hcd : (Policy.mk true tL tStar).corrDoom es.g P = false := by
        cases h : (Policy.mk true tL tStar).corrDoom es.g P
        · rfl
        · simp [h] at hd
      have hγ := hs.γ_eq P
      by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
      · simp only [hloc, ↓reduceIte] at hγ
        have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
            (es.g.st P).vR = s.st P := by
          rw [hs.s_eq]; rfl
        simp only [hooksCKA, hγ, pure_bind, hst_eq]
        exact ih (some (s.st P)) (hs.sync9_corr P)
      · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
        rcases htL : tL with _ | l
        · simp [isLocal, htL] at hloc
        · have hloc' : es.g.epoch P < l + 2 + Δcka := by
            simp [isLocal, htL] at hloc
            exact hloc
          have hall : sc.allowCorr (healEpoch (some l)) = true :=
            hs.allowCorr_of_corr htL hloc' hld hcd
          have hall' : sc.allowCorr (healEpoch tL) = true := by
            simpa [htL] using hall
          have hst_eq : realParty (es.g.st P) (sc.st P) (es.g.st P).root (es.g.st P).vS
              (es.g.st P).vR = s.st P := by
            rw [hs.s_eq]
            simp [realGS, realVP, realParty, hγ]
          simp only [hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery, StateT.run_bind,
            StateT.run_lift, simulateQ_bind, simulateQ_query_eq, QueryImpl.add_apply,
            CKA.oracleImpl, CKA.corrImpl, hall', Bool.true_or, ↓reduceIte, StateT.run_get,
            pure_bind, StateT.run_pure, simulateQ_pure, StateT.run_modify, StateT.run_set,
            bind_assoc, hst_eq, ← htL]
          exact ih (some (s.st P)) (hs.sync9_corr P)

theorem step_deliver_DFPaper {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, deliverImpl, deliverE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hch_eq : s.chall = es.g.chall := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
      obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv r hmem
      have hpos_c : r.pos.epoch = c.1.1 := by rw [← hct, ht_ep]
      have hnsend : P.sendsIn c.1.1 = false := by
        have h1 : P.other.sendsIn c.1.1 = true := by
          rw [← hpos_c, ← hsnd]
          exact hsnd_sends
        rw [sendsIn_other, Bool.not_eq_true'] at h1
        exact h1
      have hle_other : c.1.1 ≤ es.g.epoch P.other := by
        rw [← hpos_c, ← hsnd]
        exact hle_snd
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        have hle2 := hs.epoch_le P.other
        rw [Party.other_other] at hle2
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
          hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
        obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
        have hcT : c.1.2 = some T_t := by
          rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
        have hcache' : es.h.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_new_honest cka prng fs Δcka tL tStar (rec := some r) hs hnsend hstep hcT hcache' hI
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind]
        cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
        | none =>
          simp [ih (some .rejected) hs]
        | some val =>
          rcases val with ⟨v', i', m'⟩
          have hpos_ep : r.pos.epoch = es.g.epoch P + 1 := by omega
          have hnsend_pos : P.sendsIn r.pos.epoch = false := by rwa [hpos_c]
          have hcom := commitE_new cka prng fs Δcka tL tStar
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hs hpos_ep heq_other T_t hl_msg
          have hsync := hs.sync9_accept_new
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hpos_ep heq_other hnsend_pos T_t hagr
          dsimp only at hcom hsync
          rw [hpos_c] at hcom hsync
          simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
          exact ih _ hsync
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := some r) hs hnsend hle_P
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [ih (some .rejected) hs]
        | some v =>
          simp only []
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hpos_le : r.pos.epoch ≤ es.g.epoch P := by omega
            have hcom := commitE_same cka prng fs Δcka tL tStar
              (P := P)
              (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
              (pos := r.pos) (es := es) (sc := sc) rfl
            have hsync := hs.sync9_accept_same
              (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
            exact ih _ hsync

theorem step_inject_DFPaper {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, injectImpl, injectE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hsafe_eq : s.safeInj (2 + Δcka) = es.g.safeInj (2 + Δcka) := by rw [hs.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
    fun pos => by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hsafe_eq,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond :
      (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp [hcond, ih none hs]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hsafe : es.g.safeInj (2 + Δcka) = true := by
      cases h : es.g.safeInj (2 + Δcka)
      · simp [h] at hcond
      · rfl
    by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
    · obtain ⟨hrcvL, hrcvR⟩ :=
        vRecv_guard_true cka prng fs Δcka tL tStar (rec := none) hs hguard
      dsimp only [scheme]
      rw [hrcvL, StateT.run_bind, hrcvR]
      simp [ih (some .rejected) hs]
    · have hnsend : P.sendsIn c.1.1 = false := by
        cases h : P.sendsIn c.1.1
        · rfl
        · simp [h] at hguard
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        simp [hnsend] at hguard
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have htriv_f : ∀ i', es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false := by
          intro i'
          exact hs.trivial_false_of_safeInj (P := P) hsafe (by dsimp; omega)
        cases hc2 : c.1.2 with
        | none =>
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_new_none cka prng fs Δcka tL tStar (rec := none) hs hnsend hstep hc2
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
          simp [ih (some .rejected) hs]
        | some Tn =>
          by_cases hhon_ex : ∃ I_t, es.h.cache c.1.1 = some (Tn, I_t)
          · rcases hhon_ex with ⟨I_t, hcache'⟩
            have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
              by_contra hgt
              have hnone := hs.cache_gt c.1.1 (by omega)
              rw [hnone] at hcache'
              nomatch hcache'
            have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
              have hle2 := hs.epoch_le P.other
              rw [Party.other_other] at hle2
              cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
            obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.cka_step P heq_other
            rw [← heq_other, ← hstep, hcache'] at hcache_step
            injection hcache_step with hpair
            injection hpair with hT_eq hI_eq
            subst hT_eq hI_eq
            obtain ⟨hrcvL, hrcvR⟩ :=
              vRecv_new_honest cka prng fs Δcka tL tStar (rec := none)
                hs hnsend hstep hc2 hcache' hI
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
              by_cases hqep : qep + 1 < c.1.1
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, ↓reduceIte]
                by_cases hfull : (c.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]
          · have hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
              intro Tc Ik hc heq
              subst heq
              exact hhon_ex ⟨Ik, hc⟩
            by_cases htStar : c.1.1 = tStar
            · by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
              · obtain ⟨hrcvL, hrcvR⟩ :=
                  vRecv_new_dishonest_tStar_local cka prng fs Δcka tL tStar (rec := none)
                    hs hnsend hstep hc2 hhon htStar hloc
                dsimp only [scheme]
                rw [hrcvL, StateT.run_bind, hrcvR]
                simp only [pure_bind]
                cases hfs : fs.receive
                    (fs.initReceiver (prng.up (es.g.st P).root (cka.receive (s.st P).γ Tn).2).2)
                    c.1 c.2 with
                | none =>
                  simp [ih (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                  by_cases hqep : qep + 1 < c.1.1
                  · simp [hqep, ih (some .rejected) hs]
                  · have hfull : (c.1.1 == tStar) = true := beq_iff_eq.mpr htStar
                    simp only [hqep, ↓reduceIte, hfull, StateT.run_bind,
                      StateT.run_set, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure]
                    exact ih (some .rejected) (hs.sync9_win true)
              · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false :=
                  Bool.eq_false_iff.mpr hloc
                have hd4 : Doomed4 tL s := by
                  rcases hs.doomed4_or_local_of_safeInj_tStar (P := P) hsafe (by omega) with h | hd4
                  · exact False.elim (hloc h)
                  · exact hd4
                have hrcvR :=
                  vRecv_new_dishonest_tStar_nonlocal cka prng fs Δcka tL tStar (rec := none)
                    hs hnsend hstep hc2 hhon htStar hloc_f
                rw [StateT.run_bind, hrcvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom : DoomedAuth tL tStar s := Or.inr (Or.inr (Or.inr hd4))
                have hrun : 𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s hdoom
                rw [runLDFPaper_query_bind] at hrun
                dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
                  oracleImplPaper, injectImpl, Config.auth] at hrun
                simp only [hwin, hin_eq, hsafe_eq, StateT.run_bind, StateT.run_get, pure_bind,
                  hcond, Bool.false_eq_true, ↓reduceIte] at hrun
                exact hrun.trans hR.symm
            · have hrcvR :=
                vRecv_new_dishonest_ne cka prng fs Δcka tL tStar (rec := none)
                  hs hnsend hstep hc2 hhon htStar
              rw [StateT.run_bind, hrcvR]
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              dsimp only [scheme]
              cases hrcvL : receive cka prng fs (s.st P) c with
              | none =>
                simp [ih (some .rejected) hs]
              | some res =>
                rcases res with ⟨st', t', i', m'⟩
                have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL
                subst ht'
                have hfull : (c.1.1 == tStar) = false := beq_false_of_ne htStar
                simp only [htriv_eq, htriv_f, hfull, Bool.false_eq_true, ↓reduceIte]
                by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih (some .rejected) hs]
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := none) hs hnsend hle_P
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [ih (some .rejected) hs]
        | some v =>
          simp only []
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            simp only []
            by_cases hqep : qep + 1 < c.1.1
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
              · have hcom := commitE_same cka prng fs Δcka tL tStar
                  (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                have hsync := hs.sync9_accept_same
                  (Function.update (es.g.st P).vR c.1.1 (some v'))
                  (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]

theorem step_transmit_DFPaper {α : Type} (P : Party) (m : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper]
  by_cases hw : es.g.win = true
  · have hwin : s.win = true := by rw [hs.s_eq]; exact hw
    dsimp only [transmitImpl, transmitE]
    simp [hs.no_abort, hw, hwin, ih none hs]
  · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
    rw [transmitImpl_run_eq cka prng fs lam Δcka qep tL tStar hs hw_f]
    dsimp only [transmitE]
    simp only [hs.no_abort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
      exact ih none hs
    | some s₁ =>
      have hs₁_st : s₁.st = es.g.st := by
        unfold GameState.epMgmt at hep
        split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
      simp only []
      by_cases hld : (Policy.mk true tL tStar).leakDoom es.g s₁ = true
      · simp only [hld, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
            { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
          evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
            (k none) { es with abort := true } sc rfl
        rw [hR]
        refine evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
        have hdoom := hs.doomed_of_leakDoom_epMgmt hw_f hep hld
          (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
        exact evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
          (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
      · simp only [hld, Bool.false_eq_true, ↓reduceIte, hs₁_st]
        have hld_f : (Policy.mk true tL tStar).leakDoom es.g s₁ = false :=
          Bool.eq_false_iff.mpr hld
        by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
        · have hq : ¬qep < es.g.epoch P + 1 := by
            intro hq; simp [GameState.epMgmt, hsend, hq] at hep
          have hs₁_ep : s₁.epoch P = es.g.epoch P + 1 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hs₁_idx : s₁.idx P = 0 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hsend_eq := fun coins =>
            send_new_eq cka prng fs Δcka tL tStar (m := m) (coins := coins) hs hsend
          dsimp only at hsend_eq
          by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
          · have hvR := vSend_new_local cka prng fs Δcka tL tStar (m := m) (r := r) (s₁ := s₁)
              hs hsend hloc
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine evalDist_bind_congr _ _ _ fun coins => ?_
            rw [hsend_eq coins]
            exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
          · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false :=
              Bool.eq_false_iff.mpr hloc
            obtain ⟨l, htL⟩ : ∃ l, tL = some l := by
              cases h : tL
              · simp [isLocal, h] at hloc_f
              · exact ⟨_, rfl⟩
            have hloc' : es.g.epoch P < l + 2 + Δcka := by
              simpa [isLocal, htL] using hloc_f
            cases r with
            | none =>
              have hvR := vSend_new_nonlocal_none cka prng fs Δcka tL tStar
                (m := m) (s₁ := s₁) hs hsend hloc_f
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
              simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
              refine evalDist_bind_congr _ _ _ fun coins => ?_
              rw [hsend_eq coins]
              exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
            | some coins =>
              by_cases hle : es.g.epoch P + 1 ≤ l
              · have hvR := vSend_new_nonlocal_some_le cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hle
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [pure_bind, hs₁_ep, hs₁_idx]
                rw [hsend_eq coins]
                exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
              · have hgt : l < es.g.epoch P + 1 := by omega
                have hvR := vSend_new_nonlocal_some_gt cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hloc_f hgt
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom := hs.doomed4_of_sendBad_gt htL hloc' hsend hep hld_f hgt
                  (send cka prng fs (s.st P) m coins).1 m
                  (send cka prng fs (s.st P) m coins).2 false
                have hL : 𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
                    (k (some (send cka prng fs (s.st P) m coins).2))
                    ((realGS sc s₁).record (2 + Δcka) P (send cka prng fs (s.st P) m coins).1
                      ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m,
                        (send cka prng fs (s.st P) m coins).2⟩ false)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
                    (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
                exact hL.trans hR.symm
        · have hnsend : P.sendsIn (es.g.epoch P + 1) = false :=
            Bool.eq_false_iff.mpr hsend
          have hs₁_eq : s₁ = es.g := by
            unfold GameState.epMgmt at hep
            simp only [hnsend, Bool.false_eq_true, ↓reduceIte] at hep
            split_ifs at hep
            injection hep with hep
            exact hep.symm
          subst hs₁_eq
          obtain ⟨hsendL, hsendR⟩ :=
            vSend_same_epoch cka prng fs Δcka tL tStar (m := m) (r := r) hs hnsend
          have hreal_eq : realGS sc es.g = s := hs.s_eq.symm
          rw [StateT.run_bind, hsendR]
          simp only [hsendL, hreal_eq, pure_bind, OracleComp.evalDist_bind_const]
          exact ih _ (hs.sync9_send_same hnsend _ m _ false)

theorem step_deliverForge_DFPaper {α : Type} (P : Party) (c c' : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inr (P, c, c'))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, implEDFPaper,
    deliverForgeBaseImpl, deliverForgeE, sameHdrScheme, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hin'_eq : s.inTransit P.other c' = es.g.inTransit P.other c' := by rw [hs.s_eq]; rfl
  have hcomp_eq : ∀ pos, s.comp.contains pos = es.g.comp.contains pos :=
    fun pos => by rw [hs.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
    fun pos => by rw [hs.s_eq]; rfl
  have hbne : (!(c.1 == c'.1)) = (c.1 != c'.1) := rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hin'_eq, hcomp_eq, hbne,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      by_cases hguard :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos ||
            (c.1 != c'.1)) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        exact ih none hs
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hhdr : c'.1 = c.1 := by
          rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard) with ⟨_, h2⟩
          exact (bne_eq_false_iff_eq.mp h2).symm
        obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
        obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv r hmem
        have hpos_c : r.pos.epoch = c'.1.1 := by rw [hhdr, ← hct, ht_ep]
        have hnsend : P.sendsIn c'.1.1 = false := by
          have h1 : P.other.sendsIn c'.1.1 = true := by
            rw [← hpos_c, ← hsnd]
            exact hsnd_sends
          rw [sendsIn_other, Bool.not_eq_true'] at h1
          exact h1
        have hle_other : c'.1.1 ≤ es.g.epoch P.other := by
          rw [← hpos_c, ← hsnd]
          exact hle_snd
        have hle_P1 : c'.1.1 ≤ es.g.epoch P + 1 := by
          have hle2 := hs.epoch_le P.other
          rw [Party.other_other] at hle2
          omega
        by_cases hstep : c'.1.1 = es.g.epoch P + 1
        · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
            hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct, ← hhdr]; exact hstep)
          obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
          have hcT : c'.1.2 = some T_t := by
            rw [hhdr, ← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
          have hcache' : es.h.cache c'.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_new_honest cka prng fs Δcka tL tStar (rec := none) hs hnsend hstep hcT hcache' hI
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
          simp only [pure_bind]
          cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c'.1 c'.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
              rw [bne_eq_false_iff_eq, hpos_c]
            simp only [hne_ep, Bool.or_false]
            by_cases hqep : decide (qep + 1 < c'.1.1) = true
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
              · have hcom := commitE_new cka prng fs Δcka tL tStar
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hs hstep heq_other T_t hl_msg
                have hsync := hs.sync9_accept_new
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hstep heq_other hnsend T_t hagr
                dsimp only at hcom hsync
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c'.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]
        · have hle_P : c'.1.1 ≤ es.g.epoch P := by omega
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_same_epoch cka prng fs Δcka tL tStar (rec := none) hs hnsend hle_P
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
          simp only [pure_bind]
          cases hv : (es.g.st P).vR c'.1.1 with
          | none =>
            simp [ih (some .rejected) hs]
          | some v =>
            simp only []
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
                rw [bne_eq_false_iff_eq, hpos_c]
              simp only [hne_ep, Bool.or_false]
              by_cases hqep : decide (qep + 1 < c'.1.1) = true
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
                by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
                · have hcom := commitE_same cka prng fs Δcka tL tStar
                    (P := P)
                    (new :=
                      { es.g.st P with vR := Function.update (es.g.st P).vR c'.1.1 (some v') })
                    (pos := ⟨P.other, c'.1.1, i'⟩) (es := es) (sc := sc) rfl
                  have hsync := hs.sync9_accept_same
                    (Function.update (es.g.st P).vR c'.1.1 (some v'))
                    (pos := ⟨P.other, c'.1.1, i'⟩) hle_P
                  simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                    StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                    simulateQ_pure]
                  exact ih _ hsync
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                  by_cases hfull : (c'.1.1 == tStar) = true
                  · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                      StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                    exact ih (some .rejected) (hs.sync9_win true)
                  · simp [hfull, ih (some .rejected) hs]

theorem runLDFPaper_eq_runRDFPaper_of_sync {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar oa es sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc with
  | pure a =>
    rw [runLDFPaper_pure, runRDFPaper_pure]
    have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
    have hok : authLosingConditionsAvoided (2 + Δcka) tL tStar s = authLosingConditionsAvoided (2 + Δcka) tL tStar es.g := by
      rw [hs.s_eq]; rfl
    simp [authOut, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins_DFPaper cka prng fs lam Δcka qep tL tStar n k hs @ih
    · exact step_transmit_DFPaper cka prng fs lam Δcka qep tL tStar P m r k hs @ih
    · exact step_chall_DFPaper cka prng fs lam Δcka qep tL tStar P m₀ m₁ r k hs @ih
    · exact step_deliver_DFPaper cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_inject_DFPaper cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_corr_DFPaper cka prng fs lam Δcka qep tL tStar P k hs @ih
    · exact step_deliverForge_DFPaper cka prng fs lam Δcka qep tL tStar P c c' k hs @ih

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem forgeGameGuessedPaper_eq_runLDFPaper (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameGuessedPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLDFPaper cka prng fs lam Δcka qep tL t A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold forgeGameGuessedPaper runBaseDFPaper runLDFPaper
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

/-- Bounds `forgeGuessedAdvantagePaper` at `(tL, t)` by the real-world CKA branch of
`redCKAAuthDFPaper`. -/
theorem lemma9_df_paper (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · apply le_of_eq
    unfold forgeGuessedAdvantagePaper
    rw [forgeGameGuessedPaper_eq_runLDFPaper]
    congr 1
    cases htL : tL with
    | none =>
      subst htL
      unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      symm
      refine (evalDist_bind_congr ($ᵗ KC) _
        (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runLDFPaper cka prng fs lam Δcka qep none t A
            (initState (scheme cka prng fs lam) (kr, kc) false)) ?_).trans ?_
      · intro kc_ext
        refine evalDist_bind_congr _ _ _ fun kr => ?_
        refine evalDist_bind_congr _ _ _ fun kc => ?_
        symm
        refine (runLDFPaper_eq_runRDFPaper_of_sync cka prng fs lam Δcka qep none t A
          (sync9_init_none cka prng fs lam Δcka t hc hvg kr kc kc_ext)).trans ?_
        simp only [runRDFPaper, bind_pure_comp, map_pure]
        rfl
      · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
    | some l =>
      subst htL
      unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      refine (runLDFPaper_eq_runRDFPaper_of_sync cka prng fs lam Δcka qep (some l) t A
        (Sync9.sync9_init prng fs lam hc hvg kr kc)).trans ?_
      simp only [runRDFPaper, bind_pure_comp, map_pure]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero :
        forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A =
          0 := by
      unfold forgeGuessedAdvantagePaper forgeGameGuessedPaper
      simp only []
      refine evalDist_true_eq_zero_of_support _ _ fun res _ => ?_
      simp [authLosingConditionsAvoided, hvg_f]
    rw [hzero]
    exact zero_le

end CryptoGames.SM.Construction.DeliverForge.AuthL9DF

namespace CryptoGames.SM.Construction.DeliverForge.AuthL10DF

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL10

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

@[expose] def stepCDFPaper (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T) :=
  (simulateQ (cImpl cka Δcka mo.tH)
    ((implEDFPaper (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esC)).run sc

@[expose] def stepPDFPaper (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

@[expose] def runLDFPaper (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) : ProbComp Bool := do
  let r ← (simulateQ (cImpl cka Δcka mo.tH)
    ((simulateQ
      (implEDFPaper (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esC)).run sc
  pure (authOut (2 + Δcka) mo.policy r.1.2)

@[expose] def runRDFPaper (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ
      (implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDFPaper_pure (mo : Mode) (b' : Bool) (esC : EStateC Γ T Sig SS RS M E I)
    (sc : CKA.GameState Γ T) :
    runLDFPaper cka prng fs Δcka qep mo (pure b') esC sc =
      pure (authOut (2 + Δcka) mo.policy esC) := by
  simp [runLDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFPaper_pure (mo : Mode) (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runRDFPaper cka prng fs Δcka qep mo (pure b') esP sp =
      pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runRDFPaper, map_eq_bind_pure_comp]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDFPaper_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    runLDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esC sc =
      stepCDFPaper cka prng fs Δcka qep mo q esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runLDFPaper, stepCDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFPaper_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runRDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDFPaper cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runRDFPaper, stepPDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDFPaper_coins (mo : Mode) (n : unifSpec.Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDFPaper cka prng fs Δcka qep mo (.inl n) esC sc =
      stepC cka prng fs Δcka qep mo (.inl n) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDFPaper_coins (mo : Mode) (n : unifSpec.Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDFPaper cka prng fs Δcka qep mo (.inl n) esP sp =
      stepP cka prng fs Δcka qep mo (.inl n) esP sp := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDFPaper_deliverForge (mo : Mode)
    (df : Party × (Header T × E) × (Header T × E))
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDFPaper cka prng fs Δcka qep mo (.inr (.inr df)) esC sc =
      stepCDF cka prng fs Δcka qep mo (.inr (.inr df)) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDFPaper_deliverForge (mo : Mode)
    (df : Party × (Header T × E) × (Header T × E))
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDFPaper cka prng fs Δcka qep mo (.inr (.inr df)) esP sp =
      stepPDF cka prng fs Δcka qep mo (.inr (.inr df)) esP sp := rfl

theorem stepCDFPaper_abort (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) (hab : esC.abort = true) :
    ∀ r ∈ support (stepCDFPaper cka prng fs Δcka qep mo q esC sc), r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((q14 | P) | ⟨P, c, c'⟩)
  · exact stepC_abort cka prng fs Δcka qep mo (.inl n) esC sc hab r hr
  · exact stepC_abort cka prng fs Δcka qep mo (.inr (.inl q14)) esC sc hab r hr
  · simp only [stepCDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
      StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · exact stepCDF_abort cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc hab r hr

theorem runLDFPaper_abort (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true) :
    𝒟[runLDFPaper cka prng fs Δcka qep mo oa esC sc] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing esC sc with
  | pure b' =>
    rw [runLDFPaper_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runLDFPaper_query_bind]
    exact evalDist_bind_false_of_support _ _ fun r hr =>
      ih r.1.1 (stepCDFPaper_abort cka prng fs Δcka qep mo q esC sc hab r hr)

theorem runLDFPaper_abort_apply_true_le (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runLDFPaper cka prng fs Δcka qep mo oa esC sc] {true} ≤ rhs := by
  rw [runLDFPaper_abort cka prng fs Δcka qep mo oa hab]
  simp

theorem step_coinsE_DFPaper_le (mo : Mode) (n : unifSpec.Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range (.inl n) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inl n) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inl n) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_coinsE, stepP_coinsE, bind_map_left, bind_map_left]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u hS

theorem step_challE_DFPaper_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_challE cka prng fs Δcka qep mo hauth, stepP_challE cka prng fs Δcka qep mo hauth,
    pure_bind, pure_bind]
  exact ih none hS

theorem step_corrE_DFPaper_le (mo : Mode) (hauth : mo.auth = true) (P : Party)
    (k : Option (PartyState Γ T Sig SS RS) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hca : esP.g.corrAllowedPaper P = esC.g.corrAllowedPaper P :=
    AuthL11.eraseSt_corrAllowedPaper hS.g_eq P
  by_cases hguard : esC.g.win || !esC.g.corrAllowedPaper P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC :
        stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
          pure ((none, esC), sc) := by
      simp [stepCDFPaper, implEDFPaper, corrEPaper, hS.abort_C, hguard, StateT.run_pure]
    have hP :
        stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp =
          pure ((none, esP), sp) := by
      simp [stepPDFPaper, implEDFPaper, corrEPaper, hS.abort_P, hwin, hca, hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hld : mo.policy.leakDoom esP.g (esP.g.afterCorr P) =
        mo.policy.leakDoom esC.g (esC.g.afterCorr P) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_afterCorr hS.g_eq P) mo.policy
    have hcd : mo.policy.corrDoom esP.g P = mo.policy.corrDoom esC.g P :=
      eraseSt_corrDoom hS.g_eq mo.policy P
    by_cases hdoom : mo.policy.leakDoom esC.g (esC.g.afterCorr P) || mo.policy.corrDoom esC.g P
    · simp only [Bool.or_eq_true] at hdoom
      have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
          pure ((none, { esC with abort := true }), sc) := by
        simp [stepCDFPaper, implEDFPaper, corrEPaper, abortE, hS.abort_C, hguard, hdoom,
          StateT.run_modify]
      rw [hC, pure_bind]
      exact runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hdoom
      have hkr : knownRoot mo (esC.g.epoch P) = true :=
        knownRoot_of_not_doom mo hauth esC.g P hdoom.1 hdoom.2
      have hrootP : (esP.g.st P).root = some (esC.g.st P).root := by
        rw [hS.root_P P, hkr]
        rfl
      have hP : stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp =
          pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR), { esP with g := esP.g.afterCorr P }), sp) := by
        simp [stepPDFPaper, implEDFPaper, corrEPaper, hooksPRNG, hS.abort_P, hwin, hca, hguard,
          hld, hcd, hdoom.1, hdoom.2, hrootP, StateT.run_modify, hS.realParty_eq P]
      by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
      · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
          rw [hS.γ_C P, hloc]
          rfl
        have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
            pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
              (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
          simp [stepCDFPaper, implEDFPaper, corrEPaper, hooksCKA, hS.abort_C, hguard, hdoom.1,
            hdoom.2, hγC, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih _ (hS.afterCorr P)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esC.g.st P).γ = none := by
          rw [hS.γ_C P, hloc]
          rfl
        have hcka := (hS.cka_st P (Or.inl hloc)).1
        by_cases hcorr : sc.allowCorr mo.tH || sc.finished Δcka mo.tH P
        · simp only [Bool.or_eq_true] at hcorr
          have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
              pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
                (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
            simp [stepCDFPaper, implEDFPaper, corrEPaper, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, hcka, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih _ (hS.afterCorr P)
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
          have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
              pure ((none, { esC with abort := true }), sc) := by
            simp [stepCDFPaper, implEDFPaper, corrEPaper, abortE, hooksCKA, liftC, CKA.corrQuery,
              cImpl, CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, pure_bind]
          exact runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _

end CryptoGames.SM.Construction.DeliverForge.AuthL10DF

/-! ## Stage-2 bucket game under `corrAllowedPaper` -/

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine

section BucketGamePaper

variable {Key St Msg Coins : Type} {T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]

@[expose] def fullImplBaseDFPaperBucket (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Coins] (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool) :
    QueryImpl (unifSpec + specDF St Msg Coins (Header T × E))
      (StateT (GameState St Msg (Header T × E) × Option ℕ) ProbComp) :=
  withWinEpDF (fun c => c.1.1) GameState.win
    (fullImplBaseDFPaper sm (2 + Δcka) qep sameHdr (bucketAuthCfg Δcka tL par))

/-- Single-win Stage-2 `(tL, par)` bucket authenticity game under `corrAllowedPaper`. -/
@[expose] def forgeGameBucketPaper (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, (s, winEp)) ←
    (simulateQ (fullImplBaseDFPaperBucket sm Δcka qep sameHdr tL par) B).run
      (initState sm k false, none)
  return match winEp with
    | none => false
    | some tWin => s.win && authLosingConditionsAvoided (2 + Δcka) tL tWin s

@[expose] noncomputable def forgeBucketAdvantagePaper (sm : SMScheme Key St Msg Coins (Header T × E))
    (Δcka qep : ℕ) [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ℝ≥0∞ :=
  𝒟[forgeGameBucketPaper sm Δcka qep sameHdr tL par B] {true}

end BucketGamePaper

section BucketEnginePaper

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]

/-- Bucket engine `corr` oracle under `corrAllowedPaper` (no target-specific doom check). -/
@[expose] def corrEPaperBucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) :
    QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun P => do
  let es ← get
  if es.abort || es.g.win || !(es.g.corrAllowedPaper P) then return none
  let s₁ := es.g.afterCorr P
  match ← liftH (hk.reveal es.g P (es.g.st P)) with
  | none =>
    abortE
    return none
  | some st =>
    modify fun es => { es with g := s₁ }
    return some st

/-- Underlying 6-oracle `DeliverForgePaper` bucket engine implementation on `EState` (before
`withWinEpDF`). -/
@[expose] def implEDFPaperBucketRaw {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) := transmitEBucket hk Δ qep
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) := challEBucket
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := deliverE hk maxSkip cfg
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := injectE hk Δ qep cfg
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (EM tspec Γv T Sv SSv RSv M E HS) := corrEPaperBucket hk
  let iSpec : QueryImpl (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅
  let iDf : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    deliverForgeE hk Δ qep cfg
  HAdd.hAdd i₀ (HAdd.hAdd iSpec iDf)

/-- Extended 6-oracle `DeliverForgePaper` bucket engine implementation on `EState × Option ℕ`. -/
@[expose] def implEDFPaperBucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × Option ℕ) (TComp tspec)) :=
  withWinEpDF (fun c => c.1.1) (fun es => es.g.win) (implEDFPaperBucketRaw hk Δ qep maxSkip cfg)

/-- Run an extended `AdversaryDF` in the paper bucket engine (`implEDFPaperBucket`). -/
@[expose] def engRunDFPaperBucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (b : Bool) (A : AdversaryDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) :
    TComp tspec (Option (Bool × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × Option ℕ))) := do
  let (vs, h) ← init.run h₀
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx Γv T Sv SSv RSv M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := b }
    let res ←
      (simulateQ (implEDFPaperBucket hk Δ qep maxSkip cfg) A).run ({ g := g, h := h }, none)
    return some res

/-- Paper bucket authenticity outcome: `authOutBucket Δ tL st`. -/
@[expose] def authOutBucketPaper {VPt Msg C HS : Type} [DecidableEq Msg] [DecidableEq C]
    (Δ : ℕ) (tL : Option ℕ) (st : EState VPt Msg C HS × Option ℕ) : Bool :=
  authOutBucket Δ tL st

/-- Stage-2 `(tL, par)` bucket CKA authenticity reduction `B_cka_u` under `corrAllowedPaper`. -/
@[expose] def redCKAAuthDFPaperBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  let r ← engRunDFPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
    (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
    (initCKA cka prng fs lam ⟨true, tL, 0⟩) {} false A
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st

section BucketProofPaper

set_option linter.unusedSectionVars false

open CryptoGames.SM.Construction.AuthL9

local notation "ASpecDFB" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

private def bucketTStar (Δcka : ℕ) (tL : Option ℕ) : ℕ :=
  match tL with
  | none => 0
  | some l => l + 3 + Δcka

private theorem bucketTStar_admissible (Δcka : ℕ) (tL : Option ℕ) :
    lastLeakGuessAdmissible (2 + Δcka) tL (bucketTStar Δcka tL) = true := by
  cases tL with
  | none => rfl
  | some l =>
    dsimp only [bucketTStar]
    simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq]
    omega

private theorem inStage2Bucket_admissible {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {t : ℕ}
    (hb : inStage2Bucket Δcka tL par t = true) :
    lastLeakGuessAdmissible (2 + Δcka) tL t = true := by
  unfold inStage2Bucket at hb
  rw [Bool.and_eq_true] at hb
  cases tL with
  | none => rfl
  | some l =>
    simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hb ⊢
    omega

private theorem inStage2Bucket_isLocal {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {ep : ℕ}
    (hb : inStage2Bucket Δcka tL par (ep + 1) = true) :
    isLocal tL Δcka ep = true := by
  unfold inStage2Bucket at hb
  rw [Bool.and_eq_true] at hb
  cases tL with
  | none => rfl
  | some l =>
    simp only [lastLeakGuessAdmissible, healedBy, isLocal, decide_eq_true_eq] at hb ⊢
    omega

private theorem vSend_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (tStar : ℕ) :
    vSend (hooksCKABucket cka prng fs Δcka tL par) =
      vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩) := rfl

private theorem commitE_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (tStar : ℕ) :
    commitE (hooksCKABucket cka prng fs Δcka tL par) =
      commitE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩) := rfl

private theorem initCKA_zero_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (tL : Option ℕ) (tStar : ℕ) :
    initCKA cka prng fs lam ⟨true, tL, 0⟩ = initCKA cka prng fs lam ⟨true, tL, tStar⟩ := rfl

private theorem startRecv_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : Sig) (Tn : T) :
    (hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P t γv σ Tn =
      (hooksCKA cka prng fs Δcka
        ⟨true, tL, if inStage2Bucket Δcka tL par t then t else t + 1⟩).startRecv
        ctx P t γv σ Tn := by
  ext h
  simp only [hooksCKABucket, hooksCKA, StateT.run_bind, StateT.run_get, pure_bind]
  cases h.cache t with
  | none =>
    cases hb : inStage2Bucket Δcka tL par t
    · simp
    · simp; rfl
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    by_cases hTc : Tc = Tn
    · simp [hTc]
    · cases hb : inStage2Bucket Δcka tL par t
      · simp [hTc]
      · simp [hTc]; rfl

private theorem vRecv_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (vp : PartyState (Option Γ) T Sig SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E))) :
    vRecv (hooksCKABucket cka prng fs Δcka tL par) ctx P vp c rec =
      vRecv (hooksCKA cka prng fs Δcka
        ⟨true, tL, if inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1⟩)
        ctx P vp c rec := by
  unfold vRecv
  by_cases h1 : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : c.1.1 = vp.tcur + 1
    · simp only [h2, ↓reduceIte, startRecv_hooksCKABucket_eq]
      rfl
    · simp only [h2, ↓reduceIte]
      rfl

private def Doomed14 {St : Type} (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (s : GameState St M (Header T × E)) : Prop :=
  ∀ tWin, inStage2Bucket Δcka tL par tWin = true → Doomed1 tL tWin s ∨ Doomed4 tL s

private def DoomedBucket {St : Type} (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (sw : GameState St M (Header T × E) × Option ℕ) : Prop :=
  Doomed14 Δcka tL par sw.1 ∧
    (sw.1.win = true → ∃ tWin, sw.2 = some tWin ∧ inStage2Bucket Δcka tL par tWin = true)

private theorem doomed14_mono {St : Type} {Δcka : ℕ} {tL : Option ℕ} {par : Bool}
    {s s' : GameState St M (Header T × E)} (hd : Doomed14 Δcka tL par s)
    (hep : ∀ P, s.epoch P ≤ s'.epoch P)
    (hsub : ∀ x ∈ s.leaks, x ∈ s'.leaks)
    (hnew : ∀ x ∈ s'.leaks, x ∈ s.leaks ∨ min (s.epoch .A) (s.epoch .B) < x ∨
      max (s.epoch .A) (s.epoch .B) ≤ x) :
    Doomed14 Δcka tL par s' := by
  intro tWin hb
  rcases hd tWin hb with h1 | ⟨l, htL, hnl, hmin, hmax⟩
  · exact Or.inl (@doomed1_of_leaks_sub St M (Header T × E) _ _ tL tWin s s' h1 hsub)
  · right
    have hA := hep .A
    have hB := hep .B
    refine ⟨l, htL, ?_, by omega, by omega⟩
    intro hmem
    rcases hnew l hmem with hmem0 | hgt | hge
    · exact hnl hmem0
    · omega
    · omega

private theorem doomed14_epMgmt {St : Type} {Δ qep Δcka : ℕ} {tL : Option ℕ} {par : Bool}
    {s s₁ : GameState St M (Header T × E)} {P : Party} {bad : Bool}
    (hd : Doomed14 Δcka tL par s) (hep : s.epMgmt Δ qep P bad = some s₁) :
    Doomed14 Δcka tL par s₁ ∧ s₁.win = s.win := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hq1 hb hq2
  · injection hep with hep; subst hep
    refine ⟨doomed14_mono hd (fun Q => update_epoch_ge s.epoch P Q (s.epoch P + 1) (by omega))
      (fun x hx => by simp [GameState.leak, hx]) fun x hx => ?_, rfl⟩
    simp only [GameState.leak, List.mem_cons] at hx
    rcases hx with rfl | hx
    · right; left
      have := le_maxOpt_right s.tL (s.epoch P + 1)
      cases P <;> simp <;> omega
    · exact Or.inl hx
  · injection hep with hep; subst hep
    exact ⟨doomed14_mono hd (fun Q => update_epoch_ge s.epoch P Q (s.epoch P + 1) (by omega))
      (fun _ hx => hx) (fun _ hx => Or.inl hx), rfl⟩
  · injection hep with hep; subst hep; exact ⟨hd, rfl⟩

private theorem doomed14_accept {St : Type} {Δcka : ℕ} {tL : Option ℕ} {par : Bool}
    {s : GameState St M (Header T × E)} (P : Party) (st' : St) (pos : Pos)
    (hd : Doomed14 Δcka tL par s) :
    Doomed14 Δcka tL par (s.accept P st' pos) ∧ (s.accept P st' pos).win = s.win := by
  refine ⟨doomed14_mono hd (fun Q => ?_) (fun _ hx => hx) (fun _ hx => Or.inl hx), rfl⟩
  dsimp only [GameState.accept]
  exact update_epoch_ge s.epoch P Q (max (s.epoch P) pos.epoch) (Nat.le_max_left _ _)

private theorem doomedBucket_not_win {St : Type} (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (sw : GameState St M (Header T × E) × Option ℕ)
    (hd : DoomedBucket Δcka tL par sw) :
    (match sw.2 with
      | none => false
      | some tWin =>
        sw.1.win && authLosingConditionsAvoided (2 + Δcka) tL tWin sw.1) =
      false := by
  cases hw : sw.1.win
  · cases sw.2 <;> simp
  · obtain ⟨tWin, hsw2, hb⟩ := hd.2 hw
    rw [hsw2]
    have hda : DoomedAuth tL tWin sw.1 := by
      rcases hd.1 tWin hb with h1 | h4
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr h4))
    have hnw := @doomedAuth_not_win St M (Header T × E) _ inferInstance (2 + Δcka) tL tWin sw.1 hda
    have hnw' : authLosingConditionsAvoided (2 + Δcka) tL tWin sw.1 = false := by
      simpa [hw] using hnw
    simp [hnw']

private theorem doomedBucket_step_DFPaper [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : (ASpecDFB).Domain)
    {sw sw' : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ}
    {u : (ASpecDFB).Range t}
    (hd : DoomedBucket Δcka tL par sw)
    (hmem : (u, sw') ∈ support
      ((fullImplBaseDFPaperBucket (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par t).run sw)) :
    DoomedBucket Δcka tL par sw' := by
  rcases sw with ⟨s, winEp⟩
  dsimp only [fullImplBaseDFPaperBucket, withWinEpDF] at hmem
  simp only [StateT.run_mk, MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨u₀, s'⟩, h₁, h₂⟩
  simp only [support_pure, Set.mem_singleton_iff] at h₂
  injection h₂ with hu hsw'
  subst hu hsw'
  have unchanged : s' = s → DoomedBucket Δcka tL par
      (s', if (!s.win && s'.win) = true then dfQueryTargetEpoch (fun c => c.1.1) t else winEp) := by
    intro hs'
    rw [hs']
    have hwf : (!s.win && s.win) = false := by cases s.win <;> rfl
    simpa [hwf] using hd
  rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, QueryImpl.liftTarget,
      QueryImpl.ofLift] at h₁
    exact unchanged (mem_support_liftProb h₁).2
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      oracleImplPaper, transmitImpl] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    split_ifs at h₁ with hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₁
      rcases h₁ with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, h₁⟩
      rw [(mem_support_liftProb h₀).2] at h₁
      dsimp only at h₁
      cases hep : s.epMgmt (2 + Δcka) qep P bad with
      | none =>
        rw [hep] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact unchanged h₁.2
      | some s₁ =>
        rw [hep] at h₁
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rcases h₁ with ⟨_, hs'⟩
        subst hs'
        obtain ⟨hd1, hw1⟩ := doomed14_epMgmt hd.1 hep
        have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
        have hrec_w : (s₁.record (2 + Δcka) P ((scheme cka prng fs lam).send (s₁.st P) m coins).1
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ((scheme cka prng fs lam).send (s₁.st P) m coins).2⟩
            false).win = false := by
          simp [GameState.record, hw1, hw_f]
        refine ⟨doomed14_mono hd1 (fun _ => le_rfl) (fun _ hx => hx) (fun _ hx => Or.inl hx), ?_⟩
        intro hw'; exact absurd hw' (by simp [hrec_w])
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      oracleImplPaper, challImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
      injection h₁ with _ hs'; exact unchanged hs'
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at h₁
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₁
      rcases h₁ with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, h₁⟩
      rw [(mem_support_liftProb h₀).2] at h₁
      dsimp only at h₁
      cases hep : s.epMgmt (2 + Δcka) qep P bad
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
      · simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      oracleImplPaper, deliverImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    split_ifs at h₁ with hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
      injection h₁ with _ hs'; exact unchanged hs'
    · cases hin : s.inTransit P.other c with
      | none =>
        rw [hin] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
      | some rec =>
        rw [hin] at h₁
        cases hrcv : (scheme cka prng fs lam).receive (s.st P) c with
        | none =>
          rw [hrcv] at h₁
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at h₁
          injection h₁ with _ hs'; exact unchanged hs'
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          rw [hrcv] at h₁
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at h₁
          injection h₁ with _ hs'
          subst hs'
          obtain ⟨hd', hw'⟩ := doomed14_accept P st' rec.pos hd.1
          have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
          refine ⟨hd', ?_⟩
          intro h; exact absurd h (by simp [hw', hw_f])
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      oracleImplPaper, injectImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    split_ifs at h₁ with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := by
        cases h : s.win
        · rfl
        · simp [h] at hcond
      cases hrcv : (scheme cka prng fs lam).receive (s.st P) c with
      | none =>
        rw [hrcv] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact unchanged h₁.2
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcv
        subst ht'
        rw [hrcv] at h₁
        dsimp only at h₁
        split_ifs at h₁ with hqep htriv hfull
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
          exact unchanged h₁.2
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at h₁
          rcases h₁ with ⟨_, hs'⟩; subst hs'
          obtain ⟨hd', hw'⟩ := doomed14_accept P st' ⟨P.other, c.1.1, i'⟩ hd.1
          refine ⟨hd', ?_⟩
          intro h; exact absurd h (by simp [hw', hw_f])
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at h₁
          rcases h₁ with ⟨_, hs'⟩; subst hs'
          refine ⟨doomed14_mono hd.1 (fun _ => le_rfl) (fun _ hx => hx) (fun _ hx => Or.inl hx), ?_⟩
          intro _
          refine ⟨c.1.1, ?_, hfull⟩
          simp [hw_f, dfQueryTargetEpoch]
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
          exact unchanged h₁.2
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      oracleImplPaper, corrImplPaper] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    split_ifs at h₁ with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := by
        cases h : s.win
        · rfl
        · simp [h] at hcond
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, hs'⟩; subst hs'
      refine ⟨doomed14_mono hd.1 (fun _ => le_rfl)
        (fun x hx => by simp [GameState.afterCorr, GameState.leak, hx]) fun x hx => ?_, ?_⟩
      · simp only [GameState.afterCorr, GameState.leak, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr (Or.inr (le_maxOpt_right s.tL _))
        · exact Or.inl hx
      · intro h; exact absurd h (by simp [GameState.afterCorr, GameState.leak, hw_f])
  · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
      deliverForgeBaseImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
    dsimp only at h₁
    split_ifs at h₁ with hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
      cases hin : s.inTransit P.other c with
      | none =>
        rw [hin] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact unchanged h₁.2
      | some rec =>
        rw [hin] at h₁
        dsimp only at h₁
        split_ifs at h₁ with hguard
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
          exact unchanged h₁.2
        · cases hrcv : (scheme cka prng fs lam).receive (s.st P) c' with
          | none =>
            rw [hrcv] at h₁
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
            exact unchanged h₁.2
          | some res =>
            rcases res with ⟨st', t', i', m'⟩
            have ht' : t' = c'.1.1 := receive_t_eq cka prng fs hrcv
            subst ht'
            rw [hrcv] at h₁
            dsimp only at h₁
            split_ifs at h₁ with hqep htriv hfull
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
              exact unchanged h₁.2
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
              rcases h₁ with ⟨_, hs'⟩; subst hs'
              obtain ⟨hd', hw'⟩ := doomed14_accept P st' ⟨P.other, c'.1.1, i'⟩ hd.1
              refine ⟨hd', ?_⟩
              intro h; exact absurd h (by simp [hw', hw_f])
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
              rcases h₁ with ⟨_, hs'⟩; subst hs'
              refine ⟨doomed14_mono hd.1 (fun _ => le_rfl) (fun _ hx => hx) (fun _ hx => Or.inl hx), ?_⟩
              intro _
              refine ⟨c'.1.1, ?_, hfull⟩
              simp [hw_f, dfQueryTargetEpoch]
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
              exact unchanged h₁.2

private theorem doomedBucket_simulateQ_DFPaper [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {sw sw' : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ} {a : α},
      DoomedBucket Δcka tL par sw →
      (a, sw') ∈ support
        ((simulateQ (fullImplBaseDFPaperBucket (scheme cka prng fs lam) Δcka qep sameHdrScheme
          tL par) oa).run sw) →
      DoomedBucket Δcka tL par sw' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sw sw' a' hd hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.ext_iff.mp hmem with ⟨_, rfl⟩
    exact hd
  | query_bind t k ih =>
    intro sw sw' a' hd hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨u, sw₁⟩, h₁, h₂⟩
    exact ih u (doomedBucket_step_DFPaper cka prng fs lam Δcka qep tL par t hd h₁) h₂

private theorem abort_simulateQ_DFPaperBucket {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {ew ew' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × Option ℕ} {sc sc' : S} {a : α},
      ew.1.abort = true →
      ((a, ew'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDFPaperBucket hk Δ qep maxSkip cfg) oa).run ew)).run sc) →
      ew'.1.abort = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro ew ew' sc sc' a' hab hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.ext_iff.mp hmem with ⟨h1, _⟩
    rcases Prod.ext_iff.mp h1 with ⟨_, rfl⟩
    exact hab
  | query_bind t k ih =>
    intro ⟨es, winEp⟩ ew' sc sc' a' hab hmem
    dsimp only at hab
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨⟨u, ew₁⟩, sc₁⟩, h₁, h₂⟩
    dsimp only [implEDFPaperBucket, withWinEpDF] at h₁
    simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
    rcases h₁ with ⟨⟨⟨u₀, es₁⟩, sc₀⟩, hraw, h_eq⟩
    injection h_eq with h_pair hsc
    injection h_pair with hu hew
    subst hsc hu hew
    have hab₁ : es₁.abort = true := by
      rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
      · dsimp only [implEDFPaperBucketRaw, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at hraw
        simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
          simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rcases hraw with ⟨_, _, ⟨_, rfl⟩, _⟩
        exact hab
      · dsimp only [implEDFPaperBucketRaw, transmitEBucket, HAdd.hAdd, Add.add,
          QueryImpl.add] at hraw
        simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
      · dsimp only [implEDFPaperBucketRaw, challEBucket, HAdd.hAdd, Add.add,
          QueryImpl.add] at hraw
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
      all_goals
        dsimp only [implEDFPaperBucketRaw, deliverE, injectE, corrEPaperBucket, deliverForgeE,
          HAdd.hAdd, Add.add, QueryImpl.add] at hraw
        simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
    exact ih u hab₁ h₂

private theorem doomed14_of_corr_nonlocal_gt [DecidableEq I]
    {cka : CKAScheme KC Γ CCoins T I} {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc)
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hnall : sc.allowCorr (healEpoch (some l)) = false) :
    Doomed14 Δcka tL par (s.afterCorr P) := by
  have hgt : l < max (es.g.epoch .A) (es.g.epoch .B) := by
    unfold CKA.GameState.allowCorr at hnall
    rw [decide_eq_false_iff_not] at hnall
    have hA := hs.sc_epoch l htL .A
    have hB := hs.sc_epoch l htL .B
    simp only [healEpoch] at hnall
    omega
  have hm_eq : maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)) =
      max (es.g.epoch .A) (es.g.epoch .B) := by
    cases hstL : es.g.tL with
    | none => simp [maxOpt]
    | some m₀ =>
      have hm₀ := hs.leaks_ub m₀ (hs.tL_some m₀ hstL).1
      simp [maxOpt]; omega
  have hmax_le : max (es.g.epoch .A) (es.g.epoch .B) ≤ l + 2 + Δcka := by
    have hle_o := hs.epoch_le P.other
    rw [Party.other_other] at hle_o
    cases P <;> simp [Party.other] at hle_o hloc ⊢ <;> omega
  intro tWin hb
  left
  unfold inStage2Bucket at hb
  rw [Bool.and_eq_true] at hb
  have htWin : l + (3 + Δcka) ≤ tWin := by
    simpa [lastLeakGuessAdmissible, healedBy, htL] using hb.1
  rw [hs.s_eq]
  unfold Doomed1
  rw [List.any_eq_true]
  refine ⟨max (es.g.epoch .A) (es.g.epoch .B), ?_, ?_⟩
  · simp [GameState.afterCorr, GameState.leak, realGS, hm_eq]
  · simp [htL, ltOpt, hgt]
    omega

private theorem doomed14_of_sendBad_gt [DecidableEq I]
    {cka : CKAScheme KC Γ CCoins T I} {Δcka qep : ℕ} {tL : Option ℕ} {par : Bool} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc)
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P true = some s₁)
    (hgt : l < es.g.epoch P + 1)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) :
    Doomed14 Δcka tL par
      ((realGS sc s₁).record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false) := by
  have heq := hs.epoch_eq_of_sendsIn_succ hsend
  have hq : ¬qep < es.g.epoch P + 1 := by
    intro hq; simp [GameState.epMgmt, hsend, hq] at hep
  by_cases hsafe : es.g.safeCh (2 + Δcka) P = true
  · have hnl : l ∉ es.g.leaks := by
      intro hmem
      cases hstL : es.g.tL with
      | none => rw [hs.tL_none hstL] at hmem; nomatch hmem
      | some m₀ =>
        have hle := (hs.tL_some m₀ hstL).2 l hmem
        unfold GameState.safeCh at hsafe
        simp only [hstL, healedBy, decide_eq_true_eq] at hsafe
        omega
    simp only [GameState.epMgmt, hsend, hq, hsafe, Bool.not_true, Bool.and_false, ↓reduceIte,
      Option.some.injEq] at hep
    subst hep
    intro _ _
    right
    refine ⟨l, htL, hnl, ?_, ?_⟩
    · cases P <;> simp [GameState.record, realGS, Party.other] at heq ⊢ <;> omega
    · cases P <;> simp [GameState.record, realGS, Party.other] at heq ⊢ <;> omega
  · simp only [Bool.not_eq_true] at hsafe
    simp only [GameState.epMgmt, hsend, hq, hsafe, Bool.not_false, Bool.and_self, ↓reduceIte,
      Option.some.injEq] at hep
    subst hep
    have hm_eq : maxOpt es.g.tL (es.g.epoch P + 1) = es.g.epoch P + 1 := by
      cases hstL : es.g.tL with
      | none => simp [maxOpt]
      | some m₀ =>
        have hm₀ := hs.leaks_ub m₀ (hs.tL_some m₀ hstL).1
        cases P <;> simp [maxOpt, Party.other] at heq hm₀ ⊢ <;> omega
    intro tWin hb
    left
    unfold inStage2Bucket at hb
    rw [Bool.and_eq_true] at hb
    have htWin : l + (3 + Δcka) ≤ tWin := by
      simpa [lastLeakGuessAdmissible, healedBy, htL] using hb.1
    unfold Doomed1
    rw [List.any_eq_true]
    refine ⟨es.g.epoch P + 1, ?_, ?_⟩
    · simp [GameState.record, GameState.leak, realGS, hm_eq]
    · simp [htL, ltOpt, hgt]; omega

private def runLPaperBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (sw : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDFPaperBucket (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par)
    oa).run sw) >>= fun res => pure (match res.2.2 with
      | none => false
      | some tWin =>
        res.2.1.win && authLosingConditionsAvoided (2 + Δcka) tL tWin res.2.1)

private def runRPaperBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (ew : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) × Option ℕ)
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ
      (implEDFPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))
      oa).run ew)).run sc) >>= fun res => pure (authOutBucketPaper (2 + Δcka) tL res.1.2)

private theorem runLPaperBucket_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) {α : Type} (t : (ASpecDFB).Domain)
    (k : (ASpecDFB).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) (winEp : Option ℕ) :
    runLPaperBucket cka prng fs lam Δcka qep tL par (query (spec := ASpecDFB) t >>= k) (s, winEp) =
      (((fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        (bucketAuthCfg Δcka tL par) t).run s) >>=
        fun res => runLPaperBucket cka prng fs lam Δcka qep tL par (k res.1)
          (res.2, if !s.win && res.2.win then dfQueryTargetEpoch (fun c => c.1.1) t else winEp)) := by
  simp [runLPaperBucket, fullImplBaseDFPaperBucket, withWinEpDF, StateT.run_mk, StateT.run_bind]

private theorem runRPaperBucket_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) {α : Type} (t : (ASpecDFB).Domain)
    (k : (ASpecDFB).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) (sc : CKA.GameState Γ T) :
    runRPaperBucket cka prng fs Δcka qep tL par (query (spec := ASpecDFB) t >>= k) (es, winEp) sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implEDFPaperBucketRaw (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) t).run es)).run sc) >>=
        fun res => runRPaperBucket cka prng fs Δcka qep tL par (k res.1.1)
          (res.1.2, if !es.g.win && res.1.2.g.win then dfQueryTargetEpoch (fun c => c.1.1) t else winEp)
          res.2) := by
  simp [runRPaperBucket, implEDFPaperBucket, withWinEpDF, StateT.run_mk, StateT.run_bind,
    simulateQ_bind]

private theorem evalDist_runLPaperBucket_eq_pure_false_of_doomed14 [DecidableEq I]
    [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) (winEp : Option ℕ)
    (hd : Doomed14 Δcka tL par s) (hw : s.win = false) :
    𝒟[runLPaperBucket cka prng fs lam Δcka qep tL par oa (s, winEp)] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, sw'⟩ hmem
  dsimp only
  have hdb : DoomedBucket Δcka tL par (s, winEp) :=
    ⟨hd, fun h => absurd h (by simp [hw])⟩
  rw [doomedBucket_not_win Δcka tL par sw'
    (doomedBucket_simulateQ_DFPaper cka prng fs lam Δcka qep tL par oa hdb hmem)]

private theorem evalDist_runRPaperBucket_eq_pure_false_of_abort
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) (sc : CKA.GameState Γ T) (hab : es.abort = true) :
    𝒟[runRPaperBucket cka prng fs Δcka qep tL par oa (es, winEp) sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, ew'⟩, sc'⟩ hmem
  have hab' : ew'.1.abort = true :=
    abort_simulateQ_DFPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (CKA.oracleImpl cka Δcka (healEpoch tL)) oa hab hmem
  cases ew' with
  | mk es' winEp' =>
    dsimp only at hab'
    cases winEp' <;> simp [authOutBucketPaper, authOutBucket, authOut, hab']

private theorem runLPaperBucket_eq_runRPaperBucket_of_sync [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc) (winEp : Option ℕ) :
    𝒟[runLPaperBucket cka prng fs lam Δcka qep tL par oa (s, winEp)] =
      𝒟[runRPaperBucket cka prng fs Δcka qep tL par oa (es, winEp) sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc winEp with
  | pure a =>
    simp only [runLPaperBucket, runRPaperBucket, simulateQ_pure, StateT.run_pure, pure_bind]
    cases winEp with
    | none => rfl
    | some tWin =>
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hok : authLosingConditionsAvoided (2 + Δcka) tL tWin s =
          authLosingConditionsAvoided (2 + Δcka) tL tWin es.g := by
        rw [hs.s_eq]; rfl
      simp [authOutBucketPaper, authOutBucket, authOut, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    change 𝒟[runLPaperBucket cka prng fs lam Δcka qep tL par (query (spec := ASpecDFB) t >>= k)
        (s, winEp)] =
      𝒟[runRPaperBucket cka prng fs Δcka qep tL par (query (spec := ASpecDFB) t >>= k)
        (es, winEp) sc]
    rw [runLPaperBucket_query_bind, runRPaperBucket_query_bind]
    let contL : (ASpecDFB).Range t × GameState (PartyState Γ T Sig SS RS) M (Header T × E) →
        ProbComp Bool :=
      fun res => runLPaperBucket cka prng fs lam Δcka qep tL par (k res.1)
        (res.2, if !s.win && res.2.win then dfQueryTargetEpoch (fun c => c.1.1) t else winEp)
    let contR :
        ((ASpecDFB).Range t ×
          EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) ×
          CKA.GameState Γ T → ProbComp Bool :=
      fun res => runRPaperBucket cka prng fs Δcka qep tL par (k res.1.1)
        (res.1.2, if !es.g.win && res.1.2.g.win then dfQueryTargetEpoch (fun c => c.1.1) t else winEp)
        res.2
    change 𝒟[((fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
          (bucketAuthCfg Δcka tL par) t).run s) >>= contL] =
      𝒟[((simulateQ
          ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
            CKA.oracleImpl cka Δcka (healEpoch tL))
          ((implEDFPaperBucketRaw (hooksCKABucket cka prng fs Δcka tL par)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) t).run es)).run sc) >>= contR]
    have ih' : ∀ u {s' es' sc'}, Sync9 cka Δcka tL (bucketTStar Δcka tL) s' es' sc' →
        𝒟[contL (u, s')] = 𝒟[contR ((u, es'), sc')] := by
      intro u s' es' sc' hs'
      dsimp only [contL, contR]
      have hw0 : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hw1 : s'.win = es'.g.win := by rw [hs'.s_eq]; rfl
      rw [hw0, hw1]
      exact ih u hs' _
    have hdoomed : ∀ u {s'}, Doomed14 Δcka tL par s' → s'.win = false →
        𝒟[contL (u, s')] = 𝒟[(pure false : ProbComp Bool)] :=
      fun u _ hd hw' => evalDist_runLPaperBucket_eq_pure_false_of_doomed14
        cka prng fs lam Δcka qep tL par (k u) _ _ hd hw'
    have habort : ∀ u
        {es' : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)} {sc'},
        es'.abort = true → 𝒟[contR ((u, es'), sc')] = 𝒟[(pure false : ProbComp Bool)] :=
      fun u _ _ hab => evalDist_runRPaperBucket_eq_pure_false_of_abort
        cka prng fs Δcka qep tL par (k u) _ _ _ hab
    let tS := bucketTStar Δcka tL
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins cka n (fun u => ih' u hs)
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, implEDFPaperBucketRaw]
      by_cases hw : es.g.win = true
      · have hwin : s.win = true := by rw [hs.s_eq]; exact hw
        dsimp only [transmitImpl, transmitEBucket]
        simp [hs.no_abort, hw, hwin, ih' none hs]
      · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
        rw [transmitImpl_run_eq cka prng fs lam Δcka qep tL tS hs hw_f]
        dsimp only [transmitEBucket]
        rw [vSend_hooksCKABucket_eq cka prng fs Δcka tL par tS]
        simp only [hs.no_abort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
        cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
          exact ih' none hs
        | some s₁ =>
          have hs₁_st : s₁.st = es.g.st := by
            unfold GameState.epMgmt at hep
            split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
          have hs₁_win : s₁.win = false := by
            rw [(hs.epMgmt_tL_inv hep).1, hw_f]
          simp only [hs₁_st]
          by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
          · have hq : ¬qep < es.g.epoch P + 1 := by
              intro hq; simp [GameState.epMgmt, hsend, hq] at hep
            have hs₁_ep : s₁.epoch P = es.g.epoch P + 1 := by
              unfold GameState.epMgmt at hep
              simp only [hsend, hq, ↓reduceIte] at hep
              split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
            have hs₁_idx : s₁.idx P = 0 := by
              unfold GameState.epMgmt at hep
              simp only [hsend, hq, ↓reduceIte] at hep
              split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
            have hsend_eq := fun coins =>
              send_new_eq cka prng fs Δcka tL tS (m := m) (coins := coins) hs hsend
            dsimp only at hsend_eq
            by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
            · have hvR := vSend_new_local cka prng fs Δcka tL tS
                (m := m) (r := r) (s₁ := s₁) hs hsend hloc
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
              simp only [bind_assoc, pure_bind,
                hs₁_ep, hs₁_idx]
              refine evalDist_bind_congr _ _ _ fun coins => ?_
              rw [hsend_eq coins]
              exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
            · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false := Bool.eq_false_iff.mpr hloc
              obtain ⟨l, htL⟩ : ∃ l, tL = some l := by
                cases h : tL
                · simp [isLocal, h] at hloc_f
                · exact ⟨_, rfl⟩
              have hloc' : es.g.epoch P < l + 2 + Δcka := by simpa [isLocal, htL] using hloc_f
              cases r with
              | none =>
                have hvR := vSend_new_nonlocal_none cka prng fs Δcka tL tS
                  (m := m) (s₁ := s₁) hs hsend hloc_f
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [bind_assoc, pure_bind,
                  hs₁_ep, hs₁_idx]
                refine evalDist_bind_congr _ _ _ fun coins => ?_
                rw [hsend_eq coins]
                exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
              | some coins =>
                by_cases hle : es.g.epoch P + 1 ≤ l
                · have hvR := vSend_new_nonlocal_some_le cka prng fs Δcka tL tS
                    (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hle
                  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                  simp only [pure_bind,
                    hs₁_ep, hs₁_idx]
                  rw [hsend_eq coins]
                  exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
                · have hgt : l < es.g.epoch P + 1 := by omega
                  have hvR := vSend_new_nonlocal_some_gt cka prng fs Δcka tL tS
                    (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hloc_f hgt
                  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                  simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                    StateT.run_pure, simulateQ_pure]
                  have hR := habort none (es' := { es with abort := true })
                    (sc' := sc) rfl
                  have hd14 := doomed14_of_sendBad_gt (par := par) hs htL hloc' hsend hep hgt
                    (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2
                  have hL := hdoomed (some (send cka prng fs (s.st P) m coins).2) hd14
                    (by simp [GameState.record, realGS, hs₁_win])
                  exact hL.trans hR.symm
          · have hnsend : P.sendsIn (es.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsend
            have hs₁_eq : s₁ = es.g := by
              unfold GameState.epMgmt at hep
              simp only [hnsend, Bool.false_eq_true, ↓reduceIte] at hep
              split_ifs at hep
              injection hep with hep
              exact hep.symm
            subst hs₁_eq
            obtain ⟨hsendL, hsendR⟩ :=
              vSend_same_epoch cka prng fs Δcka tL tS (m := m) (r := r) hs hnsend
            have hreal_eq : realGS sc es.g = s := hs.s_eq.symm
            rw [StateT.run_bind, hsendR]
            simp only [hsendL, hreal_eq, pure_bind,
              OracleComp.evalDist_bind_const]
            exact ih' _ (hs.sync9_send_same hnsend _ m _ false)
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, implEDFPaperBucketRaw, challImpl, challEBucket, bucketAuthCfg]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure]
      by_cases hw : s.win = true
      · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
        exact ih' none hs
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
        cases r with
        | none =>
          simp only [samIfNec, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, bind_assoc, pure_bind]
          cases s.epMgmt (2 + Δcka) qep P false <;>
            simp [StateT.run_pure, OracleComp.evalDist_bind_const, ih' none hs]
        | some c =>
          simp only [samIfNec, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, pure_bind]
          cases s.epMgmt (2 + Δcka) qep P true <;>
            simp [StateT.run_pure, ih' none hs]
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, implEDFPaperBucketRaw, deliverImpl, deliverE, bucketAuthCfg]
      simp only [vRecv_hooksCKABucket_eq, commitE_hooksCKABucket_eq cka prng fs Δcka tL par tS]
      let t_eff := if inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
      have hch_eq : s.chall = es.g.chall := by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get,
        pure_bind]
      by_cases hw : es.g.win = true
      · simp [hw, ih' none hs]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        cases hin : es.g.inTransit P.other c with
        | none => simp [ih' none hs]
        | some rec =>
          simp only []
          obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
          obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv rec hmem
          have hpos_c : rec.pos.epoch = c.1.1 := by rw [← hct, ht_ep]
          have hnsend : P.sendsIn c.1.1 = false := by
            have h1 : P.other.sendsIn c.1.1 = true := by rw [← hpos_c, ← hsnd]; exact hsnd_sends
            rw [sendsIn_other, Bool.not_eq_true'] at h1; exact h1
          have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
            have hle_o : c.1.1 ≤ es.g.epoch P.other := by rw [← hpos_c, ← hsnd]; exact hle_snd
            have hle2 := hs.epoch_le P.other; rw [Party.other_other] at hle2; omega
          by_cases hstep : c.1.1 = es.g.epoch P + 1
          · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
              hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
            obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
            have hcT : c.1.2 = some T_t := by
              rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
            have hcache' : es.h.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
            obtain ⟨hrcvL, hrcvR⟩ := vRecv_new_honest cka prng fs Δcka tL t_eff
              (rec := some rec) hs hnsend hstep hcT hcache' hI
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none => simp [ih' (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              have hpos_ep : rec.pos.epoch = es.g.epoch P + 1 := by omega
              have hnsend_pos : P.sendsIn rec.pos.epoch = false := by rwa [hpos_c]
              have hcom := commitE_new cka prng fs Δcka tL tS
                (prng.up (es.g.st P).root I_t).1
                (Function.update (es.g.st P).vR c.1.1 (some v'))
                hs hpos_ep heq_other T_t hl_msg
              have hsync := hs.sync9_accept_new
                (prng.up (es.g.st P).root I_t).1
                (Function.update (es.g.st P).vR c.1.1 (some v'))
                hpos_ep heq_other hnsend_pos T_t hagr
              dsimp only at hcom hsync
              rw [hpos_c] at hcom hsync
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
              exact ih' _ hsync
          · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
            obtain ⟨hrcvL, hrcvR⟩ := vRecv_same_epoch cka prng fs Δcka tL t_eff
              (rec := some rec) hs hnsend hle_P
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hv : (es.g.st P).vR c.1.1 with
            | none => simp [ih' (some .rejected) hs]
            | some v =>
              simp only []
              cases hfs : fs.receive v c.1 c.2 with
              | none => simp [ih' (some .rejected) hs]
              | some val =>
                rcases val with ⟨v', i', m'⟩
                have hpos_le : rec.pos.epoch ≤ es.g.epoch P := by omega
                have hcom := commitE_same cka prng fs Δcka tL tS (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := rec.pos) (es := es) (sc := sc) rfl
                have hsync := hs.sync9_accept_same
                  (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
                simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                  simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
                exact ih' _ hsync
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, implEDFPaperBucketRaw, injectImpl, injectE, bucketAuthCfg]
      simp only [vRecv_hooksCKABucket_eq, commitE_hooksCKABucket_eq cka prng fs Δcka tL par tS]
      let t_eff := if inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
      have hsafe_eq : s.safeInj (2 + Δcka) = es.g.safeInj (2 + Δcka) := by rw [hs.s_eq]; rfl
      have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
        fun pos => by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hsafe_eq,
        StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hcond : (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
      · simp [hcond, ih' none hs]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        have hsafe : es.g.safeInj (2 + Δcka) = true := by
          cases h : es.g.safeInj (2 + Δcka)
          · simp [h] at hcond
          · rfl
        by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
        · obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_guard_true cka prng fs Δcka tL t_eff (rec := none) hs hguard
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
          simp [ih' (some .rejected) hs]
        · have hnsend : P.sendsIn c.1.1 = false := by
            cases h : P.sendsIn c.1.1
            · rfl
            · simp [h] at hguard
          have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by simp [hnsend] at hguard; omega
          by_cases hstep : c.1.1 = es.g.epoch P + 1
          · have htriv_f : ∀ i', es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false :=
              fun i' => hs.trivial_false_of_safeInj (P := P) hsafe (by dsimp; omega)
            cases hc2 : c.1.2 with
            | none =>
              obtain ⟨hrcvL, hrcvR⟩ :=
                vRecv_new_none cka prng fs Δcka tL t_eff (rec := none) hs hnsend hstep hc2
              dsimp only [scheme]
              rw [hrcvL, StateT.run_bind, hrcvR]
              simp [ih' (some .rejected) hs]
            | some Tn =>
              by_cases hhon_ex : ∃ I_t, es.h.cache c.1.1 = some (Tn, I_t)
              · rcases hhon_ex with ⟨I_t, hcache'⟩
                have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
                  by_contra hgt
                  have hnone := hs.cache_gt c.1.1 (by omega)
                  rw [hnone] at hcache'; nomatch hcache'
                have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
                  have hle2 := hs.epoch_le P.other; rw [Party.other_other] at hle2
                  cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
                obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.cka_step P heq_other
                rw [← heq_other, ← hstep, hcache'] at hcache_step
                injection hcache_step with hpair
                injection hpair with hT_eq hI_eq
                subst hT_eq hI_eq
                obtain ⟨hrcvL, hrcvR⟩ :=
                  vRecv_new_honest cka prng fs Δcka tL t_eff (rec := none) hs hnsend hstep hc2 hcache' hI
                dsimp only [scheme]
                rw [hrcvL, StateT.run_bind, hrcvR]
                simp only [pure_bind]
                cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
                | none => simp [ih' (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                  by_cases hqep : qep + 1 < c.1.1
                  · simp [hqep, ih' (some .rejected) hs]
                  · simp only [hqep, ↓reduceIte]
                    by_cases hfull : inStage2Bucket Δcka tL par c.1.1 = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                    · simp [hfull, ih' (some .rejected) hs]
              · have hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
                  intro Tc Ik hca heq; subst heq; exact hhon_ex ⟨Ik, hca⟩
                by_cases hb : inStage2Bucket Δcka tL par c.1.1 = true
                · have hloc : isLocal tL Δcka (es.g.epoch P) = true :=
                    inStage2Bucket_isLocal (by rwa [← hstep])
                  have hs_c : Sync9 cka Δcka tL c.1.1 s es sc :=
                    { hs with valid := inStage2Bucket_admissible hb }
                  obtain ⟨hrcvL, hrcvR⟩ :=
                    vRecv_new_dishonest_tStar_local cka prng fs Δcka tL c.1.1 (rec := none)
                      hs_c hnsend hstep hc2 hhon rfl hloc
                  dsimp only [scheme]
                  simp only [hb, ↓reduceIte]
                  rw [hrcvL, StateT.run_bind, hrcvR]
                  simp only [pure_bind]
                  cases hfs : fs.receive
                      (fs.initReceiver (prng.up (es.g.st P).root (cka.receive (s.st P).γ Tn).2).2)
                      c.1 c.2 with
                  | none => simp [ih' (some .rejected) hs]
                  | some val =>
                    rcases val with ⟨v', i', m'⟩
                    simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hqep : qep + 1 < c.1.1
                    · simp [hqep, ih' (some .rejected) hs]
                    · simp only [hqep, ↓reduceIte, hb, StateT.run_bind,
                        StateT.run_set, StateT.run_modify, pure_bind, StateT.run_pure,
                        simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                · have hb_f : inStage2Bucket Δcka tL par c.1.1 = false := Bool.eq_false_iff.mpr hb
                  have hne_eff : c.1.1 ≠ t_eff := by simp [t_eff, hb_f]
                  have hrcvR :=
                    vRecv_new_dishonest_ne cka prng fs Δcka tL t_eff (rec := none)
                      hs hnsend hstep hc2 hhon hne_eff
                  rw [StateT.run_bind, hrcvR]
                  simp only [pure_bind, StateT.run_pure, simulateQ_pure]
                  dsimp only [scheme]
                  cases hrcvL : receive cka prng fs (s.st P) c with
                  | none => simp [ih' (some .rejected) hs]
                  | some res =>
                    rcases res with ⟨st', t', i', m'⟩
                    have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL
                    subst ht'
                    simp only [htriv_eq, htriv_f, hb_f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih' (some .rejected) hs]
          · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
            obtain ⟨hrcvL, hrcvR⟩ :=
              vRecv_same_epoch cka prng fs Δcka tL t_eff (rec := none) hs hnsend hle_P
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hv : (es.g.st P).vR c.1.1 with
            | none => simp [ih' (some .rejected) hs]
            | some v =>
              simp only []
              cases hfs : fs.receive v c.1 c.2 with
              | none => simp [ih' (some .rejected) hs]
              | some val =>
                rcases val with ⟨v', i', m'⟩
                simp only []
                by_cases hqep : qep + 1 < c.1.1
                · simp [hqep, ih' (some .rejected) hs]
                · simp only [hqep, ↓reduceIte, htriv_eq]
                  by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
                  · have hcom := commitE_same cka prng fs Δcka tL tS (P := P)
                      (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                      (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                    have hsync := hs.sync9_accept_same
                      (Function.update (es.g.st P).vR c.1.1 (some v'))
                      (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                    simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                      StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                      simulateQ_pure]
                    exact ih' _ hsync
                  · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                    by_cases hfull : inStage2Bucket Δcka tL par c.1.1 = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                    · simp [hfull, ih' (some .rejected) hs]
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, implEDFPaperBucketRaw, corrImplPaper, corrEPaperBucket]
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hca : s.corrAllowedPaper P = es.g.corrAllowedPaper P := by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hguard : (es.g.win || !es.g.corrAllowedPaper P) = true
      · simp [hguard, ih' none hs]
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hwin_f : es.g.win = false := by
          cases hw : es.g.win
          · rfl
          · simp [hw] at hguard
        have hγ := hs.γ_eq P
        by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
        · simp only [hloc, ↓reduceIte] at hγ
          have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
              (es.g.st P).vR = s.st P := by rw [hs.s_eq]; rfl
          simp only [hooksCKABucket, hooksCKA, hγ, pure_bind,
            hst_eq]
          exact ih' (some (s.st P)) (hs.sync9_corr P)
        · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
          rcases htL : tL with _ | l
          · simp [isLocal, htL] at hloc
          · have hloc' : es.g.epoch P < l + 2 + Δcka := by
              simp [isLocal, htL] at hloc; exact hloc
            have hfin_f : sc.finished Δcka (healEpoch (some l)) P = false := by
              unfold CKA.GameState.finished
              rw [decide_eq_false_iff_not, hs.sc_epoch l htL P]
              simp only [healEpoch]; omega
            by_cases hall : sc.allowCorr (healEpoch (some l)) = true
            · have hst_eq : realParty (es.g.st P) (sc.st P) (es.g.st P).root (es.g.st P).vS
                  (es.g.st P).vR = s.st P := by
                rw [hs.s_eq]; simp [realGS, realVP, realParty, hγ]
              simp only [hooksCKABucket, hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery,
                StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
                QueryImpl.add_apply, CKA.oracleImpl, CKA.corrImpl, hall, Bool.true_or,
                ↓reduceIte, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure,
                StateT.run_modify, StateT.run_set, bind_assoc, hst_eq]
              exact ih' (some (s.st P)) (hs.sync9_corr P)
            · have hall_f : sc.allowCorr (healEpoch (some l)) = false := Bool.eq_false_iff.mpr hall
              simp only [hooksCKABucket, hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery,
                StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
                QueryImpl.add_apply, CKA.oracleImpl, CKA.corrImpl, hall_f, hfin_f, Bool.or_self,
                StateT.run_get, pure_bind, StateT.run_pure,
                abortE, StateT.run_set, bind_assoc]
              have hR := habort none (es' := { es with abort := true }) (sc' := sc) rfl
              have hd14 := doomed14_of_corr_nonlocal_gt (par := par) hs htL hloc' hall_f
              have hL := hdoomed (some (s.st P)) hd14
                (by rw [hs.s_eq]; simp [GameState.afterCorr, GameState.leak, realGS, hwin_f])
              exact hL.trans hR.symm
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        implEDFPaperBucketRaw, deliverForgeBaseImpl, deliverForgeE, sameHdrScheme, bucketAuthCfg]
      simp only [vRecv_hooksCKABucket_eq, commitE_hooksCKABucket_eq cka prng fs Δcka tL par tS]
      let t_eff := if inStage2Bucket Δcka tL par c'.1.1 then c'.1.1 else c'.1.1 + 1
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
      have hin'_eq : s.inTransit P.other c' = es.g.inTransit P.other c' := by rw [hs.s_eq]; rfl
      have hcomp_eq : ∀ pos, s.comp.contains pos = es.g.comp.contains pos :=
        fun pos => by rw [hs.s_eq]; rfl
      have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
        fun pos => by rw [hs.s_eq]; rfl
      have hbne : (!(c.1 == c'.1)) = (c.1 != c'.1) := rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hin'_eq, hcomp_eq, hbne,
        StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hw : es.g.win = true
      · simp [hw, ih' none hs]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte]
        cases hin : es.g.inTransit P.other c with
        | none => simp [ih' none hs]
        | some rec =>
          simp only []
          by_cases hguard :
              ((es.g.inTransit P.other c').isSome || es.g.comp.contains rec.pos ||
                (c.1 != c'.1)) = true
          · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
            exact ih' none hs
          · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
            have hhdr : c'.1 = c.1 := by
              rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard) with ⟨_, h2⟩
              exact (bne_eq_false_iff_eq.mp h2).symm
            obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
            obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv rec hmem
            have hpos_c : rec.pos.epoch = c'.1.1 := by rw [hhdr, ← hct, ht_ep]
            have hnsend : P.sendsIn c'.1.1 = false := by
              have h1 : P.other.sendsIn c'.1.1 = true := by rw [← hpos_c, ← hsnd]; exact hsnd_sends
              rw [sendsIn_other, Bool.not_eq_true'] at h1; exact h1
            have hle_P1 : c'.1.1 ≤ es.g.epoch P + 1 := by
              have hle_o : c'.1.1 ≤ es.g.epoch P.other := by rw [← hpos_c, ← hsnd]; exact hle_snd
              have hle2 := hs.epoch_le P.other; rw [Party.other_other] at hle2; omega
            by_cases hstep : c'.1.1 = es.g.epoch P + 1
            · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
                hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct, ← hhdr]; exact hstep)
              obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
              have hcT : c'.1.2 = some T_t := by
                rw [hhdr, ← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
              have hcache' : es.h.cache c'.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
              obtain ⟨hrcvL, hrcvR⟩ :=
                vRecv_new_honest cka prng fs Δcka tL t_eff (rec := none) hs hnsend hstep hcT hcache' hI
              dsimp only [scheme]
              rw [hrcvL, StateT.run_bind, hrcvR]
              simp only [pure_bind]
              cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c'.1 c'.2 with
              | none => simp [ih' (some .rejected) hs]
              | some val =>
                rcases val with ⟨v', i', m'⟩
                have hne_ep : (c'.1.1 != rec.pos.epoch) = false := by
                  rw [bne_eq_false_iff_eq, hpos_c]
                simp only [hne_ep, Bool.or_false]
                by_cases hqep : decide (qep + 1 < c'.1.1) = true
                · simp [hqep, ih' (some .rejected) hs]
                · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
                  by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
                  · have hcom := commitE_new cka prng fs Δcka tL tS
                      (pos := ⟨P.other, c'.1.1, i'⟩)
                      (prng.up (es.g.st P).root I_t).1
                      (Function.update (es.g.st P).vR c'.1.1 (some v'))
                      hs hstep heq_other T_t hl_msg
                    have hsync := hs.sync9_accept_new
                      (pos := ⟨P.other, c'.1.1, i'⟩)
                      (prng.up (es.g.st P).root I_t).1
                      (Function.update (es.g.st P).vR c'.1.1 (some v'))
                      hstep heq_other hnsend T_t hagr
                    dsimp only at hcom hsync
                    simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                      StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure]
                    exact ih' _ hsync
                  · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                    by_cases hfull : inStage2Bucket Δcka tL par c'.1.1 = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                    · simp [hfull, ih' (some .rejected) hs]
            · have hle_P : c'.1.1 ≤ es.g.epoch P := by omega
              obtain ⟨hrcvL, hrcvR⟩ :=
                vRecv_same_epoch cka prng fs Δcka tL t_eff (rec := none) hs hnsend hle_P
              dsimp only [scheme]
              rw [hrcvL, StateT.run_bind, hrcvR]
              simp only [pure_bind]
              cases hv : (es.g.st P).vR c'.1.1 with
              | none => simp [ih' (some .rejected) hs]
              | some v =>
                simp only []
                cases hfs : fs.receive v c'.1 c'.2 with
                | none => simp [ih' (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  have hne_ep : (c'.1.1 != rec.pos.epoch) = false := by
                    rw [bne_eq_false_iff_eq, hpos_c]
                  simp only [hne_ep, Bool.or_false]
                  by_cases hqep : decide (qep + 1 < c'.1.1) = true
                  · simp [hqep, ih' (some .rejected) hs]
                  · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
                    by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
                    · have hcom := commitE_same cka prng fs Δcka tL tS (P := P)
                        (new := { es.g.st P with vR := Function.update (es.g.st P).vR c'.1.1 (some v') })
                        (pos := ⟨P.other, c'.1.1, i'⟩) (es := es) (sc := sc) rfl
                      have hsync := hs.sync9_accept_same
                        (Function.update (es.g.st P).vR c'.1.1 (some v'))
                        (pos := ⟨P.other, c'.1.1, i'⟩) hle_P
                      simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                        StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure]
                      exact ih' _ hsync
                    · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                      by_cases hfull : inStage2Bucket Δcka tL par c'.1.1 = true
                      · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                          StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                        exact ih' (some .rejected) (hs.sync9_win true)
                      · simp [hfull, ih' (some .rejected) hs]

private theorem forgeGameBucketPaper_eq_runLPaperBucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameBucketPaper (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLPaperBucket cka prng fs lam Δcka qep tL par A
          (initState (scheme cka prng fs lam) (kr, kc) false, none)) := by
  unfold forgeGameBucketPaper runLPaperBucket
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

end BucketProofPaper

/-- Hop 1 (`Lemma 9`) for the Stage-2 `(tL, par)` bucket `DeliverForgePaper` game. -/
theorem lemma9_df_paper_bucket [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (hΔ : 0 < Δcka) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeBucketAdvantagePaper (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} := by
  let _ := hΔ
  apply le_of_eq
  unfold forgeBucketAdvantagePaper
  rw [forgeGameBucketPaper_eq_runLPaperBucket]
  congr 1
  have hvg := bucketTStar_admissible Δcka tL
  cases htL : tL with
  | none =>
    subst htL
    unfold CKA.branch redCKAAuthDFPaperBucket engRunDFPaperBucket
    rw [initCKA_zero_eq cka prng fs lam none (bucketTStar Δcka none)]
    unfold initCKA
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
      pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
      AuthL9.simulateQ_sampleT_run, map_bind]
    symm
    refine (evalDist_bind_congr ($ᵗ KC) _
      (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLPaperBucket cka prng fs lam Δcka qep none par A
          (initState (scheme cka prng fs lam) (kr, kc) false, none)) ?_).trans ?_
    · intro kc_ext
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      symm
      refine (runLPaperBucket_eq_runRPaperBucket_of_sync cka prng fs lam Δcka qep none par A
        (AuthL9.sync9_init_none cka prng fs lam Δcka (bucketTStar Δcka none) hc hvg kr kc kc_ext)
        none).trans ?_
      simp only [runRPaperBucket, bind_pure_comp, map_pure]
      rfl
    · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
  | some l =>
    subst htL
    unfold CKA.branch redCKAAuthDFPaperBucket engRunDFPaperBucket
    rw [initCKA_zero_eq cka prng fs lam (some l) (bucketTStar Δcka (some l))]
    unfold initCKA
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
      pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
      AuthL9.simulateQ_sampleT_run, map_bind]
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine evalDist_bind_congr _ _ _ fun kc => ?_
    refine evalDist_bind_congr _ _ _ fun kr => ?_
    refine (runLPaperBucket_eq_runRPaperBucket_of_sync cka prng fs lam Δcka qep (some l) par A
      (AuthL9.Sync9.sync9_init prng fs lam hc hvg kr kc) none).trans ?_
    simp only [runRPaperBucket, bind_pure_comp, map_pure]
    rfl

/-- Stage-2 `(tL, par)` bucket CKA hop (`lemma9_df_paper_bucket` + CKA triangle inequality):
bounds `forgeBucketAdvantagePaper` by a single `CKA.advantage` at `healEpoch tL` plus the ideal CKA
world (`b = true`) of `redCKAAuthDFPaperBucket` (ready to telescope across `B_prng_u` and hoist MAC
once per `(tL, par)` bucket). -/
theorem forgeBucketAdvantagePaper_le_cka_add_branch_true [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (hΔ : 0 < Δcka) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeBucketAdvantagePaper (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par A ≤
      CKA.advantage cka Δcka (healEpoch tL)
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A) +
      𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} := by
  refine (lemma9_df_paper_bucket cka prng fs lam Δcka qep hc hΔ tL par A).trans ?_
  rw [CKA.advantage_eq_boolDist, add_comm, Measure.boolDist_comm]
  exact Measure.apply_true_le_add_boolDist _ _

/-- Non-paper Stage-2 `(tL, par)` bucket CKA hop (`lemma9_df_bucket` + CKA triangle inequality). -/
theorem forgeBucketAdvantage_le_cka_add_branch_true [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (hΔ : 0 < Δcka) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeBucketAdvantage (scheme cka prng fs lam) Δcka qep sameHdrScheme tL par A ≤
      CKA.advantage cka Δcka (healEpoch tL)
        (redCKAAuthDFBucket cka prng fs lam Δcka qep tL par A) +
      𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFBucket cka prng fs lam Δcka qep tL par A)] {true} := by
  refine (lemma9_df_bucket cka prng fs lam Δcka qep hc hΔ tL par A).trans ?_
  rw [CKA.advantage_eq_boolDist, add_comm, Measure.boolDist_comm]
  exact Measure.apply_true_le_add_boolDist _ _

end BucketEnginePaper

end CryptoGames.SM.Construction.DeliverForge
