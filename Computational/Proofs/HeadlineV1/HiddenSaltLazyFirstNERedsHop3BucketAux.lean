/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import

import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import VCVio.OracleComp.EvalDist.Measure

set_option autoImplicit false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux

public section

open scoped ENNReal
open OracleComp OracleSpec
open MeasureTheory (Measure)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.SM (Config GameState Pos Record lastLeakGuessAdmissible specDF)
open CryptoGames.SM.Construction (Header PartyState healEpoch)
open CryptoGames.SM.Construction.DeliverForge (LocalBucketState MakesAtMostQueriesDF
  SchemeAdversaryDF authOutBucket authOutBucketPaper bucketAuthCfg challEBucket corrEPaperBucket
  deliverForgeE engRunDFPaperBucketMode hooksLocalBucket hooksLocalBucketForgedHdr
  hooksLocalBucketMain implEDFPaperBucketMode implEDFPaperBucketRaw inStage2Bucket initLocalBucket
  isHonestHdrLocalBucket localAuthDFPaperBucketForgedHdr localAuthDFPaperBucketMain
  localAuthDFPaperBucketMode localAuthDFPaperBucketSplit rootLocalBucket transmitEBucket
  withWinEpDF withWinEpDFMode)
open CryptoGames.SM.Engine (Ctx EM EState HM Hooks TComp VP abortE coinsE commitE deliverE injectE
  liftH vRecv vSend)

private theorem evalDist_bind_const_probComp {α β : Type} [MeasurableSpace β]
    (p : ProbComp α) (q : ProbComp β) :
    𝒟[p >>= fun _ => q] = 𝒟[q] := by
  induction p using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind n k ih =>
    change 𝒟[query (spec := unifSpec) n >>= fun u => (k u >>= fun _ => q)] = 𝒟[q]
    rw [evalDist_bind_congr (query (spec := unifSpec) n)
      (fun u => k u >>= fun _ => q) (fun _ => q) (fun u => ih u)]
    rw [evalDist_bind_of_discrete]
    ext s hs
    rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
    simp

private theorem withWinEpDFMode_inl_run
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool) (n : unifSpec.Domain)
    (es0 : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (winEp0 : Option ℕ) :
    (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest (.inl n)).run (es0, winEp0) =
      (fun u => (u, (es0, winEp0))) <$> query (spec := unifSpec + tspec) (.inl n) := by
  cases gMain <;>
    simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      coinsE, StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]

private theorem withWinEpDFMode_congr_of_raw_eq
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl₁ impl₂ : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (qy : (unifSpec + specDF St Msg Coins (Header T' × E')).Domain)
    (es0 : EState VPt Msg (Header T' × E') HS) (winEp0 : Option ℕ)
    (hEq : (impl₁ qy).run es0 = (impl₂ qy).run es0) :
    (withWinEpDFMode gMain isHonest epOf impl₁ qy).run (es0, winEp0) =
      (withWinEpDFMode gMain isHonest epOf impl₂ qy).run (es0, winEp0) := by
  cases gMain <;>
    simp only [withWinEpDFMode, withWinEpDF, ↓reduceIte, Bool.false_eq_true, StateT.run_mk, hEq]

private theorem mem_support_withWinEpDFMode_inr
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (t : (specDF St Msg Coins (Header T' × E')).Domain)
    (es0 es' : EState VPt Msg (Header T' × E') HS) (winEp0 winEp' : Option ℕ)
    (out : (unifSpec + specDF St Msg Coins (Header T' × E')).Range (.inr t))
    (hmem : (out, (es', winEp')) ∈
      support ((withWinEpDFMode gMain isHonest epOf impl (.inr t)).run (es0, winEp0))) :
    (out, es') ∈ support ((impl (.inr t)).run es0) ∧
    (es'.g.win = false → winEp' = winEp0) := by
  cases gMain
  · simp only [withWinEpDFMode, Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨r, es₁⟩, hr, rfl, rfl, hwin⟩ := hmem
    refine ⟨hr, fun hw => ?_⟩
    simp [hw] at hwin; exact hwin
  · simp only [withWinEpDFMode, ↓reduceIte, withWinEpDF, StateT.run_mk,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨r, es₁⟩, hr, rfl, rfl, hwin⟩ := hmem
    refine ⟨hr, fun hw => ?_⟩
    simp [hw] at hwin; exact hwin

/-- Lightweight structural epoch bound on `Ctx` across `≤ E` queries. -/
private def EpochBound {Γv T Sv SSv RSv M E_ct : Type} (E : ℕ)
    (g : Ctx Γv T Sv SSv RSv M E_ct) : Prop :=
  (∀ P, g.epoch P ≤ E) ∧ (∀ P, (g.st P).tcur ≤ E) ∧ (∀ r ∈ g.trans, r.pos.epoch ≤ E)

private theorem EpochBound.mono {Γv T Sv SSv RSv M E_ct : Type} {E₁ E₂ : ℕ}
    {g : Ctx Γv T Sv SSv RSv M E_ct} (hle : E₁ ≤ E₂) (h : EpochBound E₁ g) :
    EpochBound E₂ g :=
  ⟨fun P => (h.1 P).trans hle, fun P => (h.2.1 P).trans hle,
   fun r hr => (h.2.2 r hr).trans hle⟩

private theorem vSend_tcur_le
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type} [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : HS) :
    ∀ res ∈ support ((vSend hk ctx P s m pair r).run h),
      ∀ st' ct, res.1 = some (st', ct) → st'.tcur ≤ s.tcur + 1 := by
  intro ⟨ans, h'⟩ hmem st' ct hEq
  dsimp only at hEq; subst hEq
  unfold vSend at hmem; dsimp only at hmem
  by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
  · simp only [hSend, ↓reduceIte, StateT.run_bind, pure_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨sr, h₁⟩, _, hmem⟩ := hmem
    rcases sr with _ | ⟨γ', T', σ', ss⟩
    · simp [StateT.run_pure] at hmem
    · dsimp only at hmem
      rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨fr, _⟩, _, hmem⟩ := hmem
      rcases fr with _ | ⟨v', e⟩
      · simp [StateT.run_pure] at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases hmem with ⟨⟨rfl, _⟩, _⟩; exact le_rfl
  · simp only [hSend, Bool.false_eq_true, ↓reduceIte, pure_bind] at hmem
    cases hvS : s.vS with
    | none =>
      simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩; exact Nat.le_succ _
    | some v =>
      simp only [hvS, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨fr, _⟩, _, hmem⟩ := hmem
      rcases fr with _ | ⟨v', e⟩
      · simp [StateT.run_pure] at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases hmem with ⟨⟨rfl, _⟩, _⟩; exact Nat.le_succ _

private theorem vRecv_tcur_and_epoch_le
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec_ : Option (Record M (Header T × E))) (h : HS) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec_).run h),
      ∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        t' = c.1.1 ∧ c.1.1 ≤ s.tcur + 1 ∧ st'.tcur ≤ s.tcur + 1 := by
  intro ⟨ans, h'⟩ hmem st' t' i' m' hEq
  dsimp only at hEq; subst hEq
  unfold vRecv at hmem; dsimp only at hmem
  by_cases hGuard : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp [hGuard, StateT.run_pure] at hmem
  · simp only [hGuard, Bool.false_eq_true, ↓reduceIte] at hmem
    have hcle : c.1.1 ≤ s.tcur + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hGuard; omega
    by_cases htEq : c.1.1 = s.tcur + 1
    · simp only [htEq, ↓reduceIte] at hmem
      cases hc2 : c.1.2 with
      | none =>
        simp [hc2, pure_bind, StateT.run_pure] at hmem
      | some Tn =>
        simp only [hc2, StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨sr, h₁⟩, _, hmem⟩ := hmem
        rcases sr with _ | (_ | ⟨γ', σ', rs⟩)
        · simp [pure_bind, StateT.run_pure] at hmem
        · simp [pure_bind, StateT.run_pure] at hmem
        · simp only [pure_bind, Function.update_self, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨fr, _⟩, _, hmem⟩ := hmem
          rcases fr with _ | (_ | ⟨v', i₀, m₀⟩)
          · simp [StateT.run_pure] at hmem
          · simp [StateT.run_pure] at hmem
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
              Option.some.injEq] at hmem
            rcases hmem with ⟨⟨rfl, rfl, rfl, rfl⟩, _⟩
            exact ⟨htEq.symm, hcle, le_rfl⟩
    · simp only [htEq, ↓reduceIte, pure_bind] at hmem
      cases hvR : s.vR c.1.1 with
      | none =>
        simp [hvR, StateT.run_pure] at hmem
      | some v =>
        simp only [hvR, StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨fr, _⟩, _, hmem⟩ := hmem
        rcases fr with _ | (_ | ⟨v', i₀, m₀⟩)
        · simp [StateT.run_pure] at hmem
        · simp [StateT.run_pure] at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, rfl, rfl, rfl⟩, _⟩
          exact ⟨rfl, hcle, Nat.le_succ _⟩

private theorem epMgmt_epoch_st_trans_win
    {St Msg C : Type} {s s₁ : GameState St Msg C} {Δ qep E : ℕ} {P : Party} {bad : Bool}
    (hB : (∀ Q, s.epoch Q ≤ E) ∧ (∀ r ∈ s.trans, r.pos.epoch ≤ E))
    (hep : s.epMgmt Δ qep P bad = some s₁) :
    (∀ Q, s₁.epoch Q ≤ E + 1) ∧ s₁.st = s.st ∧ s₁.trans = s.trans ∧ s₁.win = s.win := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs1 hq1 hleak hq2
  · simp only [Option.some.injEq] at hep; subst hep
    refine ⟨fun Q => ?_, rfl, rfl, rfl⟩
    by_cases hQP : Q = P
    · subst hQP; simp [GameState.leak, Nat.add_le_add_right (hB.1 Q) 1]
    · simp [GameState.leak, Function.update_of_ne hQP, (hB.1 Q).trans (Nat.le_succ _)]
  · simp only [Option.some.injEq] at hep; subst hep
    refine ⟨fun Q => ?_, rfl, rfl, rfl⟩
    by_cases hQP : Q = P
    · subst hQP; simp [Nat.add_le_add_right (hB.1 Q) 1]
    · simp [Function.update_of_ne hQP, (hB.1 Q).trans (Nat.le_succ _)]
  · simp only [Option.some.injEq] at hep; subst hep
    exact ⟨fun Q => (hB.1 Q).trans (Nat.le_succ _), rfl, rfl, rfl⟩

private theorem epMgmt_qep_congr
    {St Msg C : Type} (s : GameState St Msg C) (Δ qep₁ qep₂ E : ℕ) (P : Party) (bad : Bool)
    (hEp : s.epoch P ≤ E) (hq₁ : E + 1 ≤ qep₁) (hq₂ : E + 1 ≤ qep₂) :
    s.epMgmt Δ qep₁ P bad = s.epMgmt Δ qep₂ P bad := by
  unfold GameState.epMgmt
  have h1 : ¬ (qep₁ < s.epoch P + 1) := by omega
  have h2 : ¬ (qep₂ < s.epoch P + 1) := by omega
  have h3 : ¬ (qep₁ < s.epoch P) := by omega
  have h4 : ¬ (qep₂ < s.epoch P) := by omega
  simp only [h1, h2, h3, h4, ↓reduceIte]

private theorem run_liftH_bind' {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E_ct HS α β : Type}
    (x : HM tspec HS α) (f : α → EM tspec Γv T Sv SSv RSv M E_ct HS β)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS) :
    (liftH x >>= f).run es = (x.run es.h >>= fun p => (f p.1).run { es with h := p.2 }) := by
  simp [StateT.run_bind]

private theorem commitE_epochBound_and_win
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E_ct HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E_ct] [Inhabited E_ct]
    (hk : Hooks tspec HS Γ T Sig SS RS M E_ct CCoins Γv Sv SSv RSv)
    (hCom : ∀ ctx P old new, hk.commit ctx P old new = pure (some new))
    {E : ℕ} {s : Ctx Γv T Sv SSv RSv M E_ct} {P : Party} {st' : VP Γv T Sv SSv RSv} {pos : Pos}
    {es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS}
    (hBound : EpochBound E s) (hst' : st'.tcur ≤ E + 1) (hpos : pos.epoch ≤ E + 1) :
    ∀ res ∈ support ((commitE hk s P (s.st P) st' pos).run es),
      ∀ s₁, res.1 = some s₁ → EpochBound (E + 1) s₁ ∧ s₁.win = s.win := by
  intro ⟨ans, es₁⟩ hmem s₁ hEq
  dsimp only at hEq; subst hEq
  unfold commitE at hmem
  simp only [hCom, StateT.run_bind] at hmem
  rcases hmem with ⟨rfl, _⟩
  refine ⟨⟨fun Q => ?_, fun Q => ?_, fun r hr => ?_⟩, rfl⟩
  · simp only [GameState.accept, GameState.delete]
    by_cases hQP : Q = P
    · subst hQP; simp [(hBound.1 Q).trans (Nat.le_succ _), hpos]
    · simp [Function.update_of_ne hQP, (hBound.1 Q).trans (Nat.le_succ _)]
  · simp only [GameState.accept, GameState.delete]
    by_cases hQP : Q = P
    · subst hQP; simp [hst']
    · simp [Function.update_of_ne hQP, (hBound.2.1 Q).trans (Nat.le_succ _)]
  · simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
    exact (hBound.2.2 r hr.1).trans (Nat.le_succ _)

private theorem implEDFPaperBucketRaw_epochBound_and_noWin
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E_ct HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E_ct] [Inhabited E_ct]
    (hk : Hooks tspec HS Γ T Sig SS RS M E_ct CCoins Γv Sv SSv RSv)
    (hCom : ∀ ctx P old new, hk.commit ctx P old new = pure (some new))
    (Δ qep maxSkip E : ℕ) (cfg : Config M)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS)
    (t : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E_ct)).Domain)
    (hBound : EpochBound E es.g) :
    ∀ res ∈ support ((implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      EpochBound (E + 1) res.2.g ∧
      (es.g.win = false → cfg.deliverWin = false →
        (∀ t', t' ≤ E + 1 → cfg.injectFull t' = false) → res.2.g.win = false) := by
  have hB1 : EpochBound (E + 1) es.g := hBound.mono (Nat.le_succ _)
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
    · rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · obtain ⟨hs₁Ep, hs₁St, hs₁Tr, hs₁Win⟩ :=
          epMgmt_epoch_st_trans_win ⟨hBound.1, hBound.2.2⟩ hep
        simp only [hep, run_liftH_bind', mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
        · have hst' : st'.tcur ≤ E + 1 := by
            have h1 := vSend_tcur_le hk s₁ P (s₁.st P) m none r es.h _ hvs st' ct rfl
            rw [hs₁St] at h1; exact h1.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          refine ⟨⟨fun Q => hs₁Ep Q, fun Q => ?_, fun rec_ hrec => ?_⟩,
            fun hw _ _ => by simpa [GameState.record, hs₁Win] using hw⟩
          · simp only [GameState.record]
            by_cases hQP : Q = P
            · subst hQP; simp [hst']
            · simp [Function.update_of_ne hQP, hs₁St, (hBound.2.1 Q).trans (Nat.le_succ _)]
          · simp only [GameState.record, List.mem_cons] at hrec
            rcases hrec with rfl | hrec
            · exact hs₁Ep P
            · rw [hs₁Tr] at hrec; exact (hBound.2.2 rec_ hrec).trans (Nat.le_succ _)
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((deliverE hk maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
    · rcases htr : es.g.inTransit P.other c with _ | rec_
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · have hrecEp : rec_.pos.epoch ≤ E + 1 := by
          unfold GameState.inTransit at htr
          exact (hBound.2.2 rec_ (List.mem_of_find?_eq_some htr)).trans (Nat.le_succ _)
        simp only [htr, run_liftH_bind', mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        rcases vrRes with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
        · dsimp only at hmem
          split_ifs at hmem with hmust
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            refine ⟨⟨hB1.1, hB1.2.1, hB1.2.2⟩, fun _ hdw _ => ?_⟩
            simp [hdw] at hmust
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
        · obtain ⟨_, _, hst'0⟩ :=
            vRecv_tcur_and_epoch_le hk es.g P (es.g.st P) c (some rec_) es.h _ hvr st' t' i' m' rfl
          have hst' : st'.tcur ≤ E + 1 := hst'0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
          rw [StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es₁⟩, hcm, hmem⟩ := hmem
          rcases cmRes with _ | s₁
          · unfold commitE at hcm
            simp [hCom, StateT.run_bind, StateT.run_pure, pure_bind] at hcm
          · obtain ⟨hs₁B, hs₁Win⟩ := commitE_epochBound_and_win hk hCom hBound hst' hrecEp _ hcm s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            split_ifs with hbad
            · refine ⟨⟨hs₁B.1, hs₁B.2.1, hs₁B.2.2⟩, fun _ hdw _ => ?_⟩
              simp [hdw] at hbad
            · exact ⟨hs₁B, fun hw _ _ => hs₁Win.trans hw⟩
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((injectE hk Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
    · rw [run_liftH_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      rcases vrRes with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · obtain ⟨ht'Eq, hcle0, hst'0⟩ :=
          vRecv_tcur_and_epoch_le hk es.g P (es.g.st P) c none es.h _ hvr st' t' i' m' rfl
        have ht' : t' ≤ E + 1 := ht'Eq ▸ hcle0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
        have hst' : st'.tcur ≤ E + 1 := hst'0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
        dsimp only at hmem
        split_ifs at hmem with hqep_lt htriv hinjF
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
        · rw [StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es₁⟩, hcm, hmem⟩ := hmem
          rcases cmRes with _ | s₁
          · unfold commitE at hcm
            simp [hCom, StateT.run_bind, StateT.run_pure, pure_bind] at hcm
          · obtain ⟨hs₁B, hs₁Win⟩ := commitE_epochBound_and_win hk hCom hBound hst' ht' _ hcm s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact ⟨hs₁B, fun hw _ _ => hs₁Win.trans hw⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          refine ⟨⟨hB1.1, hB1.2.1, hB1.2.2⟩, fun _ _ hNoInj => ?_⟩
          rw [hNoInj t' ht'] at hinjF; cases hinjF
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((corrEPaperBucket hk P).run es) at hmem
    unfold corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
    · rw [run_liftH_bind', mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem
      rcases revRes with _ | _
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨⟨hB1.1, hB1.2.1, hB1.2.2⟩, fun hw _ _ => hw⟩
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((deliverForgeE hk Δ qep cfg (P, c, c')).run es) at hmem
    unfold deliverForgeE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
    · rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
      · simp only [htr] at hmem
        split_ifs at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
        · rw [run_liftH_bind', mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
          rcases vrRes with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
          · obtain ⟨ht'Eq, hcle0, hst'0⟩ :=
              vRecv_tcur_and_epoch_le hk es.g P (es.g.st P) c' none es.h _ hvr st' t' i' m' rfl
            have ht' : t' ≤ E + 1 := ht'Eq ▸ hcle0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
            have hst' : st'.tcur ≤ E + 1 := hst'0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
            dsimp only at hmem
            split_ifs at hmem with hqep_lt htriv hinjF
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩
            · rw [StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es₁⟩, hcm, hmem⟩ := hmem
              rcases cmRes with _ | s₁
              · unfold commitE at hcm
                simp [hCom, StateT.run_bind, StateT.run_pure, pure_bind] at hcm
              · obtain ⟨hs₁B, hs₁Win⟩ := commitE_epochBound_and_win hk hCom hBound hst' ht' _ hcm s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact ⟨hs₁B, fun hw _ _ => hs₁Win.trans hw⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              refine ⟨⟨hB1.1, hB1.2.1, hB1.2.2⟩, fun _ _ hNoInj => ?_⟩
              rw [hNoInj t' ht'] at hinjF; cases hinjF
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact ⟨hB1, fun hw _ _ => hw⟩

private theorem implEDFPaperBucketRaw_qep_congr
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E_ct HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E_ct] [Inhabited E_ct]
    (hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E_ct CCoins Γv Sv SSv RSv)
    (Δ qep₁ qep₂ maxSkip E : ℕ) (cfg : Config M)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS)
    (t : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E_ct)).Domain)
    (hBound : EpochBound E es.g)
    (hq₁ : E + 1 ≤ qep₁) (hq₂ : E + 1 ≤ qep₂)
    (hStartSend : ∀ ctx P t0 γ σ r, t0 ≤ E + 1 →
      hk₁.startSend ctx P t0 γ σ r = hk₂.startSend ctx P t0 γ σ r)
    (hStartRecv : ∀ ctx P t0 γ σ Tn, t0 ≤ E + 1 →
      hk₁.startRecv ctx P t0 γ σ Tn = hk₂.startRecv ctx P t0 γ σ Tn)
    (hFsSend : hk₁.fsSend = hk₂.fsSend)
    (hFsRecv : hk₁.fsRecv = hk₂.fsRecv)
    (hCommit : hk₁.commit = hk₂.commit)
    (hReveal : hk₁.reveal = hk₂.reveal) :
    (implEDFPaperBucketRaw hk₁ Δ qep₁ maxSkip cfg (.inr t)).run es =
      (implEDFPaperBucketRaw hk₂ Δ qep₂ maxSkip cfg (.inr t)).run es := by
  have hComEq : commitE hk₁ = commitE hk₂ := by
    funext s P old new; unfold commitE; rw [hCommit]
  have hvRecvEq : ∀ P c rec_,
      (vRecv hk₁ es.g P (es.g.st P) c rec_).run es.h =
        (vRecv hk₂ es.g P (es.g.st P) c rec_).run es.h := by
    intro P c rec_
    unfold vRecv; dsimp only
    by_cases hG : ((es.g.st P).id.sendsIn c.1.1 || decide ((es.g.st P).tcur + 1 < c.1.1)) = true
    · simp [hG]
    · simp only [hG, Bool.false_eq_true, ↓reduceIte]
      by_cases htEq : c.1.1 = (es.g.st P).tcur + 1
      · simp only [htEq, ↓reduceIte]
        rcases c.1.2 with _ | Tn
        · rfl
        · simp only [hStartRecv es.g P ((es.g.st P).tcur + 1) _ _ Tn
            (Nat.add_le_add_right (hBound.2.1 P) 1), hFsRecv]
      · simp only [htEq, ↓reduceIte, hFsRecv]
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (transmitEBucket hk₁ Δ qep₁ (P, m, r)).run es =
        (transmitEBucket hk₂ Δ qep₂ (P, m, r)).run es
    unfold transmitEBucket
    simp only [StateT.run_bind, StateT.run_get, pure_bind,
      epMgmt_qep_congr es.g Δ qep₁ qep₂ E P r.isSome (hBound.1 P) hq₁ hq₂]
    split_ifs
    · rfl
    · rcases hep : es.g.epMgmt Δ qep₂ P r.isSome with _ | s₁
      · rfl
      · obtain ⟨_, hs₁St, _, _⟩ := epMgmt_epoch_st_trans_win ⟨hBound.1, hBound.2.2⟩ hep
        have ht_le : (s₁.st P).tcur + 1 ≤ E + 1 := by
          rw [hs₁St]; exact Nat.add_le_add_right (hBound.2.1 P) 1
        simp only [run_liftH_bind']
        have hvSendEq : (vSend hk₁ s₁ P (s₁.st P) m none r).run es.h =
            (vSend hk₂ s₁ P (s₁.st P) m none r).run es.h := by
          unfold vSend; dsimp only
          simp only [hStartSend s₁ P ((s₁.st P).tcur + 1) _ _ r ht_le, hFsSend]
        rw [hvSendEq]
  · rfl
  · change (deliverE hk₁ maxSkip cfg (P, c)).run es = (deliverE hk₂ maxSkip cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hComEq]
    split_ifs
    · rfl
    · rcases es.g.inTransit P.other c with _ | rec_
      · rfl
      · simp only [run_liftH_bind', hvRecvEq P c (some rec_)]
  · change (injectE hk₁ Δ qep₁ cfg (P, c)).run es = (injectE hk₂ Δ qep₂ cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hComEq]
    split_ifs
    · rfl
    · simp only [run_liftH_bind', hvRecvEq P c none]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvr => ?_
      rcases vrRes with _ | (_ | ⟨st', t', i', m'⟩)
      · rfl
      · rfl
      · obtain ⟨ht'Eq, hcle0, _⟩ :=
          vRecv_tcur_and_epoch_le hk₂ es.g P (es.g.st P) c none es.h _ hvr st' t' i' m' rfl
        have ht' : t' ≤ E + 1 := ht'Eq ▸ hcle0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
        have h1 : ¬ (qep₁ + 1 < t') := by omega
        have h2 : ¬ (qep₂ + 1 < t') := by omega
        simp only [h1, h2, ↓reduceIte]
  · change (corrEPaperBucket hk₁ P).run es = (corrEPaperBucket hk₂ P).run es
    unfold corrEPaperBucket; rw [hReveal]
  · change (deliverForgeE hk₁ Δ qep₁ cfg (P, c, c')).run es =
        (deliverForgeE hk₂ Δ qep₂ cfg (P, c, c')).run es
    unfold deliverForgeE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hComEq]
    split_ifs
    · rfl
    · rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind', hvRecvEq P c' none]
          refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvr => ?_
          rcases vrRes with _ | (_ | ⟨st', t', i', m'⟩)
          · rfl
          · rfl
          · obtain ⟨ht'Eq, hcle0, _⟩ :=
              vRecv_tcur_and_epoch_le hk₂ es.g P (es.g.st P) c' none es.h _ hvr st' t' i' m' rfl
            have ht' : t' ≤ E + 1 := ht'Eq ▸ hcle0.trans (Nat.add_le_add_right (hBound.2.1 P) 1)
            have h1 : decide (qep₁ + 1 < t') = false := decide_eq_false (by omega)
            have h2 : decide (qep₂ + 1 < t') = false := decide_eq_false (by omega)
            simp only [h1, h2]

private theorem simulateQ_implEDFPaperBucketMode_noWin
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E_ct HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E_ct] [Inhabited E_ct]
    (hk : Hooks tspec HS Γ T Sig SS RS M E_ct CCoins Γv Sv SSv RSv)
    (hCom : ∀ ctx P old new, hk.commit ctx P old new = pure (some new))
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool)
    (hDW : cfg.deliverWin = false)
    {E rem : ℕ}
    (hNoInj : ∀ t', t' ≤ E + rem → cfg.injectFull t' = false)
    {α : Type}
    (A : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E_ct)) α)
    (hq : A.IsQueryBoundP (fun x => x.isRight = true) rem)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS) (winEp : Option ℕ)
    (hBound : EpochBound E es.g) (hWin : es.g.win = false) :
    ∀ res ∈ support ((simulateQ (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest) A).run
      (es, winEp)),
      res.2.1.g.win = false ∧ res.2.2 = winEp := by
  induction A using OracleComp.inductionOn generalizing E rem es winEp with
  | pure a =>
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨hWin, rfl⟩
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases hq with ⟨hq0, hmx⟩
    intro res hmem
    rw [simulateQ_query_bind, StateT.run_bind] at hmem
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq] at hmem
    rcases qy with n | t_df
    · simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hmx
      rw [mem_support_bind_iff] at hmem
      obtain ⟨⟨u, es', winEp'⟩, hstep, hmem⟩ := hmem
      have hStepDef :
          support ((liftM (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest (.inl n)) :
            StateT _ (TComp tspec) _).run (es, winEp)) =
          support ((implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest (.inl n)).run (es, winEp)) :=
        congrArg support rfl
      rw [hStepDef] at hstep
      simp only [withWinEpDFMode_inl_run, support_map, Set.mem_image] at hstep
      obtain ⟨_, _, hEq⟩ := hstep
      rcases Prod.mk.inj hEq with ⟨_, hStEq⟩
      rcases Prod.mk.inj hStEq with ⟨rfl, rfl⟩
      exact @ih u E rem hNoInj (hmx u) es winEp hBound hWin res hmem
    · simp only [Sum.isRight_inr, ↓reduceIte] at hmx
      obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 :=
        ⟨rem - 1, by have := hq0.resolve_left (by simp); omega⟩
      rw [mem_support_bind_iff] at hmem
      obtain ⟨⟨u, es', winEp'⟩, hstep, hmem⟩ := hmem
      have hStepDef :
          support ((liftM (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest (.inr t_df)) :
            StateT _ (TComp tspec) _).run (es, winEp)) =
          support ((withWinEpDFMode gMain isHonest (fun vp => vp.tcur)
            (implEDFPaperBucketRaw hk Δ qep maxSkip cfg) (.inr t_df)).run (es, winEp)) :=
        congrArg support rfl
      rw [hStepDef] at hstep
      obtain ⟨hraw, hwinEq⟩ := @mem_support_withWinEpDFMode_inr _ tspec
        (PartyState Γ T Sig SS RS) M CCoins T E_ct (VP Γv T Sv SSv RSv) HS
        gMain isHonest (fun vp => vp.tcur)
        (implEDFPaperBucketRaw hk Δ qep maxSkip cfg) t_df es es' winEp winEp' u hstep
      obtain ⟨hB', hNoWinStep⟩ := implEDFPaperBucketRaw_epochBound_and_noWin hk hCom Δ qep maxSkip
        E cfg es t_df hBound (u, es') hraw
      have hWin' : es'.g.win = false :=
        hNoWinStep hWin hDW (fun t' ht' => hNoInj t' (by omega))
      rw [hwinEq hWin'] at hmem
      exact @ih u (E + 1) rem' (fun t' ht' => hNoInj t' (by omega)) (by simpa using hmx u)
        es' winEp hB' hWin' res hmem

private theorem simulateQ_implEDFPaperBucketMode_qep_congr
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E_ct HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E_ct] [Inhabited E_ct]
    (hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E_ct CCoins Γv Sv SSv RSv)
    (hCom₂ : ∀ ctx P old new, hk₂.commit ctx P old new = pure (some new))
    (Δ qep₁ qep₂ maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool)
    {E rem : ℕ}
    (hq₁ : E + rem ≤ qep₁) (hq₂ : E + rem ≤ qep₂)
    (hStartSend : ∀ ctx P t0 γ σ r, t0 ≤ E + rem →
      hk₁.startSend ctx P t0 γ σ r = hk₂.startSend ctx P t0 γ σ r)
    (hStartRecv : ∀ ctx P t0 γ σ Tn, t0 ≤ E + rem →
      hk₁.startRecv ctx P t0 γ σ Tn = hk₂.startRecv ctx P t0 γ σ Tn)
    (hFsSend : hk₁.fsSend = hk₂.fsSend)
    (hFsRecv : hk₁.fsRecv = hk₂.fsRecv)
    (hCommit : hk₁.commit = hk₂.commit)
    (hReveal : hk₁.reveal = hk₂.reveal)
    {α : Type}
    (A : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E_ct)) α)
    (hq : A.IsQueryBoundP (fun x => x.isRight = true) rem)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E_ct) HS) (winEp : Option ℕ)
    (hBound : EpochBound E es.g) :
    (simulateQ (implEDFPaperBucketMode hk₁ Δ qep₁ maxSkip cfg gMain isHonest) A).run (es, winEp) =
      (simulateQ (implEDFPaperBucketMode hk₂ Δ qep₂ maxSkip cfg gMain isHonest) A).run (es, winEp) := by
  induction A using OracleComp.inductionOn generalizing E rem es winEp with
  | pure _ => rfl
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases hq with ⟨hq0, hmx⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_df
    · simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hmx
      change ((implEDFPaperBucketMode hk₁ Δ qep₁ maxSkip cfg gMain isHonest (.inl n)).run
          (es, winEp) >>= _) =
        ((implEDFPaperBucketMode hk₂ Δ qep₂ maxSkip cfg gMain isHonest (.inl n)).run
          (es, winEp) >>= _)
      rw [withWinEpDFMode_inl_run, withWinEpDFMode_inl_run, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u hq₁ hq₂ hStartSend hStartRecv (hmx u) es winEp hBound
    · simp only [Sum.isRight_inr, ↓reduceIte] at hmx
      obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 :=
        ⟨rem - 1, by have := hq0.resolve_left (by simp); omega⟩
      have hRawEq := implEDFPaperBucketRaw_qep_congr hk₁ hk₂ Δ qep₁ qep₂ maxSkip E cfg es t_df
        hBound (by omega) (by omega)
        (fun ctx P t0 γ σ r ht0 => hStartSend ctx P t0 γ σ r (by omega))
        (fun ctx P t0 γ σ Tn ht0 => hStartRecv ctx P t0 γ σ Tn (by omega))
        hFsSend hFsRecv hCommit hReveal
      have hStepEq := withWinEpDFMode_congr_of_raw_eq gMain isHonest (fun vp => vp.tcur)
        (implEDFPaperBucketRaw hk₁ Δ qep₁ maxSkip cfg)
        (implEDFPaperBucketRaw hk₂ Δ qep₂ maxSkip cfg)
        (.inr t_df) es winEp hRawEq
      change ((withWinEpDFMode gMain isHonest (fun vp => vp.tcur)
          (implEDFPaperBucketRaw hk₁ Δ qep₁ maxSkip cfg) (.inr t_df)).run (es, winEp) >>= _) =
        ((withWinEpDFMode gMain isHonest (fun vp => vp.tcur)
          (implEDFPaperBucketRaw hk₂ Δ qep₂ maxSkip cfg) (.inr t_df)).run (es, winEp) >>= _)
      rw [hStepEq]
      refine OracleComp.bind_congr_of_forall_mem_support
        ((withWinEpDFMode gMain isHonest (fun vp => vp.tcur)
          (implEDFPaperBucketRaw hk₂ Δ qep₂ maxSkip cfg) (.inr t_df)).run (es, winEp))
        fun ⟨u, es', winEp'⟩ hstep => ?_
      obtain ⟨hraw, _⟩ := @mem_support_withWinEpDFMode_inr _ tspec
        (PartyState Γ T Sig SS RS) M CCoins T E_ct (VP Γv T Sv SSv RSv) HS
        gMain isHonest (fun vp => vp.tcur)
        (implEDFPaperBucketRaw hk₂ Δ qep₂ maxSkip cfg) t_df es es' winEp winEp' u hstep
      obtain ⟨hB', _⟩ := implEDFPaperBucketRaw_epochBound_and_noWin hk₂ hCom₂ Δ qep₂ maxSkip
        E cfg es t_df hBound (u, es') hraw
      exact @ih u (E + 1) rem' (by omega) (by omega)
        (fun ctx P t0 γ σ r ht0 => hStartSend ctx P t0 γ σ r (by omega))
        (fun ctx P t0 γ σ Tn ht0 => hStartRecv ctx P t0 γ σ Tn (by omega))
        (by simpa using hmx u) es' winEp' hB'

private theorem inStage2Bucket_one_eq_false_of_lt_healEpoch
    (tL : Option ℕ) (par : Bool) (t' : ℕ)
    (hlt : t' < healEpoch tL) :
    inStage2Bucket 1 tL par t' = false := by
  rcases tL with _ | l
  · simp [healEpoch] at hlt
  · simp only [healEpoch] at hlt
    have hnot : ¬ (l + (3 + 1) ≤ t') := by omega
    simp [inStage2Bucket, lastLeakGuessAdmissible, hnot]

private theorem epochBound_zero_initCtx {Γv T Sv SSv RSv M E_ct : Type}
    (vA vB : VP Γv T Sv SSv RSv) (hvA : vA.tcur = 0) (hvB : vB.tcur = 0) (b : Bool) :
    EpochBound 0 ({ st := fun P => match P with | .A => vA | .B => vB, b := b } :
      Ctx Γv T Sv SSv RSv M E_ct) := by
  refine ⟨fun _ => le_rfl, fun P => ?_, fun _ hr => by cases hr⟩
  cases P <;> simp [hvA, hvB]

private theorem mem_support_initLocalBucket_tcur
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (h₀ : LocalBucketState T Sig K I) :
    ∀ p ∈ support ((initLocalBucket cka prng fs lam Δbucket qep tL par).run h₀),
      ∀ vA vB, p.1 = some (vA, vB) → vA.tcur = 0 ∧ vB.tcur = 0 := by
  intro ⟨vs, h⟩ hmem vA vB hEq
  dsimp only at hEq; subst hEq
  unfold initLocalBucket at hmem
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
  obtain ⟨_, _, _, _, ⟨⟨_, _⟩, _⟩, _, ⟨⟨rfl, rfl⟩, _⟩⟩ := hmem
  exact ⟨rfl, rfl⟩

private theorem mem_support_simulateQ_lImpl {α : Type}
    (oa : TComp CryptoGames.SM.Construction.AuthL11.nilSpec α) (x : α) :
    x ∈ support (simulateQ CryptoGames.SM.Construction.AuthL11.lImpl oa) ↔ x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind qy r ih =>
    rcases qy with t | e
    · have hrun : (liftM (CryptoGames.SM.Construction.AuthL11.lImpl (.inl t)) :
          ProbComp (unifSpec.Range t)) = liftM (OracleSpec.query t) := rfl
      rw [simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, hrun,
        mem_support_bind_iff, ih]
      exact ⟨fun ⟨u, _, hx⟩ => ⟨u, by simp, hx⟩, fun ⟨u, _, hx⟩ => ⟨u, by simp, hx⟩⟩
    · nomatch e

/-- When `q < healEpoch tL`, `q` DF queries cannot enter any active Stage-2 bucket epoch, so
`localAuthDFPaperBucketMode` outputs `true` with probability `0` (for both `gMain` modes). -/
theorem localAuthDFPaperBucketMode_evalDist_true_eq_zero_of_lt_healEpoch
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (q qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (hlt : q < healEpoch tL)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    𝒟[localAuthDFPaperBucketMode cka prng fs lam 1 qep gMain tL par A] {true} = 0 := by
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q :=
    hq.of_imp fun x hx => by cases x <;> cases hx; rfl
  have hRunEq : ∀ (gM : Bool) (hk : Hooks CryptoGames.SM.Construction.AuthL11.nilSpec
          (LocalBucketState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
      (hCom : ∀ ctx P old new, hk.commit ctx P old new = pure (some new)),
      (do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode hk (2 + 1) qep fs.maxSkip (bucketAuthCfg 1 tL par)
            gM isHonestHdrLocalBucket (initLocalBucket cka prng fs lam (3 + 1) qep tL par)
            {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + 1) tL st)) =
      (simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode hk (2 + 1) qep fs.maxSkip (bucketAuthCfg 1 tL par)
            gM isHonestHdrLocalBucket (initLocalBucket cka prng fs lam (3 + 1) qep tL par)
            {} false A) >>= fun _ => (pure false : ProbComp Bool)) := by
    intro gM hk hCom
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r hr => ?_
    rw [mem_support_simulateQ_lImpl] at hr
    unfold engRunDFPaperBucketMode at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨⟨vs, h₁⟩, hinit, hr⟩ := hr
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · rw [mem_support_bind_iff] at hr
      obtain ⟨res, hsim, hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      obtain ⟨hvA, hvB⟩ := mem_support_initLocalBucket_tcur cka prng fs lam (3 + 1) qep tL par
        {} (some (vA, vB), h₁) hinit vA vB rfl
      have hNW := simulateQ_implEDFPaperBucketMode_noWin hk hCom (2 + 1) qep fs.maxSkip
        (bucketAuthCfg 1 tL par) gM isHonestHdrLocalBucket rfl
        (E := 0) (rem := q)
        (fun t' ht' => inStage2Bucket_one_eq_false_of_lt_healEpoch tL par t' (by omega))
        A hq' ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ })
        none (epochBound_zero_initCtx vA vB hvA hvB false) rfl res hsim
      simp [authOutBucketPaper, authOutBucket, hNW.2]
  cases gMain
  · unfold localAuthDFPaperBucketMode localAuthDFPaperBucketSplit localAuthDFPaperBucketForgedHdr
    simp only [Bool.false_eq_true, ↓reduceIte]
    change 𝒟[do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketForgedHdr cka prng fs 1 qep tL par)
            (2 + 1) qep fs.maxSkip (bucketAuthCfg 1 tL par) false isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + 1) qep tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + 1) tL st)]
        {true} = 0
    rw [hRunEq false (hooksLocalBucketForgedHdr cka prng fs 1 qep tL par) (fun _ _ _ _ => rfl),
      evalDist_bind_const_probComp]
    simp
  · unfold localAuthDFPaperBucketMode localAuthDFPaperBucketSplit localAuthDFPaperBucketMain
    simp only [↓reduceIte]
    change 𝒟[do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketMain cka prng fs 1 qep tL par)
            (2 + 1) qep fs.maxSkip (bucketAuthCfg 1 tL par) true isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + 1) qep tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + 1) tL st)]
        {true} = 0
    rw [hRunEq true (hooksLocalBucketMain cka prng fs 1 qep tL par) (fun _ _ _ _ => rfl),
      evalDist_bind_const_probComp]
    simp

private theorem rootLocalBucket_qep_congr
    {KR Sig I K T : Type} [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket qep₁ qep₂ : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig)
    (ht₁ : t0 ≤ qep₁ + 1) (ht₂ : t0 ≤ qep₂ + 1) :
    (rootLocalBucket prng Δbucket qep₁ tL par t0 pl ik0 σ0 :
      HM CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketState T Sig K I) (Sig × K)) =
      rootLocalBucket prng Δbucket qep₂ tL par t0 pl ik0 σ0 := by
  unfold rootLocalBucket
  have h1 : ¬ (qep₁ + 1 < t0) := by omega
  have h2 : ¬ (qep₂ + 1 < t0) := by omega
  simp only [decide_eq_false h1, decide_eq_false h2]

/-- On any `q`-query DF adversary with `q ≤ qep₁` and `q ≤ qep₂`, `localAuthDFPaperBucketMode` is
independent of the epoch cap (`qep₁` vs `qep₂`). -/
theorem localAuthDFPaperBucketMode_qep_congr
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka q qep₁ qep₂ : ℕ)
    (hq₁ : q ≤ qep₁) (hq₂ : q ≤ qep₂)
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    localAuthDFPaperBucketMode cka prng fs lam Δcka qep₁ gMain tL par A =
      localAuthDFPaperBucketMode cka prng fs lam Δcka qep₂ gMain tL par A := by
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q :=
    hq.of_imp fun x hx => by cases x <;> cases hx; rfl
  have hInitEq : initLocalBucket cka prng fs lam (3 + Δcka) qep₁ tL par =
      initLocalBucket cka prng fs lam (3 + Δcka) qep₂ tL par := by
    unfold initLocalBucket
    simp only [rootLocalBucket_qep_congr prng (3 + Δcka) qep₁ qep₂ tL par 0 false lam _
      (Nat.zero_le _) (Nat.zero_le _)]
  have hEngEq : ∀ (gM : Bool) (hk₁ hk₂ : Hooks CryptoGames.SM.Construction.AuthL11.nilSpec
          (LocalBucketState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
      (hCom₂ : ∀ ctx P old new, hk₂.commit ctx P old new = pure (some new))
      (hSS : ∀ ctx P t0 γ σ r, t0 ≤ q → hk₁.startSend ctx P t0 γ σ r = hk₂.startSend ctx P t0 γ σ r)
      (hSR : ∀ ctx P t0 γ σ Tn, t0 ≤ q → hk₁.startRecv ctx P t0 γ σ Tn = hk₂.startRecv ctx P t0 γ σ Tn)
      (hFS : hk₁.fsSend = hk₂.fsSend) (hFR : hk₁.fsRecv = hk₂.fsRecv)
      (hCm : hk₁.commit = hk₂.commit) (hRv : hk₁.reveal = hk₂.reveal),
      engRunDFPaperBucketMode hk₁ (2 + Δcka) qep₁ fs.maxSkip (bucketAuthCfg Δcka tL par)
        gM isHonestHdrLocalBucket (initLocalBucket cka prng fs lam (3 + Δcka) qep₁ tL par)
        {} false A =
      engRunDFPaperBucketMode hk₂ (2 + Δcka) qep₂ fs.maxSkip (bucketAuthCfg Δcka tL par)
        gM isHonestHdrLocalBucket (initLocalBucket cka prng fs lam (3 + Δcka) qep₂ tL par)
        {} false A := by
    intro gM hk₁ hk₂ hCom₂ hSS hSR hFS hFR hCm hRv
    unfold engRunDFPaperBucketMode
    rw [hInitEq]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₁⟩ hinit => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · obtain ⟨hvA, hvB⟩ := mem_support_initLocalBucket_tcur cka prng fs lam (3 + Δcka) qep₂ tL par
        {} (some (vA, vB), h₁) hinit vA vB rfl
      have hSim := simulateQ_implEDFPaperBucketMode_qep_congr hk₁ hk₂ hCom₂
        (2 + Δcka) qep₁ qep₂ fs.maxSkip (bucketAuthCfg Δcka tL par) gM isHonestHdrLocalBucket
        (E := 0) (rem := q) (by omega) (by omega)
        (fun ctx P t0 γ σ r ht0 => hSS ctx P t0 γ σ r (by omega))
        (fun ctx P t0 γ σ Tn ht0 => hSR ctx P t0 γ σ Tn (by omega))
        hFS hFR hCm hRv A hq'
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ })
        none (epochBound_zero_initCtx vA vB hvA hvB false)
      exact congrArg (· >>= fun res => pure (some res)) hSim
  cases gMain
  · unfold localAuthDFPaperBucketMode localAuthDFPaperBucketSplit localAuthDFPaperBucketForgedHdr
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketForgedHdr cka prng fs Δcka qep₁ tL par)
            (2 + Δcka) qep₁ fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + Δcka) qep₁ tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + Δcka) tL st)) =
      (do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketForgedHdr cka prng fs Δcka qep₂ tL par)
            (2 + Δcka) qep₂ fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + Δcka) qep₂ tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + Δcka) tL st))
    rw [hEngEq false (hooksLocalBucketForgedHdr cka prng fs Δcka qep₁ tL par)
        (hooksLocalBucketForgedHdr cka prng fs Δcka qep₂ tL par)
        (fun _ _ _ _ => rfl)
        (fun ctx P t0 γ σ r ht0 => by
          simp only [hooksLocalBucketForgedHdr, hooksLocalBucket,
            rootLocalBucket_qep_congr prng (3 + Δcka) qep₁ qep₂ tL par t0 _ _ _
              (by omega) (by omega)])
        (fun ctx P t0 γ σ Tn ht0 => by
          have h1 : ¬ (qep₁ + 1 < t0) := by omega
          have h2 : ¬ (qep₂ + 1 < t0) := by omega
          simp only [hooksLocalBucketForgedHdr, hooksLocalBucket,
            decide_eq_false h1, decide_eq_false h2])
        rfl rfl rfl rfl]
  · unfold localAuthDFPaperBucketMode localAuthDFPaperBucketSplit localAuthDFPaperBucketMain
    simp only [↓reduceIte]
    change (do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketMain cka prng fs Δcka qep₁ tL par)
            (2 + Δcka) qep₁ fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + Δcka) qep₁ tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + Δcka) tL st)) =
      (do
        let r ← simulateQ CryptoGames.SM.Construction.AuthL11.lImpl
          (engRunDFPaperBucketMode (hooksLocalBucketMain cka prng fs Δcka qep₂ tL par)
            (2 + Δcka) qep₂ fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrLocalBucket
            (initLocalBucket cka prng fs lam (3 + Δcka) qep₂ tL par) {} false A)
        pure (match r with | none => false | some (_, st) => authOutBucketPaper (2 + Δcka) tL st))
    rw [hEngEq true (hooksLocalBucketMain cka prng fs Δcka qep₁ tL par)
        (hooksLocalBucketMain cka prng fs Δcka qep₂ tL par)
        (fun _ _ _ _ => rfl)
        (fun ctx P t0 γ σ r ht0 => by
          simp only [hooksLocalBucketMain, hooksLocalBucket,
            rootLocalBucket_qep_congr prng (3 + Δcka) qep₁ qep₂ tL par t0 _ _ _
              (by omega) (by omega)])
        (fun ctx P t0 γ σ Tn ht0 => by
          have h1 : ¬ (qep₁ + 1 < t0) := by omega
          have h2 : ¬ (qep₂ + 1 < t0) := by omega
          simp only [hooksLocalBucketMain, decide_eq_false h1, decide_eq_false h2])
        rfl rfl rfl rfl]

/-- Unconditional `qep + 1` → `min (qep + 1) (q + 11)` clamping equality for `localAuthDFPaperBucketMode`. -/
theorem localAuthDFPaperBucketMode_eq_min_qep
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka q qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    localAuthDFPaperBucketMode cka prng fs lam Δcka (qep + 1) gMain tL par A =
      localAuthDFPaperBucketMode cka prng fs lam Δcka (min (qep + 1) (q + 11)) gMain tL par A := by
  by_cases hle : qep + 1 ≤ q + 11
  · rw [Nat.min_eq_left hle]
  · exact localAuthDFPaperBucketMode_qep_congr cka prng fs lam Δcka q (qep + 1)
      (min (qep + 1) (q + 11)) (by omega) (by omega) gMain tL par A hq

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux
