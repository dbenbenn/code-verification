/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.GameProofDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.Monad.Bool

/-!
# Stage-2 `canon`-Bucketed Authenticity Game and Lemma 17 / First-Win Bridges

**Not trusted.** Additive Stage-2 bridge module partitioning the single first-win authenticity
event of `Config.h1` directly by `tL = canon tWin s ∈ admissibleLastLeakGuesses Δ (qep + 1)`
without overcounting multi-epoch forgers across separate `Config.auth t` runs.-/

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open CryptoGames (Party SMScheme)
open CryptoGames.SM (Adversary Config GameState Pos RecvResult admissibleLastLeakGuesses
  authLosingConditionsAvoided challImpl corrImpl deliverImpl game hybridAdvantage initState
  lastLeakGuessAdmissible run spec transmitImpl)
open CryptoGames.SM.Thm1 (challSim)

namespace CryptoGames.SM.BucketAuthBridge

public section

variable {Key St Msg Coins C : Type}

/-- Authenticity `Config` for a `tL`-bucket (`injectFull t' := lastLeakGuessAdmissible Δ tL t'`). -/
@[expose] def bucketCfg (Δ : ℕ) (tL : Option ℕ) : Config Msg where
  deliverWin := false
  injectFull := fun t' => lastLeakGuessAdmissible Δ tL t'
  challAllowedIn := fun _ => false
  challMsg := fun _ => none

/-- State of `bucketRun`: `GameState` paired with the first winning injection epoch `winEp`. -/
abbrev BucketState (St Msg C : Type) := GameState St Msg C × Option ℕ

/-- Lift a `StateT (GameState St Msg C) ProbComp` oracle step to `BucketState`, leaving `winEp`
unchanged. -/
@[expose] def liftGameStep {α : Type}
    (m : StateT (GameState St Msg C) ProbComp α) :
    StateT (BucketState St Msg C) ProbComp α :=
  StateT.mk fun (s, winEp) => do
    let (a, s') ← m.run s
    return (a, (s', winEp))

/-- `inject` oracle of `bucketAuthGame`: identical to `injectImpl` at `bucketCfg Δ tL`,
additionally recording `some t'` in `winEp` when `win` transitions from `false` to `true`. -/
@[expose] def bucketInjectImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (BucketState St Msg C) ProbComp) :=
  fun ⟨P, c⟩ => do
    let (s, winEp) ← get
    if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) then return none
    match sm.receive (s.st P) c with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' then return some .rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        set (s.accept P st' pos, winEp)
        return some (.accepted t' i' (some m'))
      else
        if lastLeakGuessAdmissible Δ tL t' then
          set ({ s with win := true }, some t')
        return some .rejected

/-- Full Fig. 2 oracle implementation for `bucketAuthGame`. -/
@[expose] def bucketOracleImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] :
    QueryImpl (spec St Msg Coins C) (StateT (BucketState St Msg C) ProbComp) :=
  let cfg : Config Msg := bucketCfg Δ tL
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (BucketState St Msg C) ProbComp) :=
    fun q => liftGameStep (transmitImpl sm Δ qep q)
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (BucketState St Msg C) ProbComp) :=
    fun q => liftGameStep (challImpl sm Δ qep cfg q)
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (BucketState St Msg C) ProbComp) :=
    fun q => liftGameStep (deliverImpl sm cfg q)
  let i₅ : QueryImpl (Party →ₒ Option St)
      (StateT (BucketState St Msg C) ProbComp) :=
    fun q => liftGameStep (corrImpl q)
  i₁ + i₂ + i₃ + bucketInjectImpl sm Δ qep tL + i₅

/-- Run `A` in the `tL`-bucketed authenticity game with hidden bit `b`. -/
@[expose] def bucketRun (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    (b : Bool) (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    ProbComp (Bool × BucketState St Msg C) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (BucketState St Msg C) ProbComp) + bucketOracleImpl sm Δ qep tL
  (simulateQ impl A).run (initState sm k b, none)

/-- Stage-2 `tL`-bucketed authenticity game: `A` wins on its first non-trivial accepted injection
in an epoch `tWin ≤ qep + 1` admissible for `tL`, provided `authLosingConditionsAvoided Δ tL tWin`
holds on the final state. -/
@[expose] def bucketAuthGame (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    ProbComp Bool := do
  let (_, (s, winEp)) ← bucketRun sm Δ qep tL false A
  return match winEp with
    | none => false
    | some tWin => s.win && authLosingConditionsAvoided Δ tL tWin s

/-- Win probability of `bucketAuthGame`. -/
@[expose] noncomputable def bucketAuthAdvantage (sm : SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (tL : Option ℕ) (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] : ℝ≥0∞ :=
  𝒟[bucketAuthGame sm Δ qep tL A] {true}

section BucketLemma17Helpers

open MeasureTheory (Measure lintegral_add_left lintegral_finsetSum' lintegral_mono)
open _root_.CryptoGames.SM (AdversaryComp Record canon corrQuery deliverQuery injectQuery
  transmitQuery)
open _root_.CryptoGames.SM.Thm1 (Mirror simChall simCoins simCorr simDeliver simImpl simInject
  simRun simSend simTransmit toMirror)
open _root_.CryptoGames.SM.Thm1L17 (StateT_run_lift WFState accept_wf afterCorr_wf
  authOK_of_nontrivial_inject authOK_toAuth authOK_with_win chall_step_h coins_step_h
  corrAllowed_eq_of_chall_in_trans corr_step_h deliver_step_h epMgmt_wf epMgmt_win
  eq_of_mem_support_fullImpl_of_win_true fullImpl inTransit_epoch_le_max inject_step_h
  pos_epoch_le_of_trivial record_wf samCoins toAuth toAuth_accept toAuth_afterCorr toAuth_epMgmt
  toAuth_inTransit toAuth_initState toAuth_record toAuth_safeInj toAuth_st toAuth_trivial
  toMirror_accept toMirror_afterCorr toMirror_b toMirror_epMgmt toMirror_inTransit
  toMirror_initState toMirror_record toMirror_safeCh transmit_step_h wfState_init)

private abbrev bucketFullImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] :
    QueryImpl (unifSpec + spec St Msg Coins C) (StateT (BucketState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (BucketState St Msg C) ProbComp) + bucketOracleImpl sm Δ qep tL

@[simp] private theorem liftGameStep_run {α : Type}
    (m : StateT (GameState St Msg C) ProbComp α) (s : GameState St Msg C) (w : Option ℕ) :
    (liftGameStep m).run (s, w) = (m.run s >>= fun z => pure (z.1, (z.2, w))) := by
  simp [liftGameStep, StateT.run]
  rfl

private theorem mem_admissibleLastLeakGuesses_of_le {Δ t₁ t₂ : ℕ} {tL : Option ℕ}
    (ht : t₁ ≤ t₂) (h : tL ∈ admissibleLastLeakGuesses Δ t₁) :
    tL ∈ admissibleLastLeakGuesses Δ t₂ := by
  unfold admissibleLastLeakGuesses at h ⊢
  cases tL with
  | none => simp
  | some l =>
    simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
      Option.some.injEq, exists_eq_right, false_or] at h ⊢
    omega

private theorem lastLeakGuessAdmissible_of_authOK {Δ t : ℕ} {tL : Option ℕ}
    {s : GameState St Msg C} (hok : authLosingConditionsAvoided Δ tL t s = true) :
    lastLeakGuessAdmissible Δ tL t = true := by
  unfold authLosingConditionsAvoided at hok
  revert hok
  cases lastLeakGuessAdmissible Δ tL t <;> simp

private lemma mem_support_liftM_bucket_run {σ α : Type} {p : ProbComp α} {s s' : σ} {a : α}
    (h : (a, s') ∈ support ((liftM p : StateT σ ProbComp α).run s)) : s' = s := by
  rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at h
  rcases h with ⟨_, _, h2⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h2
  exact h2.2

private theorem eq_of_mem_support_bucketFullImpl_of_win_true
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (t : (unifSpec + spec St Msg Coins C).Domain)
    {bs : BucketState St Msg C} (hwin : bs.1.win = true)
    {z : (unifSpec + spec St Msg Coins C).Range t × BucketState St Msg C}
    (hz : z ∈ support ((bucketFullImpl sm Δ qep tL t).run bs)) :
    z.2 = bs := by
  rcases bs with ⟨sa, w⟩
  dsimp only at hwin
  rcases t with n | ((((q | q) | q) | q) | q)
  · exact mem_support_liftM_bucket_run hz
  · change z ∈ support ((liftGameStep (transmitImpl sm Δ qep q)).run (sa, w)) at hz
    rw [liftGameStep_run, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa'⟩, h1, h2⟩
    have hsa' : sa' = sa :=
      eq_of_mem_support_fullImpl_of_win_true sm Δ qep (bucketCfg Δ tL)
        (.inr (.inl (.inl (.inl (.inl q))))) hwin h1
    subst hsa'
    simp only [support_pure, Set.mem_singleton_iff] at h2
    rw [h2]
  · change z ∈ support ((liftGameStep (challImpl sm Δ qep (bucketCfg Δ tL) q)).run (sa, w)) at hz
    rw [liftGameStep_run, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa'⟩, h1, h2⟩
    have hsa' : sa' = sa :=
      eq_of_mem_support_fullImpl_of_win_true sm Δ qep (bucketCfg Δ tL)
        (.inr (.inl (.inl (.inl (.inr q))))) hwin h1
    subst hsa'
    simp only [support_pure, Set.mem_singleton_iff] at h2
    rw [h2]
  · change z ∈ support ((liftGameStep (deliverImpl sm (bucketCfg Δ tL) q)).run (sa, w)) at hz
    rw [liftGameStep_run, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa'⟩, h1, h2⟩
    have hsa' : sa' = sa :=
      eq_of_mem_support_fullImpl_of_win_true sm Δ qep (bucketCfg Δ tL)
        (.inr (.inl (.inl (.inr q)))) hwin h1
    subst hsa'
    simp only [support_pure, Set.mem_singleton_iff] at h2
    rw [h2]
  · change z ∈ support ((bucketInjectImpl sm Δ qep tL q).run (sa, w)) at hz
    unfold bucketInjectImpl at hz
    simp [hwin] at hz
    rw [hz]
  · change z ∈ support ((liftGameStep (corrImpl q)).run (sa, w)) at hz
    rw [liftGameStep_run, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa'⟩, h1, h2⟩
    have hsa' : sa' = sa :=
      eq_of_mem_support_fullImpl_of_win_true sm Δ qep (bucketCfg Δ tL) (.inr (.inr q)) hwin h1
    subst hsa'
    simp only [support_pure, Set.mem_singleton_iff] at h2
    rw [h2]

private theorem eq_of_mem_support_simulateQ_bucket_of_win_true
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    {β : Type} (c : AdversaryComp St Msg Coins C β) :
    ∀ {bs : BucketState St Msg C} {z : β × BucketState St Msg C},
      bs.1.win = true →
      z ∈ support ((simulateQ (bucketFullImpl sm Δ qep tL) c).run bs) →
      z.2 = bs := by
  induction c using OracleComp.inductionOn with
  | pure a =>
    intro bs z _ hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t r ih =>
    intro bs z hwin hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, bs₁⟩, h₁, h₂⟩
    have hbs₁ : bs₁ = bs := eq_of_mem_support_bucketFullImpl_of_win_true sm Δ qep tL t hwin h₁
    subst hbs₁
    exact ih u hwin h₂

private theorem evalDist_simulateQ_bucket_eq_one_of_win_true
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    {β : Type} (c : AdversaryComp St Msg Coins C β)
    (f : β × BucketState St Msg C → ProbComp Bool)
    {bs : BucketState St Msg C} (hwin : bs.1.win = true)
    (hf : ∀ z : β × BucketState St Msg C, z.2 = bs → f z = pure true) :
    𝒟[(simulateQ (bucketFullImpl sm Δ qep tL) c).run bs >>= f] {true} = 1 := by
  have hcongr : 𝒟[(simulateQ (bucketFullImpl sm Δ qep tL) c).run bs >>= f] =
      𝒟[(simulateQ (bucketFullImpl sm Δ qep tL) c).run bs >>=
        fun _ => (pure true : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    rw [hf z (eq_of_mem_support_simulateQ_bucket_of_win_true sm Δ qep tL c hwin hz)]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

private theorem simulateQ_bucketFullImpl_liftM_run
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    {α : Type} (p : ProbComp α) (bs : BucketState St Msg C) :
    (simulateQ (bucketFullImpl sm Δ qep tL) (liftM p : AdversaryComp St Msg Coins C α)).run bs =
      p >>= fun a => pure (a, bs) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (bucketFullImpl sm Δ qep tL)
      ((liftM (OracleSpec.query (spec := unifSpec + spec St Msg Coins C) (.inl t)) :
          AdversaryComp St Msg Coins C _) >>=
        fun u => (liftM (k u) : AdversaryComp St Msg Coins C α))).run bs = _
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((liftM (OracleSpec.query (spec := unifSpec) t) :
        StateT (BucketState St Msg C) ProbComp _).run bs >>=
      fun z => (simulateQ (bucketFullImpl sm Δ qep tL) (liftM (k z.1))).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind, ih]

private def CloseByBucketSum (Δ qep : ℕ) (c1 c2 : ProbComp Bool)
    (cAuth : Option ℕ → ProbComp Bool) : Prop :=
  ∀ ev : Set Bool,
    𝒟[c1] ev ≤ 𝒟[c2] ev +
      ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1), 𝒟[cAuth tL] {true} ∧
    𝒟[c2] ev ≤ 𝒟[c1] ev +
      ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1), 𝒟[cAuth tL] {true}

private theorem closeByBucketSum_of_eq (Δ qep : ℕ) {c1 c2 : ProbComp Bool}
    {cAuth : Option ℕ → ProbComp Bool} (h : c1 = c2) :
    CloseByBucketSum Δ qep c1 c2 cAuth := by
  intro ev
  rw [h]
  exact ⟨le_self_add, le_self_add⟩

private theorem closeByBucketSum_of_evalDist_eq_one (Δ qep : ℕ) {c1 c2 : ProbComp Bool}
    {cAuth : Option ℕ → ProbComp Bool} {tL₀ : Option ℕ}
    (htL₀ : tL₀ ∈ admissibleLastLeakGuesses Δ (qep + 1))
    (hone : 𝒟[cAuth tL₀] {true} = 1) :
    CloseByBucketSum Δ qep c1 c2 cAuth := by
  intro ev
  have h1 : (1 : ℝ≥0∞) ≤
      ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1), 𝒟[cAuth tL] {true} := by
    calc (1 : ℝ≥0∞) = 𝒟[cAuth tL₀] {true} := hone.symm
      _ ≤ ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1), 𝒟[cAuth tL] {true} :=
        Finset.single_le_sum (f := fun tL => 𝒟[cAuth tL] {true}) (fun _ _ => zero_le) htL₀
  exact ⟨(MeasureTheory.prob_le_one.trans h1).trans le_add_self,
    (MeasureTheory.prob_le_one.trans h1).trans le_add_self⟩

private theorem closeByBucketSum_bind (Δ qep : ℕ) {α : Type} (oa : ProbComp α)
    {f1 f2 : α → ProbComp Bool} {fAuth : Option ℕ → α → ProbComp Bool}
    (h : ∀ a, CloseByBucketSum Δ qep (f1 a) (f2 a) (fun tL => fAuth tL a)) :
    CloseByBucketSum Δ qep (oa >>= f1) (oa >>= f2) (fun tL => oa >>= fAuth tL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    intro ev
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool, ∀ s : Set Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] s =
          ∫⁻ u, 𝒟[g u] s ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g s
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= f1) ev, h1 (fun u => k u >>= f2) ev]
    have hsum : (∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= fun x => k x >>= fAuth tL] {true}) =
        ∫⁻ u, (∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          𝒟[k u >>= fAuth tL] {true}) ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      rw [lintegral_finsetSum' _ (fun _ _ => Measurable.of_discrete.aemeasurable)]
      refine Finset.sum_congr rfl fun tL _ => ?_
      exact h1 (fun u => k u >>= fAuth tL) {true}
    rw [hsum, ← lintegral_add_left Measurable.of_discrete,
        ← lintegral_add_left Measurable.of_discrete]
    exact ⟨lintegral_mono fun u => (ih u ev).1, lintegral_mono fun u => (ih u ev).2⟩

private theorem closeByBucketSum_of_samCoins_const (Δ qep : ℕ) [SampleableType Coins]
    (r_opt : Option Coins) {c1 c2 : ProbComp Bool} {cAuth : Option ℕ → ProbComp Bool}
    (h : CloseByBucketSum Δ qep c1 c2 cAuth) :
    CloseByBucketSum Δ qep
      (samCoins r_opt >>= fun _ => c1) (samCoins r_opt >>= fun _ => c2) cAuth := by
  intro ev
  rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]
  exact h ev

private theorem simulateQ_sim_bucket_query_bind
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] {α : Type}
    (q : (unifSpec + spec St Msg Coins C).Domain)
    (r : (unifSpec + spec St Msg Coins C).Range q → AdversaryComp St Msg Coins C α)
    (m : Mirror Msg C) (bs : BucketState St Msg C) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simulateQ (simImpl Δ qep (fun _ => none) none)
        ((liftM (OracleSpec.query q) : AdversaryComp St Msg Coins C _) >>= r)).run m)).run bs =
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none q).run m)).run bs >>=
      fun z => (simulateQ (bucketFullImpl sm Δ qep tL)
        ((simulateQ (simImpl Δ qep (fun _ => none) none) (r z.1.1)).run z.1.2)).run z.2 := by
  rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]

private theorem coins_step_bucket
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (n : unifSpec.Domain) (s : GameState St Msg C) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none (.inl n)).run (toMirror s))).run (toAuth s, none) =
      (liftM (OracleSpec.query n) : ProbComp _) >>=
        fun u => pure ((u, toMirror s), (toAuth s, none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simCoins n).run (toMirror s))).run (toAuth s, none) = _
  unfold simCoins
  simp only [StateT_run_lift, simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure]
  change ((liftM (OracleSpec.query (spec := unifSpec) n) :
      StateT (BucketState St Msg C) ProbComp _).run (toAuth s, none) >>=
    fun z => (pure ((z.1, toMirror s), z.2) : ProbComp _)) = _
  rw [StateT.run_monadLift]
  simp

private theorem bucket_transmit_step
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (m_msg : Msg) (r_opt : Option Coins) (s : GameState St Msg C) :
    (bucketFullImpl sm Δ qep tL
      (.inr (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))))).run (s, none) =
      (fullImpl sm Δ qep (bucketCfg Δ tL)
        (.inr (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))))).run s >>=
          fun z => pure (z.1, (z.2, none)) := by
  change (liftGameStep (transmitImpl sm Δ qep ⟨P, m_msg, r_opt⟩)).run (s, none) = _
  rw [liftGameStep_run]
  rfl

private theorem bucket_deliver_step
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (c : C) (s : GameState St Msg C) :
    (bucketFullImpl sm Δ qep tL (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run (s, none) =
      (fullImpl sm Δ qep (bucketCfg Δ tL) (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run s >>=
        fun z => pure (z.1, (z.2, none)) := by
  change (liftGameStep (deliverImpl sm (bucketCfg Δ tL) ⟨P, c⟩)).run (s, none) = _
  rw [liftGameStep_run]
  rfl

private theorem bucket_corr_step
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (s : GameState St Msg C) :
    (bucketFullImpl sm Δ qep tL (.inr (.inr P))).run (s, none) =
      (fullImpl sm Δ qep (bucketCfg Δ tL) (.inr (.inr P))).run s >>=
        fun z => pure (z.1, (z.2, none)) := by
  change (liftGameStep (corrImpl P)).run (s, none) = _
  rw [liftGameStep_run]
  rfl

private theorem transmit_step_bucket
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (m_msg : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))))).run (toMirror s))).run
          (toAuth s, none) =
      samCoins r_opt >>= fun coins =>
        match s.epMgmt Δ qep P r_opt.isSome with
        | none => pure ((none, toMirror s), (toAuth s, none))
        | some s₁ =>
          let out := sm.send (s₁.st P) m_msg coins
          let rec_r : Record Msg C := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, out.2⟩
          let s' := s₁.record Δ P out.1 rec_r false
          pure ((some out.2, toMirror s'), (toAuth s', none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simTransmit Δ qep ⟨P, m_msg, r_opt⟩).run (toMirror s))).run (toAuth s, none) = _
  unfold simTransmit transmitQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [bucket_transmit_step, transmit_step_h sm Δ qep (bucketCfg Δ tL) P m_msg r_opt (toAuth s) hwin]
  simp only [bind_assoc, pure_bind]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  rw [toAuth_epMgmt, toMirror_epMgmt]
  cases hep : s.epMgmt Δ qep P r_opt.isSome with
  | none =>
    simp [Option.map]
  | some s₁ =>
    simp [Option.map, StateT.run_set]
    exact ⟨toMirror_record _ _ _ _ _ _, rfl⟩

private theorem chall_step_bucket_none
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hep : s.epMgmt Δ qep P r_opt.isSome = none) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run
          (toAuth s, none) =
      pure ((none, toMirror s), (toAuth s, none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run
      (toAuth s, none) = _
  unfold simChall
  simp [toMirror_epMgmt, hep]

private theorem chall_step_bucket_unsafe
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s s₁ : GameState St Msg C) (hep : s.epMgmt Δ qep P r_opt.isSome = some s₁)
    (hsafe : s₁.safeCh Δ P = false) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run
          (toAuth s, none) =
      pure ((none, toMirror s), (toAuth s, none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run
      (toAuth s, none) = _
  unfold simChall
  simp [toMirror_epMgmt, hep, hsafe]

private theorem chall_step_bucket_safe
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s s₁ : GameState St Msg C) (hwin : s.win = false)
    (hep : s.epMgmt Δ qep P r_opt.isSome = some s₁)
    (hsafe : s₁.safeCh Δ P = true) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run
          (toAuth s, none) =
      samCoins r_opt >>= fun coins =>
        let mb := if s.b then m₁ else m₀
        let out := sm.send (s₁.st P) mb coins
        let rec_r : Record Msg C := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, out.2⟩
        let s' := s₁.record Δ P out.1 rec_r true
        pure ((some out.2, toMirror s'), (toAuth s', none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run
      (toAuth s, none) = _
  unfold simChall simSend transmitQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, toMirror_epMgmt, hep, Option.map,
    toMirror_safeCh, hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT_run_lift,
    Option.getD_none, simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [bucket_transmit_step,
      transmit_step_h sm Δ qep (bucketCfg Δ tL) P (if (toMirror s).b then m₁ else m₀) r_opt
        (toAuth s) hwin]
  simp only [bind_assoc, pure_bind, toAuth_epMgmt, hep, Option.map]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  simp [StateT.run_set, toMirror_b]
  exact ⟨⟨rfl, toMirror_record _ _ _ _ _ _⟩, toAuth_record _ _ _ _ _ _⟩

private theorem deliver_step_bucket
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (c : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run (toMirror s))).run (toAuth s, none) =
      match s.inTransit P.other c with
      | none => pure ((none, toMirror s), (toAuth s, none))
      | some r =>
        match sm.receive (s.st P) c with
        | none => pure ((some .rejected, toMirror s), (toAuth s, none))
        | some (st', t', i', m') =>
          let s' := s.accept P st' r.pos
          pure ((some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
                 toMirror s'), (toAuth s', none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simDeliver ⟨P, c⟩).run (toMirror s))).run (toAuth s, none) = _
  unfold simDeliver deliverQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [bucket_deliver_step, deliver_step_h sm Δ qep (bucketCfg Δ tL) rfl P c (toAuth s) hwin]
  simp only [bind_assoc, pure_bind]
  rw [toAuth_inTransit, toMirror_inTransit, toAuth_st]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      simp [StateT.run_set, toAuth_accept]
      exact toMirror_accept _ _ _ _

private theorem corr_step_bucket
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (s : GameState St Msg C)
    (hwf : WFState Δ s) (hwin : s.win = false) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none (.inr (.inr P))).run (toMirror s))).run
        (toAuth s, none) =
      if !(s.corrAllowed P) then pure ((none, toMirror s), (toAuth s, none))
      else pure ((some (s.st P), toMirror (s.afterCorr P)), (toAuth (s.afterCorr P), none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simCorr P).run (toMirror s))).run (toAuth s, none) = _
  unfold simCorr corrQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [bucket_corr_step, corr_step_h sm Δ qep (bucketCfg Δ tL) P (toAuth s) hwin]
  simp only [bind_assoc, pure_bind]
  have hallow_eq : (toAuth s).corrAllowed P = s.corrAllowed P :=
    corrAllowed_eq_of_chall_in_trans P hwf.chall_in_trans rfl rfl rfl
  rw [hallow_eq]
  by_cases hallow : s.corrAllowed P = true <;>
    simp [hallow, StateT.run_set, toAuth_afterCorr, toMirror_afterCorr, toAuth_st]

private theorem bucketInject_step
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (c : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (bucketFullImpl sm Δ qep tL (.inr (.inl (.inr ⟨P, c⟩)))).run (s, none) =
      if (s.inTransit P.other c).isSome || !(s.safeInj Δ) then pure (none, (s, none))
      else
        match sm.receive (s.st P) c with
        | none => pure (some .rejected, (s, none))
        | some (st', t', i', m') =>
          if qep + 1 < t' then pure (some .rejected, (s, none))
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if s.trivial Δ pos then
              pure (some (.accepted t' i' (some m')), (s.accept P st' pos, none))
            else
              pure (some .rejected,
                if lastLeakGuessAdmissible Δ tL t' then ({ s with win := true }, some t')
                else (s, none)) := by
  change (bucketInjectImpl sm Δ qep tL ⟨P, c⟩).run (s, none) = _
  unfold bucketInjectImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  split
  · simp
  · cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      dsimp only
      split
      · simp
      · split
        · simp [StateT.run_set]
        · split <;> simp [StateT.run_set]

private theorem inject_step_bucket
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (P : Party) (c : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (bucketFullImpl sm Δ qep tL)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inr ⟨P, c⟩)))).run (toMirror s))).run (toAuth s, none) =
      if (s.inTransit P.other c).isSome || !(s.safeInj Δ) then
        pure ((none, toMirror s), (toAuth s, none))
      else
        match sm.receive (s.st P) c with
        | none => pure ((some .rejected, toMirror s), (toAuth s, none))
        | some (st', t', i', m') =>
          if qep + 1 < t' then pure ((some .rejected, toMirror s), (toAuth s, none))
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if s.trivial Δ pos then
              let s' := s.accept P st' pos
              pure ((some (.accepted t' i' (some m')), toMirror s'), (toAuth s', none))
            else
              pure ((some .rejected, toMirror s),
                if lastLeakGuessAdmissible Δ tL t' then ({ toAuth s with win := true }, some t')
                else (toAuth s, none)) := by
  change (simulateQ (bucketFullImpl sm Δ qep tL)
    ((simInject ⟨P, c⟩).run (toMirror s))).run (toAuth s, none) = _
  unfold simInject injectQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [bucketInject_step sm Δ qep tL P c (toAuth s) hwin]
  rw [toAuth_inTransit, toAuth_safeInj, toAuth_st]
  split
  · simp
  · cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      dsimp only
      split
      · simp
      · rw [toAuth_trivial]
        split
        · simp [StateT.run_set, toAuth_accept]
          exact toMirror_accept _ _ _ _
        · split <;> simp

private theorem closeByBucketSum_simulateQ
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] {α : Type}
    (oa : AdversaryComp St Msg Coins C α)
    (f1 f2 : α × GameState St Msg C → ProbComp Bool)
    (fAuth : Option ℕ → (α × Mirror Msg C) × BucketState St Msg C → ProbComp Bool)
    (hf12 : ∀ a s, s.win = false → f1 (a, s) = f2 (a, s))
    (hfAuth : ∀ t tL (z : (α × Mirror Msg C) × BucketState St Msg C),
      z.2.2 = some t → z.2.1.win = true →
      authLosingConditionsAvoided Δ tL t z.2.1 = true → fAuth tL z = pure true) :
    ∀ {s : GameState St Msg C},
      WFState Δ s → s.win = false →
      CloseByBucketSum Δ qep
        ((simulateQ (fullImpl sm Δ qep Config.h1) oa).run s >>= f1)
        ((simulateQ (fullImpl sm Δ qep Config.h2) oa).run s >>= f2)
        (fun tL =>
          (simulateQ (bucketFullImpl sm Δ qep tL)
            ((simulateQ (simImpl Δ qep (fun _ => none) none) oa).run (toMirror s))).run
              (toAuth s, none) >>= fAuth tL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _ hwin
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact closeByBucketSum_of_eq Δ qep (hf12 a s hwin)
  | query_bind q r ih =>
    intro s hwf hwin
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
    simp_rw [simulateQ_sim_bucket_query_bind sm Δ qep]
    rcases q with n | ((((⟨P, m_msg, r_opt⟩ | ⟨P, m₀, m₁, r_opt⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · rw [coins_step_h, coins_step_h]
      simp_rw [coins_step_bucket, bind_assoc, pure_bind]
      exact closeByBucketSum_bind Δ qep (liftM (OracleSpec.query n)) fun u => ih u hwf hwin
    · rw [transmit_step_h sm Δ qep Config.h1 P m_msg r_opt s hwin,
          transmit_step_h sm Δ qep Config.h2 P m_msg r_opt s hwin]
      simp_rw [transmit_step_bucket sm Δ qep _ P m_msg r_opt s hwin, bind_assoc]
      refine closeByBucketSum_bind Δ qep (samCoins r_opt) fun coins => ?_
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some s₁ =>
        simp only [pure_bind]
        have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
        have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
        have hwf' : WFState Δ (s₁.record Δ P (sm.send (s₁.st P) m_msg coins).1
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, (sm.send (s₁.st P) m_msg coins).2⟩ false) :=
          record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (by intro h; cases h)
        exact ih (some (sm.send (s₁.st P) m_msg coins).2) hwf' hs₁_win
    · rw [chall_step_h sm Δ qep Config.h1 rfl rfl P m₀ m₁ r_opt s hwin,
          chall_step_h sm Δ qep Config.h2 rfl rfl P m₀ m₁ r_opt s hwin]
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp_rw [chall_step_bucket_none sm Δ qep _ P m₀ m₁ r_opt s hep, bind_assoc, pure_bind]
        exact closeByBucketSum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
      | some s₁ =>
        by_cases hsafe : s₁.safeCh Δ P = true
        · simp_rw [chall_step_bucket_safe sm Δ qep _ P m₀ m₁ r_opt s s₁ hwin hep hsafe]
          simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          refine closeByBucketSum_bind Δ qep (samCoins r_opt) fun coins => ?_
          have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
          have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
          have hwf' : WFState Δ (s₁.record Δ P
              (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, if s.b then m₁ else m₀,
                (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2⟩ true) :=
            record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe)
          exact ih (some (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2) hwf' hs₁_win
        · have hsafeF : s₁.safeCh Δ P = false := Bool.eq_false_iff.mpr hsafe
          simp_rw [chall_step_bucket_unsafe sm Δ qep _ P m₀ m₁ r_opt s s₁ hep hsafeF]
          simp only [hsafeF, Bool.not_false, ↓reduceIte, bind_assoc, pure_bind]
          exact closeByBucketSum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
    · rw [deliver_step_h sm Δ qep Config.h1 rfl P c s hwin,
          deliver_step_h sm Δ qep Config.h2 rfl P c s hwin]
      simp_rw [deliver_step_bucket sm Δ qep _ P c s hwin]
      cases htr : s.inTransit P.other c with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some rec_r =>
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp only [pure_bind]
          have hwf' : WFState Δ (s.accept P st' rec_r.pos) :=
            accept_wf hwf (inTransit_epoch_le_max Δ hwf htr)
          exact ih (some (.accepted t' i' (if s.chall.contains rec_r.pos then none else some m')))
            hwf' hwin
    · rw [inject_step_h sm Δ qep Config.h1 P c s hwin,
          inject_step_h sm Δ qep Config.h2 P c s hwin]
      simp_rw [inject_step_bucket sm Δ qep _ P c s hwin]
      by_cases hguard : ((s.inTransit P.other c).isSome || !(s.safeInj Δ)) = true
      · simp only [hguard, ↓reduceIte, pure_bind]
        exact ih none hwf hwin
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hsafe : s.safeInj Δ = true := by
          revert hguard; cases (s.inTransit P.other c).isSome <;> cases s.safeInj Δ <;> simp
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          dsimp only
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, pure_bind]
            exact ih (some .rejected) hwf hwin
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, pure_bind]
              have hwf' : WFState Δ (s.accept P st' ⟨P.other, t', i'⟩) :=
                accept_wf hwf (pos_epoch_le_of_trivial hwf hsafe htriv)
              exact ih (some (.accepted t' i' (some m'))) hwf' hwin
            · have htrivF : s.trivial Δ ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
              simp only [htrivF, Bool.false_eq_true, ↓reduceIte, pure_bind]
              have ht'_le : t' ≤ qep + 1 := by omega
              have ⟨hok, htL_t'⟩ := authOK_of_nontrivial_inject hΔ hwf htrivF
              have htL : canon t' s ∈ admissibleLastLeakGuesses Δ (qep + 1) :=
                mem_admissibleLastLeakGuesses_of_le ht'_le htL_t'
              refine closeByBucketSum_of_evalDist_eq_one Δ qep htL ?_
              have hadm : lastLeakGuessAdmissible Δ (canon t' s) t' = true :=
                lastLeakGuessAdmissible_of_authOK hok
              rw [hadm]
              simp only [↓reduceIte]
              refine evalDist_simulateQ_bucket_eq_one_of_win_true sm Δ qep (canon t' s)
                ((simulateQ (simImpl Δ qep (fun _ => none) none) (r (some .rejected))).run
                  (toMirror s))
                (fAuth (canon t' s)) rfl ?_
              intro z hz
              apply hfAuth t' (canon t' s) z
              · rw [hz]
              · rw [hz]
              · rw [hz, authOK_with_win, authOK_toAuth]
                exact hok
    · rw [corr_step_h sm Δ qep Config.h1 P s hwin,
          corr_step_h sm Δ qep Config.h2 P s hwin]
      simp_rw [corr_step_bucket sm Δ qep _ P s hwf hwin]
      by_cases hallow : s.corrAllowed P = true
      · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact ih (some (s.st P)) (afterCorr_wf hΔ hwf hallow) hwin
      · have hallowF : s.corrAllowed P = false := Bool.eq_false_iff.mpr hallow
        simp only [hallowF, Bool.not_false, ↓reduceIte, pure_bind]
        exact ih none hwf hwin

private theorem bucketAuthGame_challSim_evalDist
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    𝒟[bucketAuthGame sm Δ qep tL (challSim Δ qep A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
        (simulateQ (bucketFullImpl sm Δ qep tL)
          ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
            (toMirror (initState sm k b)))).run (toAuth (initState sm k b), none) >>=
          fun z => pure (match z.2.2 with
            | none => false
            | some tWin => z.2.1.win && authLosingConditionsAvoided Δ tL tWin z.2.1)] := by
  unfold bucketAuthGame bucketRun challSim simRun
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool)
    ($ᵗ Bool : ProbComp Bool) ($ᵗ Key : ProbComp Key)]
  refine congrArg evalDist (congrArg (($ᵗ Key : ProbComp Key) >>= ·) (funext fun k => ?_))
  simp only [StateT.run', map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_bucketFullImpl_liftM_run]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, toMirror_initState, toAuth_initState]
  rfl

private theorem closeByBucketSum_h1_h2
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    CloseByBucketSum Δ qep
      (game sm Δ qep Config.h1 A)
      (game sm Δ qep Config.h2 A)
      (fun tL => bucketAuthGame sm Δ qep tL (challSim Δ qep A)) := by
  let f (b : Bool) : Bool × GameState St Msg C → ProbComp Bool :=
    fun z => pure (b == z.1 || z.2.win)
  let fAuth (tL : Option ℕ) :
      (Bool × Mirror Msg C) × BucketState St Msg C → ProbComp Bool :=
    fun z => pure (match z.2.2 with
      | none => false
      | some tWin => z.2.1.win && authLosingConditionsAvoided Δ tL tWin z.2.1)
  have hclose : CloseByBucketSum Δ qep
      (game sm Δ qep Config.h1 A)
      (game sm Δ qep Config.h2 A)
      (fun tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (bucketFullImpl sm Δ qep tL)
            ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
              (toMirror (initState sm k b)))).run (toAuth (initState sm k b), none) >>=
            fAuth tL) := by
    unfold game run
    simp only [bind_assoc]
    refine closeByBucketSum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      closeByBucketSum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact closeByBucketSum_simulateQ sm Δ qep hΔ A (f b) (f b) fAuth
      (fun _ _ _ => rfl)
      (fun t tL z hwep hwin hok => by simp [fAuth, hwep, hwin, hok])
      (wfState_init sm Δ k b) rfl
  intro ev
  have htr := hclose ev
  dsimp only [fAuth] at htr
  simp_rw [← bucketAuthGame_challSim_evalDist sm Δ qep _ A] at htr
  exact htr

private theorem closeByBucketSum_win_false
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    CloseByBucketSum Δ qep
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        run sm Δ qep Config.h1 b A >>= fun (_, s) => pure s.win)
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        run sm Δ qep Config.h2 b A >>= fun _ => pure false)
      (fun tL => bucketAuthGame sm Δ qep tL (challSim Δ qep A)) := by
  let f1 : Bool × GameState St Msg C → ProbComp Bool := fun (_, s) => pure s.win
  let f2 : Bool × GameState St Msg C → ProbComp Bool := fun _ => pure false
  let fAuth (tL : Option ℕ) :
      (Bool × Mirror Msg C) × BucketState St Msg C → ProbComp Bool :=
    fun z => pure (match z.2.2 with
      | none => false
      | some tWin => z.2.1.win && authLosingConditionsAvoided Δ tL tWin z.2.1)
  have hclose : CloseByBucketSum Δ qep
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        run sm Δ qep Config.h1 b A >>= f1)
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        run sm Δ qep Config.h2 b A >>= f2)
      (fun tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (bucketFullImpl sm Δ qep tL)
            ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
              (toMirror (initState sm k b)))).run (toAuth (initState sm k b), none) >>=
            fAuth tL) := by
    unfold run
    simp only [bind_assoc]
    refine closeByBucketSum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      closeByBucketSum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact closeByBucketSum_simulateQ sm Δ qep hΔ A f1 f2 fAuth
      (fun _ _ hwin => by simp [f1, f2, hwin])
      (fun t tL z hwep hwin hok => by simp [fAuth, hwep, hwin, hok])
      (wfState_init sm Δ k b) rfl
  intro ev
  have htr := hclose ev
  dsimp only [f1, f2, fAuth] at htr
  simp_rw [← bucketAuthGame_challSim_evalDist sm Δ qep _ A] at htr
  exact htr

end BucketLemma17Helpers

/-- Stage-2 `canon`-bucket Lemma 17 (`H1 → H2`): bounds the `H1`/`H2` advantage gap by twice the
sum of `bucketAuthAdvantage` over `tL ∈ admissibleLastLeakGuesses Δ (qep + 1)`. -/
theorem lemma17_bucket (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    hybridAdvantage sm Δ qep Config.h1 A ≤
      hybridAdvantage sm Δ qep Config.h2 A +
        2 * ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) := by
  have htr := closeByBucketSum_h1_h2 sm Δ qep hΔ A {true}
  change 𝒟[game sm Δ qep Config.h1 A] {true} ≤
      𝒟[game sm Δ qep Config.h2 A] {true} +
        ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) ∧
    𝒟[game sm Δ qep Config.h2 A] {true} ≤
      𝒟[game sm Δ qep Config.h1 A] {true} +
        ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) at htr
  have hdiff : ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true})
      (𝒟[game sm Δ qep Config.h2 A] {true}) ≤
      ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
        bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) :=
    ENNReal.absDiff_le_iff.mpr htr
  have htri : ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true}) (1 / 2) ≤
      ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) +
        ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) := by
    calc ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true}) (1 / 2)
        ≤ ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true})
            (𝒟[game sm Δ qep Config.h2 A] {true}) +
          ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ (∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
            bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A)) +
          ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) := by gcongr
      _ = ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) +
          ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
            bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) := add_comm _ _
  unfold hybridAdvantage
  rw [MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

/-- Mixture (`oa : ProbComp α`) Stage-2 `canon`-bucket Lemma 17 (`H1 → H2`). -/
theorem lemma17_bucket_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (hΔ : 0 < Δ) (oa : ProbComp α) (A : α → Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    𝒟[oa >>= fun o => game (sm o) Δ qep Config.h1 (A o)].boolBias ≤
      𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)].boolBias +
        2 * ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
          𝒟[oa >>= fun o => bucketAuthGame (sm o) Δ qep tL
            (challSim Δ qep (A o))] {true} := by
  have hclose := closeByBucketSum_bind Δ qep oa
    (f1 := fun o => game (sm o) Δ qep Config.h1 (A o))
    (f2 := fun o => game (sm o) Δ qep Config.h2 (A o))
    (fAuth := fun tL o => bucketAuthGame (sm o) Δ qep tL (challSim Δ qep (A o)))
    fun o => closeByBucketSum_h1_h2 (sm o) Δ qep hΔ (A o)
  set S := ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
    𝒟[oa >>= fun o => bucketAuthGame (sm o) Δ qep tL (challSim Δ qep (A o))] {true}
  set μ1 := 𝒟[oa >>= fun o => game (sm o) Δ qep Config.h1 (A o)]
  set μ2 := 𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)]
  have hdiff : ENNReal.absDiff (μ1 {true}) (μ2 {true}) ≤ S :=
    ENNReal.absDiff_le_iff.mpr (hclose {true})
  have htri : ENNReal.absDiff (μ1 {true}) (1 / 2) ≤ ENNReal.absDiff (μ2 {true}) (1 / 2) + S := by
    calc ENNReal.absDiff (μ1 {true}) (1 / 2)
        ≤ ENNReal.absDiff (μ1 {true}) (μ2 {true}) + ENNReal.absDiff (μ2 {true}) (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ S + ENNReal.absDiff (μ2 {true}) (1 / 2) := by gcongr
      _ = _ := add_comm _ _
  rw [MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

/-- Stage-2 `canon`-bucket bound on the `Config.h1` `s.win` probability (bucketed counterpart of
`CryptoGames.LibsignalSM.Proofs.Refinement.run_win_prob_le_auth`). -/
theorem run_win_prob_le_bucketAuth (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : Adversary St Msg Coins C)
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      run sm Δ qep Config.h1 b A >>= fun (_, s) => pure s.win] {true} ≤
      ∑ tL ∈ admissibleLastLeakGuesses Δ (qep + 1),
        bucketAuthAdvantage sm Δ qep tL (challSim Δ qep A) := by
  have h1 := (closeByBucketSum_win_false sm Δ qep hΔ A {true}).1
  have hfalse : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      run sm Δ qep Config.h2 b A >>= fun _ => (pure false : ProbComp Bool)] {true} = 0 := by
    have hcongr : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        run sm Δ qep Config.h2 b A >>= fun _ => (pure false : ProbComp Bool)] =
        𝒟[($ᵗ Bool : ProbComp Bool) >>= fun _ => (pure false : ProbComp Bool)] := by
      refine evalDist_bind_congr_of_support _ _ _ fun b _ => ?_
      exact OracleComp.evalDist_bind_const _ _
    rw [hcongr, OracleComp.evalDist_bind_const]
    simp
  rw [hfalse, zero_add] at h1
  exact h1

end

end CryptoGames.SM.BucketAuthBridge
