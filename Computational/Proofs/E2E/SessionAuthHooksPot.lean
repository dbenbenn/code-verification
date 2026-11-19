/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperTMinusFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import

/-!
# Branch-Sensitive Monadic Potential Bound (`PotBound`) & Shallow `Hooks` Combinators

Provides `PotBound`, generic `simulateQ` potential/invariant combinators, and `ShallowHooksPot`
one-step potential preservation lemmas for `implEDFShiftedPaperGen`, `implEDFPaper`, and
`implEDFPaperBucketRaw`.-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthHooksPot

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM (Config specDF)
open _root_.CryptoGames.SM.Engine (Hooks Policy EState VP Ctx HM TComp liftH abortE
  coinsE vSend vRecv commitE transmitE challE deliverE injectE injectEGen deliverForgeEGen)
open _root_.CryptoGames.SM.Construction (PartyState Header Mode)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  implEDFPaper implEDFShiftedPaperGen implEDFPaperBucketRaw
  transmitEBucket challEBucket corrEPaperBucket corrEPaper corrEShiftedPaper
  deliverForgeE deliverForgeEB1 injectEB1 withWinEpDF)

/-! ## 1. Branch-Sensitive Monadic Potential Bound (`PotBound`) -/

section PotBound

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- `PotBound P post oa n` asserts that along every execution path of `oa`, `P`-queries never
exceed budget `n` and at least `post a` budget remains at every leaf `a`. -/
inductive PotBound {α : Type} (P : spec.Domain → Bool) (post : α → ℕ) :
    OracleComp spec α → ℕ → Prop where
  | pure {a : α} {n : ℕ} (h : post a ≤ n) : PotBound P post (Pure.pure a) n
  | query_bind {t : spec.Domain} {k : spec.Range t → OracleComp spec α} {n : ℕ}
      (ht : P t = false ∨ 0 < n)
      (hk : ∀ y, PotBound P post (k y) (if P t then n - 1 else n)) :
      PotBound P post (liftM (OracleSpec.query t) >>= k) n

theorem PotBound.mono {α : Type} {P : spec.Domain → Bool} {post₁ post₂ : α → ℕ}
    {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h : PotBound P post₁ oa n₁) (hpost : ∀ a, post₂ a ≤ post₁ a) (hn : n₁ ≤ n₂) :
    PotBound P post₂ oa n₂ := by
  induction h generalizing n₂ with
  | pure ha => exact PotBound.pure ((hpost _).trans (ha.trans hn))
  | query_bind ht _ ih =>
    refine PotBound.query_bind (ht.imp id fun h0 => Nat.lt_of_lt_of_le h0 hn) fun y => ?_
    exact ih y (by split_ifs <;> omega)

theorem PotBound.bind {α β : Type} {P : spec.Domain → Bool}
    {mid : α → ℕ} {post : β → ℕ} {mx : OracleComp spec α} {f : α → OracleComp spec β} {n : ℕ}
    (h : PotBound P mid mx n) (hf : ∀ a m, mid a ≤ m → PotBound P post (f a) m) :
    PotBound P post (mx >>= f) n := by
  induction h with
  | pure ha =>
    rw [pure_bind]
    exact hf _ _ ha
  | query_bind ht _ ih =>
    rw [bind_assoc]
    exact PotBound.query_bind ht ih

theorem PotBound.map {α β : Type} {P : spec.Domain → Bool}
    {mid : α → ℕ} {post : β → ℕ} {mx : OracleComp spec α} {g : α → β} {n : ℕ}
    (h : PotBound P mid mx n) (hg : ∀ a, post (g a) ≤ mid a) :
    PotBound P post (g <$> mx) n := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a m hm => PotBound.pure ((hg a).trans hm)

theorem PotBound.query_zero {P : spec.Domain → Bool} {t : spec.Domain} (n : ℕ)
    (ht : P t = false) : PotBound P (fun _ => n) (query (spec := spec) t) n := by
  have hq : (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) >>= Pure.pure := by
    rw [show (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) from rfl, bind_pure]
  rw [hq]
  exact PotBound.query_bind (Or.inl ht) fun _ => PotBound.pure (by simp [ht])

theorem PotBound.query_le_one {P : spec.Domain → Bool} {t : spec.Domain} {m n : ℕ}
    (h : m + 1 ≤ n) : PotBound P (fun _ => m) (query (spec := spec) t) n := by
  have hq : (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) >>= Pure.pure := by
    rw [show (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) from rfl, bind_pure]
  rw [hq]
  exact PotBound.query_bind (Or.inr (by omega)) fun _ => PotBound.pure (by split_ifs <;> omega)

theorem PotBound.to_isQueryBoundP {α : Type} {P : spec.Domain → Bool} {post : α → ℕ}
    {oa : OracleComp spec α} {n : ℕ} (h : PotBound P post oa n) :
    oa.IsQueryBoundP (fun x => P x = true) n := by
  induction h with
  | pure _ => exact isQueryBoundP_pure _ _ _
  | query_bind ht _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨ht.imp (by simp) id, fun y => by simpa using ih y⟩

theorem PotBound.of_zero_queries {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {P : (unifSpec + spec₀).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    (oa : ProbComp α) (n : ℕ) :
    PotBound P (fun _ => n) (liftM oa : OracleComp (unifSpec + spec₀) α) n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    change PotBound P (fun _ => n) (Pure.pure a) n
    exact PotBound.pure le_rfl
  | query_bind t k ih =>
    change PotBound P (fun _ => n)
      ((query (spec := unifSpec + spec₀) (.inl t)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + spec₀) α)) n
    exact (PotBound.query_zero n (hInl t)).bind fun u m hm =>
      (ih u).mono (fun _ => le_rfl) hm

end PotBound

/-! ## 2. Generic Engine `PotBound` Combinators -/

section EnginePot

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}

theorem potBound_simulateQ_run {S α : Type}
    (P : (unifSpec + spec₂).Domain → Bool)
    (pot : S → ℕ)
    (impl : QueryImpl (unifSpec + spec₁) (StateT S (OracleComp (unifSpec + spec₂))))
    (hInl : ∀ (u : unifSpec.Domain) (st : S) (rem : ℕ),
      PotBound P (fun z => rem + pot z.2) ((impl (.inl u)).run st) (rem + pot st))
    (hInr : ∀ (qr : spec₁.Domain) (st : S) (rem : ℕ),
      PotBound P (fun z => rem + pot z.2) ((impl (.inr qr)).run st) (rem + 1 + pot st)) :
    ∀ (q : ℕ) (oa : OracleComp (unifSpec + spec₁) α)
      (_hq : oa.IsQueryBoundP (fun x => x.isRight = true) q) (st : S),
      PotBound P (fun z => pot z.2) ((simulateQ impl oa).run st) (q + pot st) := by
  intro q oa
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a =>
    intro _ st
    exact PotBound.pure (Nat.le_add_left (pot st) q)
  | query_bind t k ih =>
    intro hq st
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases t with u | qr
    · exact (hInl u st q).bind fun z m hm =>
        (ih z.1 q (hq.2 z.1) z.2).mono (fun _ => le_rfl) hm
    · rcases q with _ | q'
      · simp at hq
      · have hstep := (hInr qr st q').mono (fun _ => le_rfl) (show q' + 1 + pot st ≤ (q' + 1) + pot st by omega)
        exact hstep.bind fun z m hm =>
          (ih z.1 q' (hq.2 z.1) z.2).mono (fun _ => le_rfl) hm

theorem isQueryBoundP_simulateQ_run_of_zero_inr {S α : Type}
    (P : (unifSpec + spec₂).Domain → Bool)
    (impl : QueryImpl (unifSpec + spec₁) (StateT S (OracleComp (unifSpec + spec₂))))
    (hInl : ∀ (u : unifSpec.Domain) (st : S),
      ((impl (.inl u)).run st).IsQueryBoundP (fun x => P x = true) 0)
    (oa : OracleComp (unifSpec + spec₁) α)
    (hq : oa.IsQueryBoundP (fun x => x.isRight = true) 0) :
    ∀ (st : S), ((simulateQ impl oa).run st).IsQueryBoundP (fun x => P x = true) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _
    exact isQueryBoundP_pure _ _ 0
  | query_bind t k ih =>
    intro st
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases t with u | _
    · exact (isQueryBoundP_bind (hInl u st) fun z _ => ih z.1 (hq.2 z.1) z.2).mono (by omega)
    · simp at hq

end EnginePot

/-! ## 3. Generic Shallow `Hooks` Potential Specification -/

section HooksPot

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι}
  {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}

structure ShallowHooksPot
    (P : (unifSpec + tspec).Domain → Bool)
    (pot : HS → ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) : Prop where
  inl_false : ∀ u, P (.inl u) = false
  startSend_pot : ∀ ctx Pt t γ σ r h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.startSend ctx Pt t γ σ r).run h) (rem + pot h)
  startRecv_pot : ∀ ctx Pt t γ σ Tn h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.startRecv ctx Pt t γ σ Tn).run h) (rem + pot h)
  fsSend_pot : ∀ ctx Pt t ssv hdr m pair h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.fsSend ctx Pt t ssv hdr m pair).run h) (rem + 1 + pot h)
  fsRecv_pot : ∀ ctx Pt t rsv hdr e rec h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.fsRecv ctx Pt t rsv hdr e rec).run h) (rem + 1 + pot h)
  commit_pot : ∀ ctx Pt old new h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.commit ctx Pt old new).run h) (rem + pot h)
  reveal_pot : ∀ ctx Pt vp h rem,
    PotBound P (fun z => rem + pot z.2) ((hk.reveal ctx Pt vp).run h) (rem + 1 + pot h)

private theorem liftH_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ} {α : Type}
    {x : HM tspec HS α} {es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {rem b : ℕ}
    (hx : PotBound P (fun z => rem + pot z.2) (x.run es.h) b) :
    PotBound P (fun z => rem + pot z.2.h) ((liftH x).run es) b := by
  unfold liftH
  exact hx.bind fun ⟨a, h'⟩ m hm => PotBound.pure (by dsimp only at hm ⊢; exact hm)

theorem coinsE_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    (hInl : ∀ u, P (.inl u) = false) (u : unifSpec.Domain)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((coinsE u).run es) (rem + pot es.h) := by
  unfold coinsE
  rw [StateT.run_lift]
  exact (PotBound.query_zero (rem + pot es.h) (hInl u)).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem commitE_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk)
    (ctx : Ctx Γv T Sv SSv RSv M E) (Pt : Party) (old new : VP Γv T Sv SSv RSv)
    (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((commitE hk ctx Pt old new pos).run es) (rem + pot es.h) := by
  unfold commitE
  rw [StateT.run_bind]
  refine (liftH_pot (hSpec.commit_pot _ Pt old new es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
  cases o with
  | none =>
    simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
  | some new' =>
    simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem vSend_pot [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk)
    (ctx : Ctx Γv T Sv SSv RSv M E) (Pt : Party) (s : VP Γv T Sv SSv RSv)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2) ((vSend hk ctx Pt s m pair r).run h) (rem + 1 + pot h) := by
  unfold vSend
  dsimp only
  split
  · simp only [StateT.run_bind, pure_bind]
    refine (hSpec.startSend_pot ctx Pt (s.tcur + 1) s.γ s.root r h (rem + 1)).bind fun ⟨o, h1⟩ k hk => ?_
    rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only at hk ⊢; omega)
    · simp only [StateT.run_bind]
      refine ((hSpec.fsSend_pot ctx Pt (s.tcur + 1) ss (s.tcur + 1, some T') m pair h1 rem).mono
        (fun _ => le_rfl) (by dsimp only at hk; omega)).bind fun ⟨o2, h2⟩ k2 hk2 => ?_
      cases o2 <;> simp only [StateT.run_pure] <;>
        exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
  · simp only [pure_bind]
    cases s.vS with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some v =>
      simp only [StateT.run_bind]
      refine (hSpec.fsSend_pot ctx Pt s.tcur v (s.tcur, s.curCkaMsg) m pair h rem).bind fun ⟨o2, h2⟩ k2 hk2 => ?_
      cases o2 <;> simp only [StateT.run_pure] <;>
        exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)

private theorem vRecv_pot [DecidableEq T] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk)
    (ctx : Ctx Γv T Sv SSv RSv M E) (Pt : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2) ((vRecv hk ctx Pt s c rec).run h) (rem + 1 + pot h) := by
  unfold vRecv
  dsimp only
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · split
    · cases c.1.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only; omega)
      | some Tn =>
        simp only [StateT.run_bind, pure_bind]
        refine (hSpec.startRecv_pot ctx Pt c.1.1 s.γ s.root Tn h (rem + 1)).bind fun ⟨o, h1⟩ k hk => ?_
        rcases o with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hk ⊢; omega)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hk ⊢; omega)
        · simp only [StateT.run_bind, Function.update_self]
          refine ((hSpec.fsRecv_pot ctx Pt c.1.1 rs c.1 c.2 rec h1 rem).mono
            (fun _ => le_rfl) (by dsimp only at hk; omega)).bind fun ⟨o2, h2⟩ k2 hk2 => ?_
          rcases o2 with _ | (_ | _) <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
    · simp only [pure_bind]
      cases s.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only; omega)
      | some v =>
        simp only [StateT.run_bind]
        refine (hSpec.fsRecv_pot ctx Pt c.1.1 v c.1 c.2 rec h rem).bind fun ⟨o2, h2⟩ k2 hk2 => ?_
        rcases o2 with _ | (_ | _) <;> simp only [StateT.run_pure] <;>
          exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)

private theorem transmitE_pot [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep : ℕ) (π : Policy)
    (q : Party × M × Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((transmitE hk Δ qep π q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, m, r⟩
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact PotBound.pure (by dsimp only; omega)
  · cases es.g.epMgmt Δ qep Pt r.isSome with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some s1 =>
      dsimp only
      split
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only; omega)
      · rw [StateT.run_bind]
        refine (liftH_pot (vSend_pot hSpec s1 Pt (s1.st Pt) m none r es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
        cases o with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
        | some p =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem transmitEBucket_pot [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep : ℕ)
    (q : Party × M × Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((transmitEBucket hk Δ qep q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, m, r⟩
  unfold transmitEBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact PotBound.pure (by dsimp only; omega)
  · cases es.g.epMgmt Δ qep Pt r.isSome with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some s1 =>
      dsimp only
      rw [StateT.run_bind]
      refine (liftH_pot (vSend_pot hSpec s1 Pt (s1.st Pt) m none r es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
      cases o with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      | some p =>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem challEBucket_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    (q : Party × M × M × Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((challEBucket q).run es) (rem + 1 + pot es.h) := by
  unfold challEBucket
  simp only [StateT.run_pure]
  exact PotBound.pure (by dsimp only; omega)

private theorem challE_pot [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep : ℕ) (cfg : Config M) (π : Policy)
    (q : Party × M × M × Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((challE hk Δ qep cfg π q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, m0, m1, r⟩
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact PotBound.pure (by dsimp only; omega)
  · cases es.g.epMgmt Δ qep Pt r.isSome with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some s1 =>
      dsimp only
      split
      · simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only; omega)
      · split
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only; omega)
        · rw [StateT.run_bind]
          refine (liftH_pot (vSend_pot hSpec s1 Pt (s1.st Pt) _ (some (m0, m1)) r es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
          cases o with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
          | some p =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem deliverE_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (maxSkip : ℕ) (cfg : Config M)
    (q : Party × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((deliverE hk maxSkip cfg q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · cases es.g.inTransit Pt.other c with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some r =>
      dsimp only
      rw [StateT.run_bind]
      refine (liftH_pot (vRecv_pot hSpec es.g Pt (es.g.st Pt) c (some r) es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
      rcases o with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      · dsimp only
        split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      · dsimp only
        rw [StateT.run_bind]
        refine ((commitE_pot hSpec es.g Pt (es.g.st Pt) st' r.pos es1 rem).mono (fun _ => le_rfl) hk).bind fun ⟨s1?, es2⟩ k2 hk2 => ?_
        cases s1? with
        | none =>
          simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
        | some s1 =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)

private theorem injectE_pot [DecidableEq T] [DecidableEq E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep : ℕ) (cfg : Config M)
    (q : Party × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((injectE hk Δ qep cfg q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · rw [StateT.run_bind]
    refine (liftH_pot (vRecv_pot hSpec es.g Pt (es.g.st Pt) c none es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
    rcases o with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
    · simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
    · dsimp only
      split
      · simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      · split
        · rw [StateT.run_bind]
          refine ((commitE_pot hSpec es.g Pt (es.g.st Pt) st' _ es1 rem).mono (fun _ => le_rfl) hk).bind fun ⟨s1?, es2⟩ k2 hk2 => ?_
          cases s1? with
          | none =>
            simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
          | some s1 =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
        · split
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
          · simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem injectEB1_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((injectEB1 hk qep tStar cfg q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, c⟩
  unfold injectEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · rw [StateT.run_bind]
    refine (liftH_pot (vRecv_pot hSpec es.g Pt (es.g.st Pt) c none es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
    rcases o with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
    · simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
    · dsimp only
      split
      · simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      · split
        · rw [StateT.run_bind]
          refine ((commitE_pot hSpec es.g Pt (es.g.st Pt) st' _ es1 rem).mono (fun _ => le_rfl) hk).bind fun ⟨s1?, es2⟩ k2 hk2 => ?_
          cases s1? with
          | none =>
            simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
          | some s1 =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
        · split
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
          · simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem deliverForgeE_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep : ℕ) (cfg : Config M)
    (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((deliverForgeE hk Δ qep cfg q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · cases es.g.inTransit Pt.other c with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some r =>
      dsimp only
      split
      · simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only; omega)
      · rw [StateT.run_bind]
        refine (liftH_pot (vRecv_pot hSpec es.g Pt (es.g.st Pt) c' none es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
        rcases o with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
        · dsimp only
          split
          · simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
          · split
            · rw [StateT.run_bind]
              refine ((commitE_pot hSpec es.g Pt (es.g.st Pt) st' _ es1 rem).mono (fun _ => le_rfl) hk).bind fun ⟨s1?, es2⟩ k2 hk2 => ?_
              cases s1? with
              | none =>
                simp only [StateT.run_pure]
                exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
              | some s1 =>
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
            · split
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
              · simp only [StateT.run_pure]
                exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem deliverForgeEB1_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((deliverForgeEB1 hk qep tStar cfg q).run es) (rem + 1 + pot es.h) := by
  rcases q with ⟨Pt, c, c'⟩
  unfold deliverForgeEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · cases es.g.inTransit Pt.other c with
    | none =>
      simp only [StateT.run_pure]
      exact PotBound.pure (by dsimp only; omega)
    | some r =>
      dsimp only
      split
      · simp only [StateT.run_pure]
        exact PotBound.pure (by dsimp only; omega)
      · rw [StateT.run_bind]
        refine (liftH_pot (vRecv_pot hSpec es.g Pt (es.g.st Pt) c' none es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
        rcases o with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
        · dsimp only
          split
          · simp only [StateT.run_pure]
            exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
          · split
            · rw [StateT.run_bind]
              refine ((commitE_pot hSpec es.g Pt (es.g.st Pt) st' _ es1 rem).mono (fun _ => le_rfl) hk).bind fun ⟨s1?, es2⟩ k2 hk2 => ?_
              cases s1? with
              | none =>
                simp only [StateT.run_pure]
                exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
              | some s1 =>
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                exact PotBound.pure (by dsimp only at hk2 ⊢; exact hk2)
            · split
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
              · simp only [StateT.run_pure]
                exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem corrEPaper_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (π : Policy) (Pt : Party)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((corrEPaper hk π Pt).run es) (rem + 1 + pot es.h) := by
  unfold corrEPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · split
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only; omega)
    · rw [StateT.run_bind]
      refine (liftH_pot (hSpec.reveal_pot es.g Pt (es.g.st Pt) es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
      cases o with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      | some _ =>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem corrEPaperBucket_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Pt : Party)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((corrEPaperBucket hk Pt).run es) (rem + 1 + pot es.h) := by
  unfold corrEPaperBucket
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · rw [StateT.run_bind]
    refine (liftH_pot (hSpec.reveal_pot es.g Pt (es.g.st Pt) es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
    cases o with
    | none =>
      simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
    | some _ =>
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem corrEShiftedPaper_pot {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (l : ℕ) (π : Policy) (Pt : Party)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((corrEShiftedPaper l hk π Pt).run es) (rem + 1 + pot es.h) := by
  unfold corrEShiftedPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]
    exact PotBound.pure (by dsimp only; omega)
  · split
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only; omega)
    · rw [StateT.run_bind]
      refine (liftH_pot (hSpec.reveal_pot es.g Pt (es.g.st Pt) es.h rem)).bind fun ⟨o, es1⟩ k hk => ?_
      cases o with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)
      | some _ =>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only at hk ⊢; exact hk)

private theorem injectEGen_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (b1 : Bool) (Δ qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((injectEGen b1 hk Δ qep tStar cfg q).run es)
      (rem + 1 + pot es.h) := by
  cases b1
  · exact injectE_pot hSpec Δ qep cfg q es rem
  · exact injectEB1_pot hSpec qep tStar cfg q es rem

private theorem deliverForgeEGen_pot [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (b1 : Bool) (Δ qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h) ((deliverForgeEGen b1 hk Δ qep tStar cfg q).run es)
      (rem + 1 + pot es.h) := by
  cases b1
  · exact deliverForgeE_pot hSpec Δ qep cfg q es rem
  · exact deliverForgeEB1_pot hSpec qep tStar cfg q es rem

theorem implEDFShiftedPaperGen_inr_pot [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (b1 : Bool) (l Δ qep maxSkip tStar : ℕ)
    (cfg : Config M) (π : Policy)
    (q : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h)
      ((implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr q)).run es)
      (rem + 1 + pot es.h) := by
  rcases q with ((((q1 | q2) | q3) | q4) | q5) | q6
  · exact transmitE_pot hSpec Δ qep π q1 es rem
  · exact challE_pot hSpec Δ qep cfg π q2 es rem
  · exact deliverE_pot hSpec maxSkip cfg q3 es rem
  · exact injectEGen_pot hSpec b1 Δ qep tStar cfg q4 es rem
  · exact corrEShiftedPaper_pot hSpec l π q5 es rem
  · exact deliverForgeEGen_pot hSpec b1 Δ qep tStar cfg q6 es rem

theorem implEDFPaper_inr_pot [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (q : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h)
      ((implEDFPaper hk Δ qep maxSkip cfg π (.inr q)).run es)
      (rem + 1 + pot es.h) := by
  rcases q with ((((q1 | q2) | q3) | q4) | q5) | q6
  · exact transmitE_pot hSpec Δ qep π q1 es rem
  · exact challE_pot hSpec Δ qep cfg π q2 es rem
  · exact deliverE_pot hSpec maxSkip cfg q3 es rem
  · exact injectE_pot hSpec Δ qep cfg q4 es rem
  · exact corrEPaper_pot hSpec π q5 es rem
  · exact deliverForgeE_pot hSpec Δ qep cfg q6 es rem

theorem implEDFPaperBucketRaw_inr_pot [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    {hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (hSpec : ShallowHooksPot P pot hk) (Δ qep maxSkip : ℕ) (cfg : Config M)
    (q : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (rem : ℕ) :
    PotBound P (fun z => rem + pot z.2.h)
      ((implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr q)).run es)
      (rem + 1 + pot es.h) := by
  rcases q with ((((q1 | q2) | q3) | q4) | q5) | q6
  · exact transmitEBucket_pot hSpec Δ qep q1 es rem
  · exact challEBucket_pot q2 es rem
  · exact deliverE_pot hSpec maxSkip cfg q3 es rem
  · exact injectE_pot hSpec Δ qep cfg q4 es rem
  · exact corrEPaperBucket_pot hSpec q5 es rem
  · exact deliverForgeE_pot hSpec Δ qep cfg q6 es rem

theorem withWinEpDF_pot {St Msg Coins C S' : Type}
    {P : (unifSpec + tspec).Domain → Bool} {pot : S' → ℕ}
    (ctEpoch : C → ℕ) (hasWin : S' → Bool)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins C) (StateT S' (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins C).Domain)
    (st : S' × Option ℕ) {rem b : ℕ}
    (h : PotBound P (fun z => rem + pot z.2) ((impl t).run st.1) b) :
    PotBound P (fun z => rem + pot z.2.1)
      ((withWinEpDF ctEpoch hasWin impl t).run st) b := by
  unfold withWinEpDF
  dsimp only [StateT.run_mk]
  exact h.bind fun ⟨r', s'⟩ k hk => PotBound.pure (by dsimp only at hk ⊢; exact hk)

end HooksPot

end

end Computational.Proofs.E2E.SessionAuthHooksPot
