/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import VCVio.OracleComp.EvalDist.Measure

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section InactiveZero

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}

private def projB {Sig' I' K' α : Type}
    (c : StateT (PRFPRNG.GameState Sig' I' K') ProbComp α)
    (sp : PRFPRNG.GameState Sig' I' K') :
    ProbComp (α × PRFPRNG.GameState Sig' I' K') :=
  (fun p => (p.1, { p.2 with b := false })) <$> c.run sp

private def BIndep {Sig' I' K' α : Type}
    (c : StateT (PRFPRNG.GameState Sig' I' K') ProbComp α) : Prop :=
  ∀ sp, projB c sp = projB c { sp with b := false }

private def BIndepC [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    (m : PRFPRNG.AdversaryComp Sig I K α) : Prop :=
  BIndep (simulateQ (AuthL11.pImpl prng) m)

private theorem BIndep_bind {Sig' I' K' α β : Type}
    {c1 : StateT (PRFPRNG.GameState Sig' I' K') ProbComp α}
    {c2 : α → StateT (PRFPRNG.GameState Sig' I' K') ProbComp β}
    (h1 : BIndep c1) (h2 : ∀ x, BIndep (c2 x)) :
    BIndep (c1 >>= c2) := by
  intro sp
  have step : ∀ sp0, projB (c1 >>= c2) sp0 =
      (projB c1 sp0) >>= fun p => projB (c2 p.1) p.2 := by
    intro sp0
    simp only [projB, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun p => ?_
    simpa only [projB, map_eq_bind_pure_comp, Function.comp_apply] using h2 p.1 p.2
  rw [step sp, h1 sp, ← step { sp with b := false }]

private theorem BIndepC_pure [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type} (x : α) :
    BIndepC prng (pure x) := by
  intro sp; simp [projB]

private theorem BIndepC_bind [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α β : Type}
    {m : PRFPRNG.AdversaryComp Sig I K α}
    {f : α → PRFPRNG.AdversaryComp Sig I K β}
    (hm : BIndepC prng m) (hf : ∀ x, BIndepC prng (f x)) :
    BIndepC prng (m >>= f) := by
  unfold BIndepC
  rw [simulateQ_bind]
  exact BIndep_bind hm hf

private theorem BIndepC_query_inl [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (s : unifSpec.Domain) :
    BIndepC prng (query (spec := unifSpec + PRFPRNG.spec Sig I K) (.inl s)) := by
  intro sp
  unfold projB AuthL11.pImpl
  erw [simulateQ_query]
  simp [OracleQuery.input_query, OracleQuery.cont_query, StateT.run_monadLift]

private theorem BIndepC_sampleT [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (X : Type) [SampleableType X] :
    BIndepC prng (sampleT X) := by
  intro sp
  simp [projB, AuthL11.simulateQ_pImpl_sampleT]

private theorem BIndepC_processQuery [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (optI : Option I) :
    BIndepC prng (PRFPRNG.processQuery optI) := by
  intro sp
  cases optI <;> cases hprf : sp.prf <;>
    simp [projB, AuthL11.simulateQ_pImpl_processQuery,
      AuthL11.run_processImpl_some, AuthL11.run_processImpl_none, hprf]

private theorem BIndepC_corrQuery [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) :
    BIndepC prng (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) := by
  intro sp
  cases hprf : sp.prf <;>
    simp [projB, AuthL11.simulateQ_pImpl_corrQuery, AuthL11.run_corrImpl, hprf]

private def BIndepS [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S α : Type}
    (m : StateT S (PRFPRNG.AdversaryComp Sig I K) α) : Prop :=
  ∀ s, BIndepC prng (m.run s)

private theorem BIndepS_pure [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S α : Type} (x : α) :
    BIndepS (S := S) prng (pure x) := by
  intro s; exact BIndepC_pure prng (x, s)

private theorem BIndepS_bind [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S α β : Type}
    {m : StateT S (PRFPRNG.AdversaryComp Sig I K) α}
    {f : α → StateT S (PRFPRNG.AdversaryComp Sig I K) β}
    (hm : BIndepS prng m) (hf : ∀ x, BIndepS prng (f x)) :
    BIndepS prng (m >>= f) := by
  intro s; rw [StateT.run_bind]
  exact BIndepC_bind prng (hm s) (fun p => hf p.1 p.2)

private theorem BIndepS_get [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S : Type} :
    BIndepS (S := S) prng get := by
  intro s; exact BIndepC_pure prng (s, s)

private theorem BIndepS_modify [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S : Type} (f : S → S) :
    BIndepS prng (modify f) := by
  intro s; exact BIndepC_pure prng ((), f s)

private theorem BIndepS_lift [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {S α : Type}
    {m : PRFPRNG.AdversaryComp Sig I K α} (hm : BIndepC prng m) :
    BIndepS (S := S) prng (StateT.lift m) := by
  intro s
  exact BIndepC_bind prng hm (fun a => BIndepC_pure prng (a, s))

private theorem BIndepS_liftH [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {Γv T' Sv SSv RSv M' E' HS α : Type}
    {x : HM (PRFPRNG.spec Sig I K) HS α} (hx : BIndepS prng x) :
    BIndepS (S := EState (VP Γv T' Sv SSv RSv) M' (Header T' × E') HS) prng (liftH x) := by
  intro es
  exact BIndepC_bind prng (hx es.h) (fun p => BIndepC_pure prng (p.1, { es with h := p.2 }))

private theorem BIndepS_lookupPRNGBucketF [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (t0 : ℕ) (ik : I) :
    BIndepS (S := PRNGBucketState T Sig K I) prng (lookupPRNGBucketF t0 ik) := by
  unfold lookupPRNGBucketF
  refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
  dsimp only
  cases (h0.fTable t0).lookup ik with
  | some k => exact BIndepS_pure prng k
  | none =>
    refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_sampleT prng K)) fun k => ?_
    refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
    exact BIndepS_pure prng k

private theorem BIndepS_rootPRNGBucketHybrid [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t t0 : ℕ) (pl : Bool) (ik0 : I) (σv0 : Option Sig)
    (hNoChall : t0 ≠ t ∨ isActiveBucketEpoch Δbucket tL par t0 = false) :
    BIndepS (S := PRNGBucketState T Sig K I) prng
      (rootPRNGBucketHybrid prng Δbucket tL par t t0 pl ik0 σv0) := by
  unfold rootPRNGBucketHybrid
  refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
  dsimp only
  split_ifs with hlt hpl heq h1 h2 hge h3 h4
  · cases resolveCorrRoot h0 (t0 - 1) σv0 <;> exact BIndepS_pure prng _
  · cases resolveCorrRoot h0 (t0 - 1) σv0 with
    | some σ => exact BIndepS_pure prng _
    | none =>
      refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_corrQuery prng)) fun r => ?_
      cases r with
      | none => exact BIndepS_pure prng _
      | some σOut =>
        refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
        exact BIndepS_pure prng _
  · exfalso
    rcases hNoChall with hne | hinact
    · exact hne heq
    · simp [isActiveBucketEpoch, h1] at hinact
  · exfalso
    rcases hNoChall with hne | hinact
    · exact hne heq
    · simp [isActiveBucketEpoch, h2] at hinact
  · refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_processQuery prng (some ik0))) fun r1 => ?_
    cases r1 with
    | none => exact BIndepS_pure prng _
    | some kOut =>
      refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_corrQuery prng)) fun r2 => ?_
      cases r2 <;> exact BIndepS_pure prng _
  · refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_processQuery prng none)) fun r1 => ?_
    cases r1 with
    | none => exact BIndepS_pure prng _
    | some _ =>
      refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_sampleT prng K)) fun kRand => ?_
      exact BIndepS_pure prng _
  · refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_processQuery prng (some ik0))) fun r1 => ?_
    cases r1 with
    | none => exact BIndepS_pure prng _
    | some _ =>
      refine BIndepS_bind prng (BIndepS_lookupPRNGBucketF prng t0 ik0) fun kRand => ?_
      exact BIndepS_pure prng _
  · refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_processQuery prng (some ik0))) fun r1 => ?_
    cases r1 <;> exact BIndepS_pure prng _
  · refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_processQuery prng (some ik0))) fun r1 => ?_
    cases r1 with
    | none => exact BIndepS_pure prng _
    | some kOut =>
      refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_corrQuery prng)) fun r2 => ?_
      cases r2 <;> exact BIndepS_pure prng _

private structure HooksBIndep [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {HS : Type}
    (hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS) : Prop where
  startRecv : ∀ ctx P ep γ0 σv0 tn0, BIndepS prng (hk.startRecv ctx P ep γ0 σv0 tn0)
  fsSend : ∀ ctx P ep ss h m r0, BIndepS prng (hk.fsSend ctx P ep ss h m r0)
  fsRecv : ∀ ctx P ep rs h e rec, BIndepS prng (hk.fsRecv ctx P ep rs h e rec)
  commit : ∀ ctx P old new, BIndepS prng (hk.commit ctx P old new)
  reveal : ∀ ctx P vp, BIndepS prng (hk.reveal ctx P vp)

private theorem BIndepS_vSend_of_hooks
    [DecidableEq I] [Inhabited E] [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (s : VP Γ T (Option Sig) SS RS)
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hStartSend : s.id.sendsIn (s.tcur + 1) = true →
      BIndepS prng (hk.startSend ctx P (s.tcur + 1) s.γ s.root r)) :
    BIndepS prng (vSend hk ctx P s m pair r) := by
  unfold vSend
  by_cases hs : s.id.sendsIn (s.tcur + 1) = true
  · simp only [hs, ↓reduceIte]
    refine BIndepS_bind prng (hStartSend hs) fun res => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]; exact BIndepS_pure prng none
    · simp only [pure_bind]
      refine BIndepS_bind prng (hhk.fsSend _ _ _ _ _ _ _) fun rfs => ?_
      cases rfs <;> exact BIndepS_pure prng _
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases s.vS with
    | none => exact BIndepS_pure prng _
    | some v =>
      refine BIndepS_bind prng (hhk.fsSend _ _ _ _ _ _ _) fun rfs => ?_
      cases rfs <;> exact BIndepS_pure prng _

private theorem BIndepS_vRecv_of_hooks
    [DecidableEq T] [DecidableEq I] [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (s : VP Γ T (Option Sig) SS RS)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    BIndepS prng (vRecv hk ctx P s c rec) := by
  unfold vRecv
  dsimp only
  split_ifs with hbad heq
  · exact BIndepS_pure prng _
  · cases c.1.2 with
    | none =>
      simp only [pure_bind]
      exact BIndepS_pure prng _
    | some Tn =>
      dsimp only
      refine BIndepS_bind prng (hhk.startRecv ctx P c.1.1 s.γ s.root Tn) fun res => ?_
      rcases res with _ | _ | ⟨γ', σ', rs⟩
      · simp only [pure_bind]; exact BIndepS_pure prng _
      · simp only [pure_bind]; exact BIndepS_pure prng _
      · simp only [pure_bind, Function.update_self]
        refine BIndepS_bind prng (hhk.fsRecv _ _ _ _ _ _ _) fun rfs => ?_
        rcases rfs with _ | _ | _ <;> exact BIndepS_pure prng _
  · simp only [pure_bind]
    cases s.vR c.1.1 with
    | none => exact BIndepS_pure prng _
    | some v =>
      refine BIndepS_bind prng (hhk.fsRecv _ _ _ _ _ _ _) fun rfs => ?_
      rcases rfs with _ | _ | _ <;> exact BIndepS_pure prng _

private theorem BIndepS_commitE_of_hooks
    [DecidableEq I] [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos) :
    BIndepS (S := EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS)
      prng (commitE hk s P old new pos) := by
  unfold commitE
  refine BIndepS_bind prng (BIndepS_liftH prng (hhk.commit _ P old new)) fun r => ?_
  cases r with
  | none =>
    refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
    exact BIndepS_pure prng none
  | some new' => exact BIndepS_pure prng _

private theorem BIndepS_deliverE_of_hooks
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk) (maxSkip : ℕ) (cfg : Config M)
    (arg : Party × (Header T × E)) :
    BIndepS prng (deliverE hk maxSkip cfg arg) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  refine BIndepS_bind prng (BIndepS_get prng) fun es => ?_
  dsimp only
  split_ifs with hab
  · exact BIndepS_pure prng none
  · cases es.g.inTransit P.other c with
    | none => exact BIndepS_pure prng none
    | some r =>
      dsimp only
      refine BIndepS_bind prng
        (BIndepS_liftH prng (BIndepS_vRecv_of_hooks hhk es.g P (es.g.st P) c (some r)))
        fun rv => ?_
      rcases rv with _ | _ | ⟨st', t', i', m'⟩
      · dsimp only
        refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
        exact BIndepS_pure prng none
      · dsimp only
        split_ifs
        all_goals repeat refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
        all_goals exact BIndepS_pure prng _
      · dsimp only
        refine BIndepS_bind prng
          (BIndepS_commitE_of_hooks hhk es.g P (es.g.st P) st' r.pos)
          fun rc => ?_
        cases rc with
        | none => exact BIndepS_pure prng none
        | some s₁ =>
          refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
          exact BIndepS_pure prng _

private theorem BIndepS_injectE_of_hooks
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk) (Δ qep : ℕ) (cfg : Config M)
    (arg : Party × (Header T × E)) :
    BIndepS prng (injectE hk Δ qep cfg arg) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  refine BIndepS_bind prng (BIndepS_get prng) fun es => ?_
  dsimp only
  split_ifs with hab
  · exact BIndepS_pure prng none
  · refine BIndepS_bind prng
      (BIndepS_liftH prng (BIndepS_vRecv_of_hooks hhk es.g P (es.g.st P) c none))
      fun rv => ?_
    rcases rv with _ | _ | ⟨st', t', i', m'⟩
    · dsimp only
      refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
      exact BIndepS_pure prng none
    · exact BIndepS_pure prng _
    · dsimp only
      split_ifs with hgt htriv
      · exact BIndepS_pure prng _
      · refine BIndepS_bind prng
          (BIndepS_commitE_of_hooks hhk es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
          fun rc => ?_
        cases rc with
        | none => exact BIndepS_pure prng none
        | some s₁ =>
          refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
          exact BIndepS_pure prng _
      · refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => BIndepS_pure prng _
      · exact BIndepS_pure prng _

private theorem BIndepS_deliverForgeE_of_hooks
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk) (Δ qep : ℕ) (cfg : Config M)
    (arg : Party × (Header T × E) × (Header T × E)) :
    BIndepS prng (deliverForgeE hk Δ qep cfg arg) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeE
  refine BIndepS_bind prng (BIndepS_get prng) fun es => ?_
  dsimp only
  split_ifs with hab
  · exact BIndepS_pure prng none
  · cases es.g.inTransit P.other c with
    | none => exact BIndepS_pure prng none
    | some r =>
      dsimp only
      split_ifs with hbad
      · exact BIndepS_pure prng none
      · refine BIndepS_bind prng
          (BIndepS_liftH prng (BIndepS_vRecv_of_hooks hhk es.g P (es.g.st P) c' none))
          fun rv => ?_
        rcases rv with _ | _ | ⟨st', t', i', m'⟩
        · dsimp only
          refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
          exact BIndepS_pure prng none
        · exact BIndepS_pure prng _
        · dsimp only
          split_ifs with hgt htriv
          · exact BIndepS_pure prng _
          · refine BIndepS_bind prng
              (BIndepS_commitE_of_hooks hhk es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
              fun rc => ?_
            cases rc with
            | none => exact BIndepS_pure prng none
            | some s₁ =>
              refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
              exact BIndepS_pure prng _
          · refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => BIndepS_pure prng _
          · exact BIndepS_pure prng _

private theorem BIndepS_corrEPaperBucket_of_hooks
    [DecidableEq I] [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk) (P : Party) :
    BIndepS prng (corrEPaperBucket hk P) := by
  unfold corrEPaperBucket
  refine BIndepS_bind prng (BIndepS_get prng) fun es => ?_
  dsimp only
  split_ifs with hab
  · exact BIndepS_pure prng none
  · refine BIndepS_bind prng
      (BIndepS_liftH prng (hhk.reveal es.g P (es.g.st P)))
      fun rv => ?_
    cases rv with
    | none =>
      refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
      exact BIndepS_pure prng none
    | some st =>
      refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
      exact BIndepS_pure prng _

private theorem BIndepS_startSend_hybridGen
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (ep : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (r0 : Option CCoins)
    (hNoChall : ep ≠ t0 ∨ isActiveBucketEpoch Δbucket tL par ep = false) :
    BIndepS prng ((hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t0).startSend ctx P ep γ0 σv0 r0) := by
  unfold hooksPRNGBucketHybridGen
  dsimp only
  refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
  split_ifs <;>
    repeat refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
  all_goals
    cases r0 with
    | none =>
      dsimp only
      refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_sampleT prng CCoins)) fun coins => ?_
      refine BIndepS_bind prng (BIndepS_rootPRNGBucketHybrid prng Δbucket tL par t0 ep _ _ σv0 hNoChall) fun r => ?_
      cases r with
      | none => exact BIndepS_pure prng none
      | some p =>
        refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
        exact BIndepS_pure prng _
    | some coins =>
      simp only [pure_bind]
      refine BIndepS_bind prng (BIndepS_rootPRNGBucketHybrid prng Δbucket tL par t0 ep _ _ σv0 hNoChall) fun r => ?_
      cases r with
      | none => exact BIndepS_pure prng none
      | some p =>
        refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
        exact BIndepS_pure prng _

private theorem hooksBIndep_main
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) :
    HooksBIndep prng (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0) where
  startRecv ctx P ep γ0 σv0 tn0 := by
    unfold hooksPRNGBucketMain hooksPRNGBucketMainGen
    dsimp only
    refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
    split
    · exact BIndepS_pure prng _
    · split_ifs <;> exact BIndepS_pure prng _
  fsSend _ _ _ _ _ _ _ := BIndepS_pure prng _
  fsRecv _ _ _ _ _ _ _ := BIndepS_pure prng _
  commit _ _ _ new := BIndepS_pure prng (some new)
  reveal ctx P vp := by
    unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen
    dsimp only
    refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
    cases resolveCorrRoot h0 vp.tcur vp.root with
    | some σ =>
      dsimp only
      split_ifs
      all_goals repeat refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
      all_goals exact BIndepS_pure prng _
    | none =>
      dsimp only
      split_ifs
      all_goals first
        | exact BIndepS_pure prng none
        | (refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_corrQuery prng)) fun r => ?_
           cases r with
           | none => exact BIndepS_pure prng none
           | some σOut =>
             dsimp only
             repeat refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
             exact BIndepS_pure prng _)

private theorem hooksBIndep_forgedHdr
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hInact : isActiveBucketEpoch (3 + Δcka) tL par t0 = false) :
    HooksBIndep prng (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t0) where
  startRecv ctx P ep γ0 σv0 tn0 := by
    unfold hooksPRNGBucketForgedHdr hooksPRNGBucketForgedHdrGen hooksPRNGBucketHybridGen
    dsimp only
    refine BIndepS_bind prng (BIndepS_get prng) fun h0 => ?_
    split
    · exact BIndepS_pure prng _
    · split_ifs with hGuard hTH hpl heq hge
      · exact BIndepS_pure prng none
      · cases resolveCorrRoot h0 (ep - 1) σv0 <;> exact BIndepS_pure prng _
      · exfalso
        subst heq
        unfold isActiveBucketEpoch inStage2BucketGen at hInact
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hInact
        simp only [Bool.and_eq_true] at hGuard
        rcases hInact.2 with h1 | h2
        · rw [hGuard.2.1] at h1; cases h1
        · rw [hGuard.2.2] at h2; cases h2
      · refine BIndepS_bind prng (BIndepS_lookupPRNGBucketF prng ep _) fun _ => ?_
        exact BIndepS_pure prng _
      · exact BIndepS_pure prng _
      · exact BIndepS_pure prng _
  fsSend _ _ _ _ _ _ _ := BIndepS_pure prng _
  fsRecv _ _ _ _ _ _ _ := BIndepS_pure prng _
  commit _ _ _ new := BIndepS_pure prng (some new)
  reveal ctx P vp := by
    unfold hooksPRNGBucketForgedHdr hooksPRNGBucketForgedHdrGen
    dsimp only
    split_ifs
    · exact BIndepS_pure prng none
    · cases vp.root <;> exact BIndepS_pure prng _

private theorem prng_advantage_eq_zero_of_BIndepC
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (M : PRFPRNG.Adversary Sig I K)
    (hM : BIndepC prng M) :
    PRFPRNG.advantage prng M = 0 := by
  rw [PRFPRNG.advantage_eq_boolDist]
  suffices hEq : PRFPRNG.branch prng true M = PRFPRNG.branch prng false M by
    rw [hEq, MeasureTheory.Measure.boolDist_self]
  unfold PRFPRNG.branch
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  simp only [hpImpl, StateT.run'_eq]
  refine bind_congr fun kr => ?_
  have h1 := hM { σ := prng.init kr, b := true }
  have h2 := congrArg (Functor.map Prod.fst) h1
  simpa only [projB, Functor.map_map] using h2

private theorem BIndepS_simulateQ_mode_of_hooks
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {prng : PRFPRNG KR Sig I K} {HS α : Type}
    {hk : Hooks (PRFPRNG.spec Sig I K) HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS}
    (hhk : HooksBIndep prng hk)
    (hStartSend : ∀ ctx P ep γ0 σv0 r0, BIndepS prng (hk.startSend ctx P ep γ0 σv0 r0))
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (gMain : Bool) (isHonest : HS → Header T → Bool)
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α) :
    BIndepS prng (simulateQ (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest) oa) := by
  have hImplRaw : ∀ q, BIndepS prng (implEDFPaperBucketRaw hk Δ qep maxSkip cfg q) := by
    intro q
    rcases q with n | q'
    · exact BIndepS_lift prng (BIndepC_query_inl prng n)
    · rcases q' with ((((⟨P, m, r⟩ | x) | c) | c) | P) | c
      · change BIndepS prng (transmitEBucket _ _ _ (P, m, r))
        unfold transmitEBucket
        refine BIndepS_bind prng (BIndepS_get prng) fun es => ?_
        split_ifs with hab
        · exact BIndepS_pure prng none
        · cases es.g.epMgmt Δ qep P r.isSome with
          | none => exact BIndepS_pure prng none
          | some s₁ =>
            refine BIndepS_bind prng
              (BIndepS_liftH prng (BIndepS_vSend_of_hooks hhk s₁ P (s₁.st P) m none r
                (fun _ => hStartSend _ _ _ _ _ _)))
              fun rv => ?_
            cases rv with
            | none =>
              refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
              exact BIndepS_pure prng none
            | some p =>
              refine BIndepS_bind prng (BIndepS_modify prng _) fun _ => ?_
              exact BIndepS_pure prng _
      · exact BIndepS_pure prng none
      · exact BIndepS_deliverE_of_hooks hhk maxSkip cfg c
      · exact BIndepS_injectE_of_hooks hhk Δ qep cfg c
      · exact BIndepS_corrEPaperBucket_of_hooks hhk P
      · exact BIndepS_deliverForgeE_of_hooks hhk Δ qep cfg c
  have hImpl : ∀ q, BIndepS prng (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest q) := by
    intro q ⟨es0, winEp0⟩
    unfold implEDFPaperBucketMode withWinEpDFMode
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk]
      exact BIndepC_bind prng (hImplRaw q es0) (fun p => BIndepC_pure prng _)
    · simp only [↓reduceIte, withWinEpDF, StateT.run_mk]
      exact BIndepC_bind prng (hImplRaw q es0) (fun p => BIndepC_pure prng _)
  induction oa using OracleComp.inductionOn with
  | pure a => exact BIndepS_pure prng a
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact BIndepS_bind prng (hImpl q) ih

theorem prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hInact : isActiveBucketEpoch (3 + Δcka) tL par t0 = false)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A) = 0 := by
  apply prng_advantage_eq_zero_of_BIndepC
  have hNoChall : ∀ ep : ℕ, ep ≠ t0 ∨ isActiveBucketEpoch (3 + Δcka) tL par ep = false := by
    intro ep; by_cases h : ep = t0
    · subst h; exact Or.inr hInact
    · exact Or.inl h
  have hInit : BIndepS prng (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t0) := by
    unfold initPRNGBucketHybrid
    refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_sampleT prng KC)) fun kc => ?_
    refine BIndepS_bind prng
      (BIndepS_rootPRNGBucketHybrid prng (3 + Δcka) tL par t0 0 false lam none (hNoChall 0))
      fun r => ?_
    cases r <;> exact BIndepS_pure prng _
  unfold redPRNGAuthDFPaperBucketMain engRunDFPaperBucket
  refine BIndepC_bind prng ?_ fun r => BIndepC_pure prng _
  refine BIndepC_bind prng (hInit {}) fun ⟨vs, h⟩ => ?_
  cases vs with
  | none => exact BIndepC_pure prng none
  | some p =>
    have hSim := BIndepS_simulateQ_mode_of_hooks
      (hooksBIndep_main cka prng fs Δcka qep tL par t0)
      (fun ctx P ep γ0 σv0 r0 => BIndepS_startSend_hybridGen cka prng fs (3 + Δcka) qep tL par t0 ctx P ep γ0 σv0 r0 (hNoChall ep))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) true isHonestHdrPRNGBucket A
    exact BIndepC_bind prng (hSim ({ g := _, h := h }, none)) fun res => BIndepC_pure prng (some res)

theorem prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hInact : isActiveBucketEpoch (3 + Δcka) tL par t0 = false)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A) = 0 := by
  apply prng_advantage_eq_zero_of_BIndepC
  have hNoChall : ∀ ep : ℕ, ep ≠ t0 ∨ isActiveBucketEpoch (3 + Δcka) tL par ep = false := by
    intro ep; by_cases h : ep = t0
    · subst h; exact Or.inr hInact
    · exact Or.inl h
  have hInit : BIndepS prng (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t0) := by
    unfold initPRNGBucketHybrid
    refine BIndepS_bind prng (BIndepS_lift prng (BIndepC_sampleT prng KC)) fun kc => ?_
    refine BIndepS_bind prng
      (BIndepS_rootPRNGBucketHybrid prng (3 + Δcka) tL par t0 0 false lam none (hNoChall 0))
      fun r => ?_
    cases r <;> exact BIndepS_pure prng _
  unfold redPRNGAuthDFPaperBucketForgedHdr engRunDFPaperBucketMode
  refine BIndepC_bind prng ?_ fun r => BIndepC_pure prng _
  refine BIndepC_bind prng (hInit {}) fun ⟨vs, h⟩ => ?_
  cases vs with
  | none => exact BIndepC_pure prng none
  | some p =>
    have hSim := BIndepS_simulateQ_mode_of_hooks
      (hooksBIndep_forgedHdr cka prng fs Δcka qep tL par t0 hInact)
      (fun ctx P ep γ0 σv0 r0 => BIndepS_startSend_hybridGen cka prng fs (3 + Δcka) qep tL par t0 ctx P ep γ0 σv0 r0 (hNoChall ep))
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket A
    exact BIndepC_bind prng (hSim ({ g := _, h := h }, none)) fun res => BIndepC_pure prng (some res)

end InactiveZero

end CryptoGames.SM.Construction.DeliverForge
