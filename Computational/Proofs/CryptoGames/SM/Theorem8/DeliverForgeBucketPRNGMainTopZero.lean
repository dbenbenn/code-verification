/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9Aux
import VCVio.OracleComp.EvalDist.Measure

/-!
# Scratch Shard (`N01`): Inactive-Epoch and Top-Epoch (`qep + 1`) Zero `PRFPRNG.advantage` for `Main`

Proves `prng_advantage_redPRNGAuthDFPaperBucketMain_eq_zero_of_inactive` and
`prng_advantage_redPRNGAuthDFPaperBucketMain_top_eq_zero` unconditionally (`0` `RespectsCorrAllowedDF`).-/

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section MainNoChallPRNG

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}

private def isChallPRNGQuery : (unifSpec + PRFPRNG.spec Sig I K).Domain → Bool
  | .inl _ => false
  | .inr (.inl (.inl (.inl _))) => false
  | .inr (.inr _) => false
  | _ => true

private inductive NoChallPRNG {α : Type} (post : α → Prop) :
    OracleComp (unifSpec + PRFPRNG.spec Sig I K) α → Prop where
  | pure {a : α} (ha : post a) : NoChallPRNG post (Pure.pure a)
  | query_bind {t : (unifSpec + PRFPRNG.spec Sig I K).Domain}
      {k : (unifSpec + PRFPRNG.spec Sig I K).Range t →
        OracleComp (unifSpec + PRFPRNG.spec Sig I K) α}
      (ht : isChallPRNGQuery (Sig := Sig) (I := I) (K := K) t = false)
      (hk : ∀ y, NoChallPRNG post (k y)) :
      NoChallPRNG post (liftM (OracleSpec.query t) >>= k)

private theorem NoChallPRNG.bind {α β : Type} {mid : α → Prop} {post : β → Prop}
    {mx : OracleComp (unifSpec + PRFPRNG.spec Sig I K) α}
    {f : α → OracleComp (unifSpec + PRFPRNG.spec Sig I K) β}
    (h : NoChallPRNG mid mx) (hf : ∀ a, mid a → NoChallPRNG post (f a)) :
    NoChallPRNG post (mx >>= f) := by
  induction h with
  | pure ha => rw [pure_bind]; exact hf _ ha
  | query_bind ht _ ih => rw [bind_assoc]; exact NoChallPRNG.query_bind ht ih

private theorem NoChallPRNG.query_false
    {t : (unifSpec + PRFPRNG.spec Sig I K).Domain}
    (ht : isChallPRNGQuery (Sig := Sig) (I := I) (K := K) t = false) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True)
      (query (spec := unifSpec + PRFPRNG.spec Sig I K) t) := by
  have hq : (query (spec := unifSpec + PRFPRNG.spec Sig I K) t :
      OracleComp (unifSpec + PRFPRNG.spec Sig I K) _) = liftM (OracleSpec.query t) >>= Pure.pure := by
    rw [show (query (spec := unifSpec + PRFPRNG.spec Sig I K) t :
      OracleComp (unifSpec + PRFPRNG.spec Sig I K) _) = liftM (OracleSpec.query t) from rfl, bind_pure]
  rw [hq]; exact NoChallPRNG.query_bind ht fun _ => NoChallPRNG.pure trivial

private theorem NoChallPRNG.of_probComp {α : Type} (oa : ProbComp α) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True)
      (liftM oa : OracleComp (unifSpec + PRFPRNG.spec Sig I K) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => change NoChallPRNG _ (Pure.pure a); exact NoChallPRNG.pure trivial
  | query_bind t k ih =>
    change NoChallPRNG _
      ((query (spec := unifSpec + PRFPRNG.spec Sig I K) (.inl t)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + PRFPRNG.spec Sig I K) α))
    exact (NoChallPRNG.query_false rfl).bind fun u _ => ih u

private theorem NoChallPRNG.sampleT_comp (α : Type) [SampleableType α] :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True)
      (sampleT (tspec := PRFPRNG.spec Sig I K) α) :=
  NoChallPRNG.of_probComp ($ᵗ α : ProbComp α)

private theorem NoChallPRNG.lift_sampleT {HS : Type} (α : Type) [SampleableType α] (h : HS) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2 = h)
      ((StateT.lift (sampleT (tspec := PRFPRNG.spec Sig I K) α)).run h) := by
  rw [StateT.run_lift]; exact (NoChallPRNG.sampleT_comp α).bind fun _ _ => NoChallPRNG.pure rfl

private theorem NoChallPRNG.liftPBucket_process (x : Option I)
    (h : PRNGBucketState T Sig K I) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2 = h)
      ((liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) x)).run h) := by
  unfold liftPBucket PRFPRNG.processQuery
  rw [StateT.run_lift]
  exact (NoChallPRNG.query_false rfl).bind fun _ _ => NoChallPRNG.pure rfl

private theorem NoChallPRNG.liftPBucket_corr (h : PRNGBucketState T Sig K I) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2 = h)
      ((liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K))).run h) := by
  unfold liftPBucket PRFPRNG.corrQuery
  rw [StateT.run_lift]
  exact (NoChallPRNG.query_false rfl).bind fun _ _ => NoChallPRNG.pure rfl

private theorem simulateQ_pImpl_b_indep [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) {α : Type}
    {m : OracleComp (unifSpec + PRFPRNG.spec Sig I K) α}
    (hm : NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True) m)
    (σ : Sig) (corr prngF prf : Bool) (tab1 tab2 : List (I × K)) :
    Prod.fst <$> ((simulateQ (AuthL11.pImpl prng) m).run
        { σ := σ, b := false, corr := corr, prng := prngF, prf := prf, table := tab1 }) =
    Prod.fst <$> ((simulateQ (AuthL11.pImpl prng) m).run
        { σ := σ, b := true, corr := corr, prng := prngF, prf := prf, table := tab2 }) := by
  induction hm generalizing σ corr prngF prf tab1 tab2 with
  | pure _ => rfl
  | @query_bind t k ht _ ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]
    rcases t with q | (((x | x) | x) | ⟨⟩)
    · let k' : unifSpec.Range q → OracleComp (unifSpec + PRFPRNG.spec Sig I K) α := k
      change ((StateT.lift (liftM (OracleSpec.query q)) :
          StateT (PRFPRNG.GameState Sig I K) ProbComp (unifSpec.Range q)).run
            { σ := σ, b := false, corr := corr, prng := prngF, prf := prf, table := tab1 } >>= fun x =>
          ((simulateQ (AuthL11.pImpl prng) (k' x.1)).run x.2 >>= pure ∘ Prod.fst)) =
        ((StateT.lift (liftM (OracleSpec.query q)) :
          StateT (PRFPRNG.GameState Sig I K) ProbComp (unifSpec.Range q)).run
            { σ := σ, b := true, corr := corr, prng := prngF, prf := prf, table := tab2 } >>= fun x =>
          ((simulateQ (AuthL11.pImpl prng) (k' x.1)).run x.2 >>= pure ∘ Prod.fst))
      simp only [StateT.run_lift, bind_assoc, pure_bind]
      exact congrArg (Bind.bind _) (funext fun y => by
        simpa only [map_eq_bind_pure_comp] using ih y σ corr prngF prf tab1 tab2)
    · let k' : Option K → OracleComp (unifSpec + PRFPRNG.spec Sig I K) α := k
      change ((PRFPRNG.processImpl prng x).run
            { σ := σ, b := false, corr := corr, prng := prngF, prf := prf, table := tab1 } >>= fun z =>
          ((simulateQ (AuthL11.pImpl prng) (k' z.1)).run z.2 >>= pure ∘ Prod.fst)) =
        ((PRFPRNG.processImpl prng x).run
            { σ := σ, b := true, corr := corr, prng := prngF, prf := prf, table := tab2 } >>= fun z =>
          ((simulateQ (AuthL11.pImpl prng) (k' z.1)).run z.2 >>= pure ∘ Prod.fst))
      cases x with
      | some Ik =>
        rw [AuthL11.run_processImpl_some, AuthL11.run_processImpl_some]
        cases prf <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
        · simpa only [map_eq_bind_pure_comp] using ih _ (prng.up σ Ik).1 corr prngF false tab1 tab2
        · simpa only [map_eq_bind_pure_comp] using ih _ σ corr prngF true tab1 tab2
      | none =>
        rw [AuthL11.run_processImpl_none, AuthL11.run_processImpl_none]
        cases prf <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
        · exact congrArg (Bind.bind _) (funext fun Ir => by
            simpa only [map_eq_bind_pure_comp] using ih _ (prng.up σ Ir).1 false prngF false tab1 tab2)
        · simpa only [map_eq_bind_pure_comp] using ih _ σ corr prngF true tab1 tab2
    · simp [isChallPRNGQuery] at ht
    · simp [isChallPRNGQuery] at ht
    · let k' : Option Sig → OracleComp (unifSpec + PRFPRNG.spec Sig I K) α := k
      change ((PRFPRNG.corrImpl (State := Sig) (Input := I) (Output := K) ()).run
            { σ := σ, b := false, corr := corr, prng := prngF, prf := prf, table := tab1 } >>= fun z =>
          ((simulateQ (AuthL11.pImpl prng) (k' z.1)).run z.2 >>= pure ∘ Prod.fst)) =
        ((PRFPRNG.corrImpl (State := Sig) (Input := I) (Output := K) ()).run
            { σ := σ, b := true, corr := corr, prng := prngF, prf := prf, table := tab2 } >>= fun z =>
          ((simulateQ (AuthL11.pImpl prng) (k' z.1)).run z.2 >>= pure ∘ Prod.fst))
      rw [AuthL11.run_corrImpl, AuthL11.run_corrImpl]
      cases prf <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      · simpa only [map_eq_bind_pure_comp] using ih _ σ true prngF false tab1 tab2
      · simpa only [map_eq_bind_pure_comp] using ih _ σ corr prngF true tab1 tab2

private theorem prng_advantage_eq_zero_of_noChall
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (B : PRFPRNG.Adversary Sig I K)
    (hB : NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True) B) :
    PRFPRNG.advantage prng B = 0 := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = AuthL11.pImpl prng := rfl
  have hbr : PRFPRNG.branch prng false B = PRFPRNG.branch prng true B := by
    unfold PRFPRNG.branch
    simp only [hpImpl, StateT.run'_eq]
    congr 1; funext kr
    exact simulateQ_pImpl_b_indep prng hB (prng.init kr) false false false [] []
  rw [PRFPRNG.advantage_eq_boolDist, hbr, Measure.boolDist_self]

private theorem lookupPRNGBucketF_noChall [DecidableEq I] [SampleableType K]
    (ep : ℕ) (ik : I) (h : PRNGBucketState T Sig K I) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2.cache = h.cache)
      ((lookupPRNGBucketF (T := T) (Sig := Sig) ep ik).run h) := by
  unfold lookupPRNGBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable ep).lookup ik with
  | some k => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
  | none =>
    simp only [StateT.run_bind]
    refine (NoChallPRNG.lift_sampleT K h).bind fun ⟨k, h1⟩ hc1 => ?_
    dsimp only at hc1; subst h1
    simp only [StateT.run_modify, pure_bind, StateT.run_pure]
    exact NoChallPRNG.pure rfl

private theorem rootPRNGBucketHybrid_noChall [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 ep : ℕ) (pl : Bool) (ik0 : I) (σv0 : Option Sig)
    (h : PRNGBucketState T Sig K I)
    (hskip : ep = t0 → isActiveBucketEpoch Δbucket tL par t0 = false) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2.cache = h.cache)
      ((rootPRNGBucketHybrid (T := T) prng Δbucket tL par t0 ep pl ik0 σv0).run h) := by
  unfold rootPRNGBucketHybrid
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · cases resolveCorrRoot h (ep - 1) σv0 <;> simp only [StateT.run_pure] <;> exact NoChallPRNG.pure rfl
  · split
    · cases resolveCorrRoot h (ep - 1) σv0 with
      | some σ => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
      | none =>
        rw [StateT.run_bind]
        refine (NoChallPRNG.liftPBucket_corr h).bind fun ⟨o, h1⟩ hc1 => ?_
        dsimp only at hc1; subst h1
        cases o <;> simp only [StateT.run_pure] <;> exact NoChallPRNG.pure rfl
    · by_cases heq : ep = t0
      · subst heq
        have hinact := hskip rfl
        have his_tH : (tL.isSome && decide (ep = healEpoch tL)) = false := by
          simp only [isActiveBucketEpoch, Bool.or_eq_false_iff] at hinact; exact hinact.1
        have hin_f : inStage2BucketGen Δbucket tL par ep = false := by
          simp only [isActiveBucketEpoch, Bool.or_eq_false_iff] at hinact; exact hinact.2
        simp only [↓reduceIte, his_tH, hin_f, Bool.false_eq_true, StateT.run_bind]
        refine (NoChallPRNG.liftPBucket_process (some ik0) h).bind fun ⟨o1, h1⟩ hc1 => ?_
        dsimp only at hc1; subst h1
        cases o1 with
        | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
        | some kOut =>
          simp only [StateT.run_bind]
          refine (NoChallPRNG.liftPBucket_corr h).bind fun ⟨o2, h2⟩ hc2 => ?_
          dsimp only at hc2; subst h2
          cases o2 <;> simp only [StateT.run_pure] <;> exact NoChallPRNG.pure rfl
      · simp only [heq, ↓reduceIte]
        split
        · split
          · rw [StateT.run_bind]
            refine (NoChallPRNG.liftPBucket_process none h).bind fun ⟨o1, h1⟩ hc1 => ?_
            dsimp only at hc1; subst h1
            cases o1 with
            | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
            | some _ =>
              simp only [StateT.run_bind]
              refine (NoChallPRNG.lift_sampleT K h).bind fun ⟨_, h2⟩ hc2 => ?_
              dsimp only at hc2; subst h2
              simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
          · split
            · rw [StateT.run_bind]
              refine (NoChallPRNG.liftPBucket_process (some ik0) h).bind fun ⟨o1, h1⟩ hc1 => ?_
              dsimp only at hc1; subst h1
              cases o1 with
              | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
              | some _ =>
                simp only [StateT.run_bind]
                refine (lookupPRNGBucketF_noChall ep ik0 h).bind fun ⟨_, h2⟩ hc2 => ?_
                dsimp only at hc2
                simp only [StateT.run_pure]; exact NoChallPRNG.pure hc2
            · rw [StateT.run_bind]
              refine (NoChallPRNG.liftPBucket_process (some ik0) h).bind fun ⟨o1, h1⟩ hc1 => ?_
              dsimp only at hc1; subst h1
              cases o1 <;> simp only [StateT.run_pure] <;> exact NoChallPRNG.pure rfl
        · rw [StateT.run_bind]
          refine (NoChallPRNG.liftPBucket_process (some ik0) h).bind fun ⟨o1, h1⟩ hc1 => ?_
          dsimp only at hc1; subst h1
          cases o1 with
          | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
          | some kOut =>
            simp only [StateT.run_bind]
            refine (NoChallPRNG.liftPBucket_corr h).bind fun ⟨o2, h2⟩ hc2 => ?_
            dsimp only at hc2; subst h2
            cases o2 <;> simp only [StateT.run_pure] <;> exact NoChallPRNG.pure rfl

private structure InvLeQep (qep : ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) : Prop where
  vp_id : ∀ P, (es.g.st P).id = P
  vp_tcur : ∀ P, (es.g.st P).tcur = es.g.epoch P
  ep_le : ∀ P, es.g.epoch P ≤ qep
  cache_gt : ∀ t', qep < t' → es.h.cache t' = none
  trans_le : ∀ r ∈ es.g.trans, r.pos.epoch ≤ qep ∧ r.ct.1.1 = r.pos.epoch

private def InactiveOrLeQep (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) : Prop :=
  isActiveBucketEpoch Δbucket tL par t0 = false ∨ (t0 = qep + 1 ∧ InvLeQep qep es)

private theorem liftH_noChall {α : Type} {post : α × PRNGBucketState T Sig K I → Prop}
    {m : HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) α}
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (hm : NoChallPRNG (Sig := Sig) (I := I) (K := K) post (m.run es.h)) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z => post (z.1, z.2.h) ∧ z.2.g = es.g)
      ((liftH m).run es) := by
  rw [AuthL11.run_liftH]
  refine hm.bind fun ⟨a, h'⟩ hp => ?_
  exact NoChallPRNG.pure ⟨hp, rfl⟩

private theorem startSendMain_noChall [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (ep : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (r0 : Option CCoins)
    (h : PRNGBucketState T Sig K I)
    (hskip : ep = t0 → isActiveBucketEpoch (3 + Δcka) tL par t0 = false) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z => ∀ t', t' ≠ ep → z.2.cache t' = h.cache t')
      (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t0).startSend ctx P ep γ0 σv0 r0).run h) := by
  have hcoins : ∀ (coins : CCoins) (h1 : PRNGBucketState T Sig K I) (hc1 : h1.cache = h.cache),
      NoChallPRNG (Sig := Sig) (I := I) (K := K)
        (fun z => ∀ t', t' ≠ ep → z.2.cache t' = h.cache t')
        ((do
          let c := cka.send γ0 coins
          match ← rootPRNGBucketHybrid prng (3 + Δcka) tL par t0 ep (postLeak tL ctx) c.2.2 σv0 with
          | none => return none
          | some (σ', kVal) =>
            modify fun s : PRNGBucketState T Sig K I =>
              { s with cache := Function.update s.cache ep (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run h1) := by
    intro coins h1 hc1
    simp only [StateT.run_bind]
    refine (rootPRNGBucketHybrid_noChall prng (3 + Δcka) tL par t0 ep (postLeak tL ctx)
      (cka.send γ0 coins).2.2 σv0 h1 hskip).bind fun ⟨o, h2⟩ hc2 => ?_
    dsimp only at hc2
    cases o with
    | none =>
      simp only [StateT.run_pure]
      exact NoChallPRNG.pure fun t' _ => by rw [hc2, hc1]
    | some p =>
      rcases p with ⟨σ', kVal⟩
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      exact NoChallPRNG.pure fun t' hne => by simp [Function.update_of_ne hne, hc2, hc1]
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
    cases r0 with
    | some c => exact hcoins c _ rfl
    | none =>
      rw [StateT.run_bind]
      exact (NoChallPRNG.lift_sampleT CCoins _).bind fun ⟨c, h1⟩ hc1 => by
        dsimp only at hc1; subst h1; exact hcoins c _ rfl
  · cases r0 with
    | some c => simp only [StateT.run_bind]; exact hcoins c h rfl
    | none =>
      simp only [StateT.run_bind]
      exact (NoChallPRNG.lift_sampleT CCoins h).bind fun ⟨c, h1⟩ hc1 => by
        dsimp only at hc1; subst h1; exact hcoins c h rfl

private theorem vSendMain_noChall [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (m : M) (r0 : Option CCoins)
    (h : PRNGBucketState T Sig K I)
    (hskip : vp.id.sendsIn (vp.tcur + 1) = true → vp.tcur + 1 = t0 →
      isActiveBucketEpoch (3 + Δcka) tL par t0 = false) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z =>
        (∀ t', (vp.id.sendsIn (vp.tcur + 1) = true → t' ≠ vp.tcur + 1) → z.2.cache t' = h.cache t') ∧
        (∀ vp' ct, z.1 = some (vp', ct) →
          vp'.id = vp.id ∧
          vp'.tcur = (if vp.id.sendsIn (vp.tcur + 1) then vp.tcur + 1 else vp.tcur) ∧
          ct.1.1 = vp'.tcur))
      ((vSend (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0) ctx P vp m none r0).run h) := by
  unfold vSend
  by_cases hs : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind]
    refine (startSendMain_noChall cka prng fs Δcka qep tL par t0 ctx P (vp.tcur + 1)
      vp.γ vp.root r0 h (hskip hs)).bind fun ⟨o, h1⟩ hc1 => ?_
    dsimp only at hc1
    cases o with
    | none =>
      simp only [pure_bind, StateT.run_pure]
      apply NoChallPRNG.pure
      exact ⟨fun t' ht' => hc1 t' (ht' trivial), fun _ _ hfalse => by cases hfalse⟩
    | some p =>
      rcases p with ⟨γ', T', σ', ss⟩
      simp only [pure_bind, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
        StateT.run_pure]
      apply NoChallPRNG.pure
      exact ⟨fun t' ht' => hc1 t' (ht' trivial),
        fun vp' ct heq => by injection heq with heq; cases heq; exact ⟨rfl, rfl, rfl⟩⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases vp.vS with
    | none =>
      simp only [StateT.run_pure]
      exact NoChallPRNG.pure ⟨fun _ _ => rfl,
        fun vp' ct heq => by injection heq with heq; cases heq; exact ⟨rfl, rfl, rfl⟩⟩
    | some v =>
      simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
        pure_bind, StateT.run_pure]
      exact NoChallPRNG.pure ⟨fun _ _ => rfl,
        fun vp' ct heq => by injection heq with heq; cases heq; exact ⟨rfl, rfl, rfl⟩⟩

private theorem vRecvMain_noChall [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E)))
    (h : PRNGBucketState T Sig K I) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z => z.2 = h ∧
        ∀ vp' t' i' m', z.1 = some (some (vp', t', i', m')) →
          t' = c.1.1 ∧ c.1.1 ≤ vp.tcur + 1 ∧ vp'.id = vp.id ∧ vp'.tcur = max vp.tcur c.1.1 ∧
          (c.1.1 = vp.tcur + 1 → (h.cache c.1.1).isSome = true))
      ((vRecv (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0) ctx P vp c rec).run h) := by
  unfold vRecv
  dsimp only
  by_cases hbad : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hbad, ↓reduceIte, StateT.run_pure]
    exact NoChallPRNG.pure ⟨rfl, fun _ _ _ _ hf => by cases hf⟩
  · have hle : c.1.1 ≤ vp.tcur + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hbad; omega
    simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : c.1.1 = vp.tcur + 1
    · simp only [heq, ↓reduceIte]
      cases hc2 : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure]
        exact NoChallPRNG.pure ⟨rfl, fun _ _ _ _ hf => by cases hf⟩
      | some Tn =>
        simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen,
          StateT.run_bind, StateT.run_get, pure_bind]
        cases hcache : h.cache (vp.tcur + 1) with
        | none =>
          dsimp only
          split <;> simp only [pure_bind, StateT.run_pure] <;>
            (apply NoChallPRNG.pure; exact ⟨rfl, fun _ _ _ _ hf => by cases hf⟩)
        | some entry =>
          rcases entry with ⟨Tc, σc, kVal⟩
          dsimp only
          by_cases hTc : Tc = Tn
          · simp only [hTc, ↓reduceIte, StateT.run_pure, pure_bind, Function.update_self]
            cases fs.receive (fs.initReceiver kVal) c.1 c.2 with
            | none =>
              simp only [StateT.run_pure]
              apply NoChallPRNG.pure
              exact ⟨rfl, fun _ _ _ _ hf => by cases hf⟩
            | some res =>
              rcases res with ⟨v', i', m'⟩
              simp only [StateT.run_pure]
              apply NoChallPRNG.pure
              refine ⟨rfl, fun vp' t' i1 m1 hok => ?_⟩
              injection hok with hok; injection hok with hok; cases hok
              exact ⟨rfl, by omega, rfl, by dsimp only; omega, fun _ => by simp⟩
          · simp only [hTc, ↓reduceIte]
            split <;> simp only [pure_bind, StateT.run_pure] <;>
              (apply NoChallPRNG.pure; exact ⟨rfl, fun _ _ _ _ hf => by cases hf⟩)
    · simp only [heq, ↓reduceIte, pure_bind]
      cases vp.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure]
        exact NoChallPRNG.pure ⟨rfl, fun _ _ _ _ hf => by cases hf⟩
      | some v =>
        simp only [hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen, pure_bind]
        cases fs.receive v c.1 c.2 with
        | none =>
          simp only [StateT.run_pure]
          apply NoChallPRNG.pure
          exact ⟨rfl, fun _ _ _ _ hf => by cases hf⟩
        | some res =>
          rcases res with ⟨v', i', m'⟩
          simp only [StateT.run_pure]
          apply NoChallPRNG.pure
          refine ⟨rfl, fun vp' t' i1 m1 hok => ?_⟩
          injection hok with hok; injection hok with hok; cases hok
          exact ⟨rfl, hle, rfl, by dsimp only; omega, fun hcontra => False.elim hcontra⟩

private theorem revealMain_noChall [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (h : PRNGBucketState T Sig K I) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun z => z.2.cache = h.cache)
      (((hooksPRNGBucketMain cka prng fs Δcka qep tL par t0).reveal ctx P vp).run h) := by
  unfold hooksPRNGBucketMain hooksPRNGBucketMainGen hooksPRNGBucketHybridGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hres : resolveCorrRoot h vp.tcur vp.root with
  | some σ =>
    dsimp only
    by_cases hc1 : (!decide (vp.tcur < healEpoch tL) && h.corrRoot.isNone) = true
    · simp only [hc1, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]
      split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
        exact NoChallPRNG.pure rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
        exact NoChallPRNG.pure rfl
  | none =>
    dsimp only
    by_cases hcond : (!postLeak tL ctx && h.corrRoot.isNone && !decide (vp.tcur < healEpoch tL) &&
        (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
    · simp only [hcond, ↓reduceIte, StateT.run_bind]
      refine (NoChallPRNG.liftPBucket_corr h).bind fun ⟨o, h1⟩ hc1 => ?_
      dsimp only at hc1; subst h1
      cases o with
      | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure rfl
      | some σOut =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
          exact NoChallPRNG.pure rfl
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
      exact NoChallPRNG.pure rfl

private theorem invLeQep_accept [DecidableEq M] [DecidableEq T] [DecidableEq E]
    {qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {h1 : PRNGBucketState T Sig K I} {P : Party} {vp' : VP Γ T (Option Sig) SS RS} {pos : SM.Pos}
    (hes : InvLeQep qep es) (hh1 : h1 = es.h)
    (hid : vp'.id = P) (htcur : vp'.tcur = max (es.g.epoch P) pos.epoch)
    (hpos_le : pos.epoch ≤ qep) :
    InvLeQep qep { es with g := es.g.accept P vp' pos, h := h1 } := by
  refine ⟨fun Q => ?_, fun Q => ?_, fun Q => ?_,
    fun t' ht' => hh1 ▸ hes.cache_gt t' ht', fun r hr => ?_⟩
  · dsimp only [SM.GameState.accept, SM.GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp [hid]
    · simp [Function.update_of_ne hQ, hes.vp_id Q]
  · dsimp only [SM.GameState.accept, SM.GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp [htcur]
    · simp [Function.update_of_ne hQ, hes.vp_tcur Q]
  · dsimp only [SM.GameState.accept, SM.GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp [hes.ep_le Q, hpos_le]
    · simp [Function.update_of_ne hQ, hes.ep_le Q]
  · dsimp only [SM.GameState.accept, SM.GameState.delete] at hr
    exact hes.trans_le r (List.mem_filter.mp hr).1

private theorem implEDFPaperBucketMain_step_noChall
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (hst : InactiveOrLeQep (3 + Δcka) qep tL par t0 st.1) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z => InactiveOrLeQep (3 + Δcka) qep tL par t0 z.2.1)
      ((implEDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run st) := by
  have hraw : NoChallPRNG (Sig := Sig) (I := I) (K := K)
      (fun z => InactiveOrLeQep (3 + Δcka) qep tL par t0 z.2)
      ((implEDFPaperBucketRaw (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run st.1) := by
    set es := st.1
    have hpreserve_trivial : ∀ es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E)
        (PRNGBucketState T Sig K I),
        (∀ P, (es'.g.st P).id = (es.g.st P).id ∧ (es'.g.st P).tcur = (es.g.st P).tcur ∧
          es'.g.epoch P = es.g.epoch P) →
        es'.h.cache = es.h.cache →
        (∀ r ∈ es'.g.trans, r ∈ es.g.trans) →
        InactiveOrLeQep (3 + Δcka) qep tL par t0 es' := by
      intro es' hst_eq hcache_eq htrans_sub
      rcases hst with hinact | ⟨ht0, hinv⟩
      · exact Or.inl hinact
      · refine Or.inr ⟨ht0,
          fun P => (hst_eq P).1.trans (hinv.vp_id P),
          fun P => (hst_eq P).2.1.trans ((hinv.vp_tcur P).trans (hst_eq P).2.2.symm),
          fun P => (hst_eq P).2.2 ▸ hinv.ep_le P,
          fun t' ht' => hcache_eq ▸ hinv.cache_gt t' ht',
          fun r hr => hinv.trans_le r (htrans_sub r hr)⟩
    rcases q with n | (((((q1 | q2) | q3) | q4) | P) | q6)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, coinsE]
      rw [StateT.run_lift]
      exact (NoChallPRNG.query_false (t := Sum.inl n) rfl).bind fun _ _ => NoChallPRNG.pure hst
    · rcases q1 with ⟨Pt, m, r0⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      unfold transmitEBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
      · cases hep : es.g.epMgmt (2 + Δcka) qep Pt r0.isSome with
        | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
        | some s1 =>
          have hst_s1 : s1.st = es.g.st ∧ s1.trans = es.g.trans := by
            unfold SM.GameState.epMgmt at hep
            by_cases hs0 : Pt.sendsIn (es.g.epoch Pt + 1) = true
            · simp only [hs0, ↓reduceIte] at hep
              split at hep
              · simp at hep
              · simp only [Option.some.injEq] at hep; subst hep
                split <;> simp [SM.GameState.leak]
            · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hep
              split at hep
              · simp at hep
              · simp only [Option.some.injEq] at hep; subst hep; exact ⟨rfl, rfl⟩
          have hskip : (s1.st Pt).id.sendsIn ((s1.st Pt).tcur + 1) = true →
              (s1.st Pt).tcur + 1 = t0 → isActiveBucketEpoch (3 + Δcka) tL par t0 = false := by
            intro hs heq_t0
            rcases hst with hinact | ⟨ht0, hinv⟩
            · exact hinact
            · rw [hst_s1.1] at hs heq_t0
              rw [hinv.vp_id Pt] at hs
              rw [hinv.vp_tcur Pt] at hs heq_t0
              have he1_le := (epMgmt_le_qep hinv.ep_le hep).2 hs
              omega
          dsimp only; rw [StateT.run_bind]
          refine (liftH_noChall es (vSendMain_noChall cka prng fs Δcka qep tL par t0
            s1 Pt (s1.st Pt) m r0 es.h hskip)).bind fun ⟨o, es1⟩ ⟨⟨hc1, ho⟩, hg1⟩ => ?_
          dsimp only at hc1 ho hg1
          cases o with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            rcases hst with hinact | ⟨ht0, hinv⟩
            · exact NoChallPRNG.pure (Or.inl hinact)
            · refine NoChallPRNG.pure (Or.inr ⟨ht0,
                fun P => by rw [hg1]; exact hinv.vp_id P,
                fun P => by rw [hg1]; exact hinv.vp_tcur P,
                fun P => by rw [hg1]; exact hinv.ep_le P,
                fun t' ht' => ?_,
                fun r hr => by rw [hg1] at hr; exact hinv.trans_le r hr⟩)
              dsimp only
              have hne : (s1.st Pt).id.sendsIn ((s1.st Pt).tcur + 1) = true →
                  t' ≠ (s1.st Pt).tcur + 1 := by
                intro hs
                rw [hst_s1.1] at hs ⊢
                rw [hinv.vp_id Pt] at hs
                rw [hinv.vp_tcur Pt] at hs ⊢
                have := (epMgmt_le_qep hinv.ep_le hep).2 hs; omega
              rw [hc1 t' hne]; exact hinv.cache_gt t' ht'
          | some res =>
            rcases res with ⟨vp', ct⟩
            obtain ⟨hid', htcur', hct_ep⟩ := ho vp' ct rfl
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            rcases hst with hinact | ⟨ht0, hinv⟩
            · exact NoChallPRNG.pure (Or.inl hinact)
            · refine NoChallPRNG.pure (Or.inr ⟨ht0, ?_⟩)
              have hep_le_s1 := (epMgmt_le_qep hinv.ep_le hep).1
              have hs1_ep : ∀ Q, s1.epoch Q =
                  if Q = Pt ∧ Pt.sendsIn (es.g.epoch Pt + 1) then es.g.epoch Pt + 1 else es.g.epoch Q := by
                intro Q; unfold SM.GameState.epMgmt at hep
                by_cases hs : Pt.sendsIn (es.g.epoch Pt + 1) = true
                · simp only [hs, ↓reduceIte] at hep
                  split at hep
                  · simp at hep
                  · simp only [Option.some.injEq] at hep; subst hep
                    by_cases hQ : Q = Pt
                    · subst hQ; split <;> simp [SM.GameState.leak, hs]
                    · split <;> simp [SM.GameState.leak, hQ]
                · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
                  split at hep
                  · simp at hep
                  · simp only [Option.some.injEq] at hep; subst hep
                    simp [hs]
              rw [hst_s1.1] at hid' htcur' hc1
              rw [hinv.vp_id Pt] at hid' htcur' hc1
              rw [hinv.vp_tcur Pt] at htcur' hc1
              refine ⟨fun Q => ?_, fun Q => ?_, fun Q => hep_le_s1 Q, fun t' ht' => ?_, fun r hr => ?_⟩
              · dsimp only [SM.GameState.record]
                by_cases hQ : Q = Pt
                · subst hQ; simp [hid']
                · simp [hst_s1.1, hinv.vp_id Q, hQ]
              · dsimp only [SM.GameState.record]
                by_cases hQ : Q = Pt
                · subst hQ; simp [htcur', hs1_ep Q]
                · simp [hst_s1.1, hinv.vp_tcur Q, hs1_ep Q, hQ]
              · have hne : Pt.sendsIn (es.g.epoch Pt + 1) = true → t' ≠ es.g.epoch Pt + 1 := by
                  intro hs; have := (epMgmt_le_qep hinv.ep_le hep).2 hs; omega
                rw [hc1 t' hne]; exact hinv.cache_gt t' ht'
              · dsimp only [SM.GameState.record] at hr
                rcases List.mem_cons.mp hr with rfl | hr_old
                · refine ⟨hep_le_s1 Pt, ?_⟩
                  rw [hct_ep, htcur', hs1_ep Pt]
                  by_cases hs : Pt.sendsIn (es.g.epoch Pt + 1) = true <;> simp [hs]
                · exact hinv.trans_le r (hst_s1.2 ▸ hr_old)
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply, challEBucket, StateT.run_pure]
      exact NoChallPRNG.pure hst
    · rcases q3 with ⟨Pt, c⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
      · cases htr : es.g.inTransit Pt.other c with
        | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
        | some r =>
          dsimp only; rw [StateT.run_bind]
          refine (liftH_noChall es (vRecvMain_noChall cka prng fs Δcka qep tL par t0
            es.g Pt (es.g.st Pt) c (some r) es.h)).bind fun ⟨o, es1⟩ ⟨⟨hh1, ho⟩, hg1⟩ => ?_
          dsimp only at hh1 ho hg1
          rcases o with _ | (_ | ⟨vp', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact NoChallPRNG.pure (hpreserve_trivial _
              (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
          · dsimp only; split <;>
              simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
              exact NoChallPRNG.pure (hpreserve_trivial _
                (fun P => ⟨by simp [hg1], by simp [hg1], by simp [hg1]⟩)
                (by simp [hh1]) (by simp [hg1]))
          · obtain ⟨ht_eq, hle, hid', htcur', hcache_some⟩ := ho vp' t' i' m' rfl
            dsimp only [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
            simp only [AuthL11.run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind]
            rcases hst with hinact | ⟨ht0, hinv⟩
            · exact NoChallPRNG.pure (Or.inl hinact)
            · have hr_mem : r ∈ es.g.trans ∧ r.ct = c := by
                unfold SM.GameState.inTransit at htr
                have hmem := List.mem_of_find?_eq_some htr
                have hp := List.find?_some htr
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
                exact ⟨hmem, hp.2⟩
              have hr_props := hinv.trans_le r hr_mem.1
              have hpos_eq : r.pos.epoch = c.1.1 := hr_props.2.symm.trans (congrArg (fun x => x.1.1) hr_mem.2)
              have hacc := invLeQep_accept hinv hh1 (hid'.trans (hinv.vp_id Pt))
                (by rw [htcur', hinv.vp_tcur Pt, hpos_eq]) hr_props.1
              have hupd : { (es.g.accept Pt vp' r.pos) with st := Function.update (es.g.accept Pt vp' r.pos).st Pt vp' } =
                  es.g.accept Pt vp' r.pos := by
                cases es.g; simp [SM.GameState.accept]
              rw [hupd]
              split <;> exact NoChallPRNG.pure (Or.inr ⟨ht0, hacc.vp_id, hacc.vp_tcur, hacc.ep_le, hacc.cache_gt, hacc.trans_le⟩)
    · rcases q4 with ⟨Pt, c⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
      · rw [StateT.run_bind]
        refine (liftH_noChall es (vRecvMain_noChall cka prng fs Δcka qep tL par t0
          es.g Pt (es.g.st Pt) c none es.h)).bind fun ⟨o, es1⟩ ⟨⟨hh1, ho⟩, hg1⟩ => ?_
        dsimp only at hh1 ho hg1
        rcases o with _ | (_ | ⟨vp', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact NoChallPRNG.pure (hpreserve_trivial _
            (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
        · simp only [StateT.run_pure]
          exact NoChallPRNG.pure (hpreserve_trivial _
            (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
        · obtain ⟨ht_eq, hle, hid', htcur', hcache_some⟩ := ho vp' t' i' m' rfl
          subst ht_eq
          dsimp only; split
          · simp only [StateT.run_pure]
            exact NoChallPRNG.pure (hpreserve_trivial _
              (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
          · split
            · dsimp only [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
              simp only [AuthL11.run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind]
              rcases hst with hinact | ⟨ht0, hinv⟩
              · exact NoChallPRNG.pure (Or.inl hinact)
              · have hc_le_qep : c.1.1 ≤ qep := by
                  rw [hinv.vp_tcur Pt] at hle hcache_some
                  have hep_le := hinv.ep_le Pt
                  by_cases heq1 : c.1.1 = es.g.epoch Pt + 1
                  · by_contra hgt
                    have hcs := hcache_some heq1
                    have hnone := hinv.cache_gt c.1.1 (by omega)
                    rw [hnone] at hcs; simp at hcs
                  · omega
                have hacc := invLeQep_accept (pos := ⟨Pt.other, c.1.1, i'⟩) hinv hh1
                  (hid'.trans (hinv.vp_id Pt)) (by rw [htcur', hinv.vp_tcur Pt]) hc_le_qep
                have hupd : { (es.g.accept Pt vp' ⟨Pt.other, c.1.1, i'⟩) with
                    st := Function.update (es.g.accept Pt vp' ⟨Pt.other, c.1.1, i'⟩).st Pt vp' } =
                    es.g.accept Pt vp' ⟨Pt.other, c.1.1, i'⟩ := by
                  cases es.g; simp [SM.GameState.accept]
                rw [hupd]
                exact NoChallPRNG.pure (Or.inr ⟨ht0, hacc.vp_id, hacc.vp_tcur, hacc.ep_le, hacc.cache_gt, hacc.trans_le⟩)
            · split <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
                exact NoChallPRNG.pure (hpreserve_trivial _
                  (fun P => ⟨by simp [hg1], by simp [hg1], by simp [hg1]⟩)
                  (by simp [hh1]) (by simp [hg1]))
    · simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
      · rw [StateT.run_bind]
        refine (liftH_noChall es (revealMain_noChall cka prng fs Δcka qep tL par t0
          es.g P (es.g.st P) es.h)).bind fun ⟨o, es1⟩ ⟨hh1, hg1⟩ => ?_
        dsimp only at hh1 hg1
        cases o with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact NoChallPRNG.pure (hpreserve_trivial _
            (fun Q => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) hh1 (by rw [hg1]; exact fun _ h => h))
        | some stP =>
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact NoChallPRNG.pure (hpreserve_trivial _
            (fun Q => by simp [SM.GameState.afterCorr, SM.GameState.leak]) hh1
            (fun r hr => by simpa [SM.GameState.afterCorr, SM.GameState.leak] using hr))
    · rcases q6 with ⟨Pt, c, c'⟩
      simp only [implEDFPaperBucketRaw, QueryImpl.add_apply]
      unfold deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
      · cases htr : es.g.inTransit Pt.other c with
        | none => simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
        | some r =>
          dsimp only; split
          · simp only [StateT.run_pure]; exact NoChallPRNG.pure hst
          · rw [StateT.run_bind]
            refine (liftH_noChall es (vRecvMain_noChall cka prng fs Δcka qep tL par t0
              es.g Pt (es.g.st Pt) c' none es.h)).bind fun ⟨o, es1⟩ ⟨⟨hh1, ho⟩, hg1⟩ => ?_
            dsimp only at hh1 ho hg1
            rcases o with _ | (_ | ⟨vp', t', i', m'⟩)
            · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
              exact NoChallPRNG.pure (hpreserve_trivial _
                (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
            · simp only [StateT.run_pure]
              exact NoChallPRNG.pure (hpreserve_trivial _
                (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
            · obtain ⟨ht_eq, hle, hid', htcur', hcache_some⟩ := ho vp' t' i' m' rfl
              subst ht_eq
              dsimp only
              by_cases hbad_ep : (decide (qep + 1 < c'.1.1) || (c'.1.1 != r.pos.epoch)) = true
              · simp only [hbad_ep, ↓reduceIte, StateT.run_pure]
                exact NoChallPRNG.pure (hpreserve_trivial _
                  (fun P => ⟨by rw [hg1], by rw [hg1], by rw [hg1]⟩) (by rw [hh1]) (by rw [hg1]; exact fun _ h => h))
              · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
                have hc'_ep : c'.1.1 = r.pos.epoch := by
                  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hbad_ep
                  exact hbad_ep.2
                split
                · dsimp only [commitE, hooksPRNGBucketMain, hooksPRNGBucketMainGen, hooksPRNGBucketHybridGen]
                  simp only [AuthL11.run_liftH, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind]
                  rcases hst with hinact | ⟨ht0, hinv⟩
                  · exact NoChallPRNG.pure (Or.inl hinact)
                  · have hr_mem : r ∈ es.g.trans := by
                      unfold SM.GameState.inTransit at htr
                      exact List.mem_of_find?_eq_some htr
                    have hr_props := hinv.trans_le r hr_mem
                    have hacc := invLeQep_accept (pos := ⟨Pt.other, c'.1.1, i'⟩) hinv hh1
                      (hid'.trans (hinv.vp_id Pt)) (by rw [htcur', hinv.vp_tcur Pt]) (hc'_ep ▸ hr_props.1)
                    have hupd : { (es.g.accept Pt vp' ⟨Pt.other, c'.1.1, i'⟩) with
                        st := Function.update (es.g.accept Pt vp' ⟨Pt.other, c'.1.1, i'⟩).st Pt vp' } =
                        es.g.accept Pt vp' ⟨Pt.other, c'.1.1, i'⟩ := by
                      cases es.g; simp [SM.GameState.accept]
                    rw [hupd]
                    exact NoChallPRNG.pure (Or.inr ⟨ht0, hacc.vp_id, hacc.vp_tcur, hacc.ep_le, hacc.cache_gt, hacc.trans_le⟩)
                · split <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
                    exact NoChallPRNG.pure (hpreserve_trivial _
                      (fun P => ⟨by simp [hg1], by simp [hg1], by simp [hg1]⟩)
                      (by simp [hh1]) (by simp [hg1]))
  unfold implEDFPaperBucket withWinEpDF
  dsimp only [StateT.run_mk]
  exact hraw.bind fun ⟨_, _⟩ hs' => NoChallPRNG.pure hs'

private theorem simulateQ_implEDFPaperBucketMain_noChall
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    {α : Type} (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E α)
    (st : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (hst : InactiveOrLeQep (3 + Δcka) qep tL par t0 st.1) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True)
      ((simulateQ (implEDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) oa).run st) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => change NoChallPRNG _ (Pure.pure (a, st)); exact NoChallPRNG.pure trivial
  | query_bind q k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind]
    exact (implEDFPaperBucketMain_step_noChall cka prng fs Δcka qep tL par t0 q st hst).bind
      fun ⟨u, st'⟩ hst' => ih u st' hst'

private theorem redPRNGAuthDFPaperBucketMain_noChall
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hcond : isActiveBucketEpoch (3 + Δcka) tL par t0 = false ∨ t0 = qep + 1)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    NoChallPRNG (Sig := Sig) (I := I) (K := K) (fun _ => True)
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A) := by
  have hskip0 : 0 = t0 → isActiveBucketEpoch (3 + Δcka) tL par t0 = false := by
    intro h0; rcases hcond with hinact | ht0
    · exact hinact
    · omega
  unfold redPRNGAuthDFPaperBucketMain engRunDFPaperBucket initPRNGBucketHybrid
  simp only [StateT.run_bind, bind_assoc]
  refine (NoChallPRNG.lift_sampleT KC ({} : PRNGBucketState T Sig K I)).bind fun ⟨kc, h1⟩ hc1 => ?_
  dsimp only at hc1; subst h1
  refine (rootPRNGBucketHybrid_noChall prng (3 + Δcka) tL par t0 0 false lam none _
    hskip0).bind fun ⟨o, h2⟩ hc2 => ?_
  dsimp only at hc2
  cases o with
  | none =>
    simp only [StateT.run_pure, pure_bind]
    exact NoChallPRNG.pure trivial
  | some p =>
    rcases p with ⟨σ0, k0⟩
    simp only [StateT.run_pure, pure_bind, bind_assoc]
    let g0 : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E) :=
      { st := fun P => match P with
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σ0 (fs.initSender k0) (fs.initReceiver k0)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σ0 (fs.initSender k0) (fs.initReceiver k0)).2
        b := false }
    have hinit : InactiveOrLeQep (M := M) (E := E) (3 + Δcka) qep tL par t0
        { g := g0, h := h2 } := by
      rcases hcond with hinact | ht0
      · exact Or.inl hinact
      · refine Or.inr ⟨ht0, fun P => by cases P <;> rfl, fun P => by cases P <;> rfl,
          fun _ => Nat.zero_le qep, fun t' _ => congrFun hc2 t', fun _ hr => by cases hr⟩
    exact (simulateQ_implEDFPaperBucketMain_noChall cka prng fs Δcka qep tL par t0 A
      ({ g := g0, h := h2 }, none) hinit).bind fun _ _ => NoChallPRNG.pure trivial

/-- Top-epoch (`t0 = qep + 1`) zero `PRFPRNG.advantage` for `Main` (`epMgmt` caps `startSend` at
`≤ qep` and `hooksPRNGBucketMain.startRecv` makes `0` `PRFPRNG` queries). -/
theorem prng_advantage_redPRNGAuthDFPaperBucketMain_top_eq_zero_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.advantage prng
      (redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par (qep + 1) A) = 0 :=
  prng_advantage_eq_zero_of_noChall prng _
    (redPRNGAuthDFPaperBucketMain_noChall cka prng fs lam Δcka qep tL par (qep + 1) (Or.inr rfl) A)

end MainNoChallPRNG

end CryptoGames.SM.Construction.DeliverForge
