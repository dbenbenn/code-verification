/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthHooksPot

/-!
# Per-Session Query Bound for `redFSAuthDFPaperMultiBucketMode`

Establishes the `2 * q` per-session `FSMultiSpec` query bound for the mode-split
Stage-2 `(tL, par)`-bucket reduction `redFSAuthDFPaperMultiBucketMode`.-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketPot

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.FSAEAD (
  transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM (specDF)
open _root_.CryptoGames.SM.Engine (EState VP TComp coinsE)
open _root_.CryptoGames.SM.Construction (
  PartyState Header FSMultiSpec FSMultiBook FSMultiDFBucketState sampleT
  liftFSMultiDFBucket lookupMultiDFBucketF regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  initFSMultiDFBucketPaper isHonestHdrFSMultiDFBucket bucketAuthCfgGen
  redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  SchemeAdversaryDF MakesAtMostQueriesDF implEDFPaperBucketRaw
  implEDFPaperBucketMode engRunDFPaperBucketMode withWinEpDFMode)
open Computational.Proofs.E2E.SessionAuthHooksPot (
  PotBound potBound_simulateQ_run isQueryBoundP_simulateQ_run_of_zero_inr
  ShallowHooksPot coinsE_pot implEDFPaperBucketRaw_inr_pot withWinEpDF_pot)

private def sessPred {SS RS T M E : Type} (s : ℕ) :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨s', _⟩ => decide (s' = s)

private def potBucket {T Sig K I E : Type} (s : ℕ) (h : FSMultiDFBucketState T Sig K I E) : ℕ :=
  if ((h.book s).getD {}).sCorr then 0 else 1

private theorem sampleT_pot {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {P : (unifSpec + tspec).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    (α : Type) [SampleableType α] {f : α → ℕ} {b : ℕ} (hf : ∀ a, f a ≤ b) :
    PotBound P f (sampleT (tspec := tspec) α) b :=
  (PotBound.of_zero_queries hInl ($ᵗ α : ProbComp α) b).mono hf le_rfl

private theorem lift_sampleT_pot {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS : Type}
    (P : (unifSpec + tspec).Domain → Bool) (hInl : ∀ u, P (.inl u) = false)
    (α : Type) [SampleableType α] (f : HS → ℕ) (h : HS) :
    PotBound P (fun z => f z.2) ((StateT.lift (sampleT (tspec := tspec) α)).run h) (f h) := by
  rw [StateT.run_lift]
  exact (sampleT_pot hInl α (f := fun _ => f h) (fun _ => le_rfl)).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem query_eq_liftM {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl

private theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

private theorem liftFSMultiDFBucket_query_le_one {SS RS T M E Sig K I : Type} (s sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiDFBucketState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun z => b + potBucket s z.2)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) (b + 1 + potBucket s h) := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := b + potBucket s h) (by omega)).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem liftFSMultiDFBucket_query_ne {SS RS T M E Sig K I : Type} {s sIdx : ℕ}
    (hne : sIdx ≠ s)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiDFBucketState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun z => b + potBucket s z.2)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) (b + potBucket s h) := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_zero (b + potBucket s h) (by simp [sessPred, hne])).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem liftFSMultiDFBucket_query_eq {SS RS T M E Sig K I : Type} (s : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiDFBucketState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun _ => b)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        s (liftM (OracleSpec.query q₀))).run h) (b + 1) := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      s (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨s, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := b) (by omega)).bind fun _ _ hk => PotBound.pure hk

private theorem regSessMultiDFBucket_book {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (tL : Option ℕ) (t0 : ℕ) (ik : I) (s : FSMultiDFBucketState T RSt K I E) :
    (regSessMultiDFBucket L tL t0 ik s).2.book = s.book := by
  unfold regSessMultiDFBucket
  dsimp only
  split <;> rfl

private theorem regSessOptMultiDFBucket_book {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (tL : Option ℕ) (t0 : ℕ) (sid : Option I) (s : FSMultiDFBucketState T RSt K I E) :
    (regSessOptMultiDFBucket L tL t0 sid s).2.book = s.book := by
  cases sid with
  | none => rfl
  | some ik => exact regSessMultiDFBucket_book L tL t0 ik s

private theorem lookupMultiDFBucketF_pot {SS RS T M E RSt K I : Type}
    [DecidableEq I] [SampleableType K] (s : ℕ)
    (f : FSMultiDFBucketState T RSt K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiDFBucketState T RSt K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T RSt K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h) (f h) := by
  unfold lookupMultiDFBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some k => simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_pot (sessPred s) (fun _ => rfl) K f h).bind fun ⟨k, h1⟩ m hm => by
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]
      refine PotBound.pure (le_trans ?_ hm)
      exact le_of_eq (hf _ h1 rfl)

private theorem rootFSMultiDFBucketPaper_pot {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) (s : ℕ)
    (f : FSMultiDFBucketState T RSt K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiDFBucketState T RSt K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (h : FSMultiDFBucketState T RSt K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h) (f h) := by
  unfold rootFSMultiDFBucketPaper
  dsimp only
  split
  · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  · split
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) I f h).bind fun ⟨ir, h1⟩ m hm => ?_
        simp only []
        refine ((lift_sampleT_pot (sessPred s) (fun _ => rfl) K f h1).mono (fun _ => le_rfl) hm).bind
          fun ⟨kSample, h2⟩ m2 hm2 => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm2
      · simp only [StateT.run_bind]
        refine (lookupMultiDFBucketF_pot s f hf t0 ik0 h).bind fun ⟨kLookup, h1⟩ m hm => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) I f h).bind fun ⟨ir, h1⟩ m hm => ?_
        simp only []
        refine ((lift_sampleT_pot (sessPred s) (fun _ => rfl) K f h1).mono (fun _ => le_rfl) hm).bind
          fun ⟨kSample, h2⟩ m2 hm2 => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm2
      · simp only [StateT.run_pure]; exact PotBound.pure le_rfl

private theorem fsSendTailBucket_le_one {SS RS T M E Sig K I : Type}
    (s sIdx : ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z => rem + potBucket s z.2)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiDFBucketState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h)
      (rem + 1 + potBucket s h) := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind, transmitQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind
      fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by
        dsimp only [potBucket] at hm2 ⊢
        by_cases hs : sIdx = s
        · subst hs; simpa only [Function.update_self, Option.getD_some] using hm2
        · simpa only [Function.update_of_ne (Ne.symm hs)] using hm2)
  · simp only [StateT.run_bind, challengeQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind
      fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by
        dsimp only [potBucket] at hm2 ⊢
        by_cases hs : sIdx = s
        · subst hs; simpa only [Function.update_self, Option.getD_some] using hm2
        · simpa only [Function.update_of_ne (Ne.symm hs)] using hm2)

private theorem fsSendTailBucket_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z => rem + potBucket s z.2)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiDFBucketState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h)
      (rem + potBucket s h) := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind, transmitQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind
      fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by
        dsimp only [potBucket] at hm2 ⊢
        simpa only [Function.update_of_ne (Ne.symm hne)] using hm2)
  · simp only [StateT.run_bind, challengeQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind
      fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by
        dsimp only [potBucket] at hm2 ⊢
        simpa only [Function.update_of_ne (Ne.symm hne)] using hm2)

private theorem fsRecvTailBucket_le_one {SS RS T M E Sig K I : Type}
    (s sIdx : ℕ) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z => rem + potBucket s z.2)
      ((do
        let res ← if matched.isSome then
            liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiDFBucketState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + 1 + potBucket s h) := by
  by_cases hm : matched.isSome = true
  · simp only [hm, ↓reduceIte, StateT.run_bind, deliverQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind
      fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        let b0 := (h1.book sIdx).getD {}
        let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
        let b' : FSMultiBook T E := { b0 with fsTrans := b0.fsTrans.filter (·.1 != drop) }
        have hbk_eq : potBucket s { h1 with book := Function.update h1.book sIdx (some b') } =
            potBucket s h1 := by
          by_cases hs : sIdx = s
          · subst hs; simp [potBucket, b', b0, Function.update_self]
          · simp [potBucket, Function.update_of_ne (Ne.symm hs)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, injectQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind
      fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        let b0 := (h1.book sIdx).getD {}
        let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
        let b' : FSMultiBook T E := { b0 with fsTrans := b0.fsTrans.filter (·.1 != drop) }
        have hbk_eq : potBucket s { h1 with book := Function.update h1.book sIdx (some b') } =
            potBucket s h1 := by
          by_cases hs : sIdx = s
          · subst hs; simp [potBucket, b', b0, Function.update_self]
          · simp [potBucket, Function.update_of_ne (Ne.symm hs)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)

private theorem fsRecvTailBucket_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z => rem + potBucket s z.2)
      ((do
        let res ← if matched.isSome then
            liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiDFBucketState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + potBucket s h) := by
  by_cases hm : matched.isSome = true
  · simp only [hm, ↓reduceIte, StateT.run_bind, deliverQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind
      fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        let b0 := (h1.book sIdx).getD {}
        let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
        let b' : FSMultiBook T E := { b0 with fsTrans := b0.fsTrans.filter (·.1 != drop) }
        have hbk_eq : potBucket s { h1 with book := Function.update h1.book sIdx (some b') } =
            potBucket s h1 := by
          simp [potBucket, Function.update_of_ne (Ne.symm hne)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, injectQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind
      fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        let b0 := (h1.book sIdx).getD {}
        let drop := (matched.map fun x : ℕ × Header T × E => x.1).getD i
        let b' : FSMultiBook T E := { b0 with fsTrans := b0.fsTrans.filter (·.1 != drop) }
        have hbk_eq : potBucket s { h1 with book := Function.update h1.book sIdx (some b') } =
            potBucket s h1 := by
          simp [potBucket, Function.update_of_ne (Ne.symm hne)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]
          exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)

private theorem hooksFSMultiDFBucketPaper_shallowHooksPot
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (s : ℕ) :
    ShallowHooksPot (sessPred s) (potBucket s)
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) where
  inl_false _ := rfl
  startSend_pot ctx _ t0 γ0 σ0 r0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]
    have hbk : ∀ h₁ h₂ : FSMultiDFBucketState T RSt K I E,
        h₁.book = h₂.book → rem + potBucket s h₁ = rem + potBucket s h₂ :=
      fun _ _ hb => by simp [potBucket, hb]
    rcases r0 with _ | c
    · simp only [StateT.run_bind]
      refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) CCoins
        (fun x => rem + potBucket s x) h).bind fun ⟨coins, h1⟩ m1 hm1 => ?_
      simp only []
      refine ((rootFSMultiDFBucketPaper_pot prng Δbucket qep tL par t0 _
        (cka.send γ0 coins).2.2 σ0 s _ hbk h1).mono (fun _ => le_rfl) hm1).bind
        fun ⟨⟨σ', kVal, sid⟩, h2⟩ m2 hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
      refine PotBound.pure ?_
      dsimp only [potBucket] at hm2 ⊢
      rw [regSessOptMultiDFBucket_book]
      exact hm2
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine (rootFSMultiDFBucketPaper_pot prng Δbucket qep tL par t0 _
        (cka.send γ0 c).2.2 σ0 s _ hbk h).bind fun ⟨⟨σ', kVal, sid⟩, h2⟩ m2 hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, pure_bind]
      refine PotBound.pure ?_
      dsimp only [potBucket] at hm2 ⊢
      rw [regSessOptMultiDFBucket_book]
      exact hm2
  startRecv_pot ctx _ t0 γ0 σ0 tn0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]
    have hbk : ∀ h₁ h₂ : FSMultiDFBucketState T RSt K I E,
        h₁.book = h₂.book → rem + potBucket s h₁ = rem + potBucket s h₂ :=
      fun _ _ hb => by simp [potBucket, hb]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
    · split
      · split
        · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
        · split
          · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
          · simp only [StateT.run_bind]
            refine (lookupMultiDFBucketF_pot s _ hbk t0 (cka.receive γ0 tn0).2 h).bind
              fun ⟨_, h1⟩ m1 hm1 => ?_
            simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
            refine PotBound.pure ?_
            dsimp only [potBucket] at hm1 ⊢
            rw [regSessMultiDFBucket_book]
            exact hm1
      · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  fsSend_pot ctx Pt _ ssv hdr m pair h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases ssv with ss | sIdx
    · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only; omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hs : sIdx = s
      · subst hs
        split
        · next hcond =>
          have hsCorr : ((h.book sIdx).getD {}).sCorr = false := by
            revert hcond; cases ((h.book sIdx).getD {}).sCorr <;> simp
          have hpot : potBucket sIdx h = 1 := by simp [potBucket, hsCorr]
          simp only [StateT.run_bind]
          refine ((liftFSMultiDFBucket_query_eq sIdx _ h (rem + 1)).mono (fun _ => le_rfl)
            (by omega)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; split <;> omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact (fsSendTailBucket_le_one sIdx sIdx hdr m pair _ rem).mono (fun _ => le_rfl)
              (by simp only [potBucket, Function.update_self, Option.getD_some, ↓reduceIte]; omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact fsSendTailBucket_le_one sIdx sIdx hdr m pair h rem
      · split
        · simp only [StateT.run_bind]
          refine (liftFSMultiDFBucket_query_ne hs _ h (rem + 1)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only at hm1 ⊢; omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact (fsSendTailBucket_ne hs hdr m pair _ rem).mono (fun _ => le_rfl) (by
              simp only [potBucket, Function.update_of_ne (Ne.symm hs)] at hm1 ⊢
              omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsSendTailBucket_ne hs hdr m pair h rem).mono (fun _ => le_rfl) (by omega)
  fsRecv_pot ctx _ t0 rsv hdr e rec h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases rsv with rs | sIdx
    · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only; omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hs : sIdx = s
      · subst hs
        split
        · next hcond =>
          have hsCorr : ((h.book sIdx).getD {}).sCorr = false := by
            revert hcond; cases ((h.book sIdx).getD {}).sCorr <;> simp
          have hpot : potBucket sIdx h = 1 := by simp [potBucket, hsCorr]
          simp only [StateT.run_bind]
          refine ((liftFSMultiDFBucket_query_eq sIdx _ h (rem + 1)).mono (fun _ => le_rfl)
            (by omega)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; split <;> omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine (fsRecvTailBucket_le_one sIdx sIdx la _ hdr e rec _ rem).mono (fun _ => le_rfl) ?_
            simp only [potBucket, Function.update_self, Option.getD_some, ↓reduceIte]
            omega
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact fsRecvTailBucket_le_one sIdx sIdx la _ hdr e rec h rem
      · split
        · simp only [StateT.run_bind]
          refine (liftFSMultiDFBucket_query_ne hs _ h (rem + 1)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only at hm1 ⊢; omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine (fsRecvTailBucket_ne hs la _ hdr e rec _ rem).mono (fun _ => le_rfl) ?_
            dsimp only at hm1
            simp only [potBucket, Function.update_of_ne (Ne.symm hs)] at hm1 ⊢
            omega
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine (fsRecvTailBucket_ne hs la _ hdr e rec h rem).mono (fun _ => le_rfl) ?_
          omega
  commit_pot _ _ _ new h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]; simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  reveal_pot _ _ vp h rem := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases hvs : vp.vS with _ | (ss | sIdx)
    · simp only [pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure (by dsimp only; omega)
    · simp only [pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure (by dsimp only; omega)
    · simp only [StateT.run_bind]
      refine (liftFSMultiDFBucket_query_le_one s sIdx _ h rem).bind fun ⟨o, h1⟩ m1 hm1 => ?_
      rcases o with _ | ss
      · simp only [StateT.run_pure, pure_bind]; exact PotBound.pure hm1
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hm1' : rem + potBucket s
            (let b := (h1.book sIdx).getD {}
             { h1 with book := Function.update h1.book sIdx (some { b with sCorr := true }) }) ≤ m1 := by
          dsimp only [potBucket] at hm1 ⊢
          by_cases hs : sIdx = s
          · subst hs; simp [Function.update_self]; omega
          · simpa only [Function.update_of_ne (Ne.symm hs)] using hm1
        split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure hm1'

private theorem hooksFSMultiDFBucketPaperMode_shallowHooksPot
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) (s : ℕ) :
    ShallowHooksPot (sessPred s) (potBucket s)
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la) where
  inl_false _ := rfl
  startSend_pot ctx P t0 γ0 σ0 r0 h rem :=
    (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).startSend_pot
      ctx P t0 γ0 σ0 r0 h rem
  startRecv_pot ctx P t0 γ0 σ0 tn0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode]
    cases gMain
    · exact (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).startRecv_pot
        ctx P t0 γ0 σ0 tn0 h rem
    · simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
      · split <;> simp only [StateT.run_pure] <;> exact PotBound.pure le_rfl
  fsSend_pot ctx P b ssv hdr m pair h rem :=
    (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).fsSend_pot
      ctx P b ssv hdr m pair h rem
  fsRecv_pot ctx P t0 rsv hdr e rec h rem :=
    (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).fsRecv_pot
      ctx P t0 rsv hdr e rec h rem
  commit_pot ctx P b new h rem :=
    (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).commit_pot
      ctx P b new h rem
  reveal_pot ctx P vp h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode]
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only; omega)
      · exact (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).reveal_pot
          ctx P vp h rem
    · exact (hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s).reveal_pot
        ctx P vp h rem

private theorem withWinEpDFMode_pot {St Msg Coins T' E' VPt HS : Type}
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {P : (unifSpec + tspec).Domain → Bool} {pot : HS → ℕ}
    (gMain : Bool) (isHonestHdr : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins (Header T' × E')).Domain)
    (st : EState VPt Msg (Header T' × E') HS × Option ℕ) {rem b : ℕ}
    (h : PotBound P (fun z => rem + pot z.2.h) ((impl t).run st.1) b) :
    PotBound P (fun z => rem + pot z.2.1.h)
      ((withWinEpDFMode gMain isHonestHdr epOf impl t).run st) b := by
  cases gMain
  · unfold withWinEpDFMode
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.run_mk]
    exact h.bind fun ⟨r', s'⟩ k hk => PotBound.pure (by dsimp only at hk ⊢; exact hk)
  · unfold withWinEpDFMode
    simp only [↓reduceIte]
    exact withWinEpDF_pot (pot := fun es => pot es.h) (rem := rem) _ _ impl t st h

private theorem initFSMultiDFBucketPaper_pot {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (s n : ℕ) :
    PotBound (sessPred s) (fun _ => n)
      ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run
        ({} : FSMultiDFBucketState T RSt K I E)) n := by
  unfold initFSMultiDFBucketPaper
  simp only [StateT.run_bind]
  refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) KR (fun _ => n)
    ({} : FSMultiDFBucketState T RSt K I E)).bind fun ⟨kr, h1⟩ m1 hm1 => ?_
  simp only []
  refine ((lift_sampleT_pot (sessPred s) (fun _ => rfl) KC (fun _ => n) h1).mono
    (fun _ => le_rfl) hm1).bind fun ⟨kc, h2⟩ m2 hm2 => ?_
  simp only []
  refine ((rootFSMultiDFBucketPaper_pot (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng Δbucket qep tL par 0 false lam (prng.init kr) s (fun _ => n) (fun _ _ _ => rfl) h2).mono
    (fun _ => le_rfl) hm2).bind fun ⟨⟨σ, kVal, sid⟩, h3⟩ m3 hm3 => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  exact PotBound.pure hm3

private theorem hq_to_isInrQuery {Γ T RSt SS RS M CCoins E : Type} {q : ℕ}
    {A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E} (hq : MakesAtMostQueriesDF A q) :
    A.IsQueryBoundP (fun x => x.isRight = true) q := by
  unfold MakesAtMostQueriesDF at hq
  convert hq using 1; funext x; rcases x with _ | _ <;> rfl

/-- Per-session `min (2 * q) (q + 2)` query bound on `redFSAuthDFPaperMultiBucketMode`. -/
theorem redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucketMode L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) := by
  suffices h :
      (redFSAuthDFPaperMultiBucketMode L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
        (fun x => sessPred s x = true) (min (2 * q) (q + 2)) by
    convert h using 1; funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  have hq' := hq_to_isInrQuery hq
  unfold redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode
    implEDFPaperBucketMode
  rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDFMode gMain isHonestHdrFSMultiDFBucket (fun vp => vp.tcur) rawImpl
  have hkPot := hooksFSMultiDFBucketPaperMode_shallowHooksPot L cka prng fs Δcka Δbucket qep gMain tL par la s
  rcases q with _ | q'
  · refine (isQueryBoundP_bind (m := 0)
      (initFSMultiDFBucketPaper_pot L cka prng fs lam Δbucket qep tL par s 0).to_isQueryBoundP
      fun ⟨vs, h⟩ _ => ?_).mono (by omega)
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact isQueryBoundP_pure _ _ 0
    · simp only [bind_assoc]
      exact isQueryBoundP_bind
        (isQueryBoundP_simulateQ_run_of_zero_inr (sessPred s) impl
          (fun u st => (withWinEpDFMode_pot (pot := fun _ => 0) (rem := 0) gMain _ _ rawImpl (.inl u) st
            (coinsE_pot (pot := fun _ => 0) (fun _ => rfl) u st.1 0)).to_isQueryBoundP)
          A hq' _)
        fun _ _ => isQueryBoundP_pure _ _ 0
  · have hInit := (initFSMultiDFBucketPaper_pot L cka prng fs lam Δbucket qep tL par s (q' + 2)).mono
      (fun z => show (q' + 1) + potBucket s z.2 ≤ q' + 2 by dsimp [potBucket]; split <;> omega)
      le_rfl
    refine (hInit.bind (post := fun _ => 0) fun ⟨vs, h⟩ m hm => ?_).to_isQueryBoundP.mono (by omega)
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact PotBound.pure (Nat.zero_le m)
    · simp only [bind_assoc]
      let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiDFBucketState T RSt K I E) :=
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
      exact ((potBound_simulateQ_run (sessPred s) (fun st => potBucket s st.1.h) impl
        (fun u st rem => withWinEpDFMode_pot (pot := potBucket s) (rem := rem) gMain _ _
          rawImpl (.inl u) st (coinsE_pot (fun _ => rfl) u st.1 rem))
        (fun qr st rem => withWinEpDFMode_pot (pot := potBucket s) (rem := rem) gMain _ _
          rawImpl (.inr qr) st
          (implEDFPaperBucketRaw_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ qr st.1 rem))
        (q' + 1) A hq' (es₀, none)).mono (fun _ => Nat.zero_le _) hm).bind fun _ m2 _ =>
        PotBound.pure (Nat.zero_le m2)

/-- Per-session `2 * q` query bound on `redFSAuthDFPaperMultiBucketMode`. -/
theorem redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucketMode L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min L cka prng fs lam q Δcka Δbucket qep
    gMain tL par la A hq s).mono (Nat.min_le_left _ _)

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketPot
