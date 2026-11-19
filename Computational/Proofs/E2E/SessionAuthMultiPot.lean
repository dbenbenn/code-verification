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
import Computational.Proofs.E2E.SessionAuthHooksPot

/-!
# Per-Session Query Bounds for Multi-Session Stage-2 `DeliverForgePaper` Reductions

Establishes the `2 * q` per-session `FSMultiSpec` query bounds for
`redFSAuthDFShiftedPaperMultiGen`, `redFSAuthDFPaperMulti`, and `redFSAuthDFPaperMultiBucket`.-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiPot

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.FSAEAD (
  transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM.Engine (EState VP authOut TComp coinsE)
open _root_.CryptoGames.SM.Construction (PartyState Header Mode sampleT mkParties
  FSMultiSpec FSMultiState FSMultiBook hooksFSMulti rootFSMulti initFSMultiRaw
  liftFSMulti lookupMultiF regSessMulti regSessOptMulti
  FSMultiDFBucketState hooksFSMultiDFBucketPaper rootFSMultiDFBucketPaper
  initFSMultiDFBucketPaper liftFSMultiDFBucket lookupMultiDFBucketF
  regSessMultiDFBucket regSessOptMultiDFBucket
  bucketAuthCfgGen runFSMultiDFPaper
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (SchemeAdversaryDF
  MakesAtMostQueriesDF implEDFPaper implEDFShiftedPaperGen engRunDFPaperBucket authOutBucket
  implEDFPaperBucket implEDFPaperBucketRaw withWinEpDF)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper redFSAuthDFShiftedPaperMultiGen)
open Computational.Proofs.E2E.SessionAuthHooksPot (
  PotBound potBound_simulateQ_run isQueryBoundP_simulateQ_run_of_zero_inr
  ShallowHooksPot coinsE_pot implEDFShiftedPaperGen_inr_pot implEDFPaper_inr_pot
  implEDFPaperBucketRaw_inr_pot withWinEpDF_pot)

private def sessPred {SS RS T M E : Type} (s : ℕ) :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨s', _⟩ => decide (s' = s)

private def potMulti {T Sig K I E : Type} (s : ℕ) (h : FSMultiState T Sig K I E) : ℕ :=
  if ((h.book s).getD {}).sCorr then 0 else 1

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

private theorem liftFSMulti_query_le_one {SS RS T M E Sig K I : Type} (s sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun z => b + potMulti s z.2)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h)
      (b + 1 + potMulti s h) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := b + potMulti s h) (by omega)).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem liftFSMulti_query_ne {SS RS T M E Sig K I : Type} {s sIdx : ℕ} (hne : sIdx ≠ s)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun z => b + potMulti s z.2)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h)
      (b + potMulti s h) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_zero (b + potMulti s h) (by simp [sessPred, hne])).bind fun _ _ hk =>
    PotBound.pure (by dsimp only; exact hk)

private theorem liftFSMulti_query_eq {SS RS T M E Sig K I : Type} (s : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiState T Sig K I E) (b : ℕ) :
    PotBound (sessPred s) (fun _ => b)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        s (liftM (OracleSpec.query q₀))).run h)
      (b + 1) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      s (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨s, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]
    simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := b) (by omega)).bind fun _ _ hk => PotBound.pure hk

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

private theorem lookupMultiF_pot {SS RS T M E Sig K I : Type} [DecidableEq I] [SampleableType K]
    (s : ℕ) (f : FSMultiState T Sig K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiState T Sig K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (Ik : I) (h : FSMultiState T Sig K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h) (f h) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some k => simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_pot (sessPred s) (fun _ => rfl) K f h).bind fun ⟨k, h1⟩ m hm => by
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]
      refine PotBound.pure (le_trans ?_ hm)
      exact le_of_eq (hf _ h1 rfl)

private theorem regSessMulti_pot {SS RS T M E Sig K I : Type} [DecidableEq I]
    (s : ℕ) (f : FSMultiState T Sig K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiState T Sig K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (Ik : I) (h : FSMultiState T Sig K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h) (f h) := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    exact PotBound.pure (le_of_eq (hf _ h rfl))

private theorem regSessOptMulti_pot {SS RS T M E Sig K I : Type} [DecidableEq I]
    (s : ℕ) (f : FSMultiState T Sig K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiState T Sig K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (sid : Option I) (h : FSMultiState T Sig K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h) (f h) := by
  cases sid with
  | none => simp only [regSessOptMulti, StateT.run_pure]; exact PotBound.pure le_rfl
  | some Ik =>
    simp only [regSessOptMulti, StateT.run_map]
    exact (regSessMulti_pot s f hf Ik h).map fun _ => le_rfl

private theorem rootFSMulti_pot {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt)
    (s : ℕ) (f : FSMultiState T RSt K I E → ℕ)
    (hf : ∀ h₁ h₂ : FSMultiState T RSt K I E, h₁.book = h₂.book → f h₁ = f h₂)
    (h : FSMultiState T RSt K I E) :
    PotBound (sessPred s) (fun z => f z.2)
      ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t Ik σ).run h)
      (f h) := by
  unfold rootFSMulti
  split
  · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  · split
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) I f h).bind fun ⟨Ir, h1⟩ m hm => ?_
        simp only []
        refine ((lift_sampleT_pot (sessPred s) (fun _ => rfl) K f h1).mono (fun _ => le_rfl) hm).bind
          fun ⟨k, h2⟩ m2 hm2 => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm2
      · simp only [StateT.run_bind]
        refine (lookupMultiF_pot s f hf Ik h).bind fun ⟨k, h1⟩ m hm => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) I f h).bind fun ⟨Ir, h1⟩ m hm => ?_
        simp only [StateT.run_pure]; exact PotBound.pure hm
      · simp only [StateT.run_pure]; exact PotBound.pure le_rfl

private theorem fsSendTailMulti_le_one {SS RS T M E Sig K I : Type}
    (s sIdx : ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option ((SS ⊕ ℕ) × E) × FSMultiState T Sig K I E => rem + potMulti s z.2)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMulti sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMulti sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h)
      (rem + 1 + potMulti s h) := by
  rcases pair with _ | ⟨m₀, m₁⟩ <;> ·
    simp only [StateT.run_bind, challengeQuery, transmitQuery, query_eq_liftM]
    refine (liftFSMulti_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      refine PotBound.pure (by
        dsimp only [potMulti] at hm2 ⊢
        by_cases hs : sIdx = s
        · subst hs; simpa only [Function.update_self, Option.getD_some] using hm2
        · simpa only [Function.update_of_ne (Ne.symm hs)] using hm2)

private theorem fsSendTailMulti_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option ((SS ⊕ ℕ) × E) × FSMultiState T Sig K I E => rem + potMulti s z.2)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMulti sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMulti sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h)
      (rem + potMulti s h) := by
  rcases pair with _ | ⟨m₀, m₁⟩ <;> ·
    simp only [StateT.run_bind, challengeQuery, transmitQuery, query_eq_liftM]
    refine (liftFSMulti_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only [potMulti] at hm2 ⊢; simpa only [Function.update_of_ne (Ne.symm hne)] using hm2)

private theorem fsRecvTailMulti_le_one {SS RS T M E Sig K I : Type}
    (s sIdx : ℕ) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiState T Sig K I E => rem + potMulti s z.2)
      ((do
        let res ← if matched.isSome then
            liftFSMulti sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMulti sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map Prod.fst).getD i
            modify fun (st : FSMultiState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + 1 + potMulti s h) := by
  rcases matched with _ | ⟨c0, h0, e0⟩ <;> ·
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, deliverQuery, injectQuery, query_eq_liftM]
    refine (liftFSMulti_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potMulti] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hbk_eq : ∀ b' : FSMultiBook T E, b'.sCorr = ((h1.book sIdx).getD {}).sCorr →
            potMulti s { h1 with book := Function.update h1.book sIdx (some b') } = potMulti s h1 := fun b' hb' => by
          by_cases hs : sIdx = s
          · subst hs; simp [potMulti, Function.update_self, hb']
          · simp [potMulti, Function.update_of_ne (Ne.symm hs)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1; rfl)
        · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1; rfl)

private theorem fsRecvTailMulti_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiState T Sig K I E => rem + potMulti s z.2)
      ((do
        let res ← if matched.isSome then
            liftFSMulti sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMulti sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map Prod.fst).getD i
            modify fun (st : FSMultiState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + potMulti s h) := by
  rcases matched with _ | ⟨c0, h0, e0⟩ <;> ·
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, deliverQuery, injectQuery, query_eq_liftM]
    refine (liftFSMulti_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potMulti] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hbk_eq : ∀ b' : FSMultiBook T E, potMulti s { h1 with book := Function.update h1.book sIdx (some b') } = potMulti s h1 :=
          fun _ => by simp [potMulti, Function.update_of_ne (Ne.symm hne)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)

private theorem hooksFSMulti_shallowHooksPot
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (s : ℕ) :
    ShallowHooksPot (sessPred s) (potMulti s) (hooksFSMulti cka prng fs Δcka mo gMain la) where
  inl_false _ := rfl
  startSend_pot _ _ t γ σ r h rem := by
    dsimp only [hooksFSMulti]
    have hbk : ∀ h₁ h₂ : FSMultiState T RSt K I E,
        h₁.book = h₂.book → rem + potMulti s h₁ = rem + potMulti s h₂ :=
      fun _ _ hb => by simp [potMulti, hb]
    rcases r with _ | c
    · simp only [StateT.run_bind]
      refine (lift_sampleT_pot (sessPred s) (fun _ => rfl) CCoins
        (fun x => rem + potMulti s x) h).bind fun ⟨coins, h1⟩ m1 hm1 => ?_
      simp only []
      refine ((rootFSMulti_pot prng mo t (cka.send γ coins).2.2 σ s _ hbk h1).mono
        (fun _ => le_rfl) hm1).bind fun ⟨⟨σ', k, sid⟩, h2⟩ m2 hm2 => ?_
      simp only []
      refine ((regSessOptMulti_pot s _ hbk sid h2).mono (fun _ => le_rfl) hm2).bind
        fun ⟨optIdx, h3⟩ m3 hm3 => ?_
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only [potMulti] at hm3 ⊢; exact hm3)
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine (rootFSMulti_pot prng mo t (cka.send γ c).2.2 σ s _ hbk h).bind
        fun ⟨⟨σ', k, sid⟩, h2⟩ m2 hm2 => ?_
      simp only []
      refine ((regSessOptMulti_pot s _ hbk sid h2).mono (fun _ => le_rfl) hm2).bind
        fun ⟨optIdx, h3⟩ m3 hm3 => ?_
      simp only [StateT.run_modify, pure_bind]
      exact PotBound.pure (by dsimp only [potMulti] at hm3 ⊢; exact hm3)
  startRecv_pot _ _ t γ σ Tn h rem := by
    dsimp only [hooksFSMulti]
    have hbk : ∀ h₁ h₂ : FSMultiState T RSt K I E,
        h₁.book = h₂.book → rem + potMulti s h₁ = rem + potMulti s h₂ :=
      fun _ _ hb => by simp [potMulti, hb]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
    · split
      · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
      · split
        · split
          · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
          · simp only [StateT.run_bind]
            refine (lookupMultiF_pot s _ hbk (cka.receive γ Tn).2 h).bind fun ⟨_, h1⟩ m1 hm1 => ?_
            simp only []
            refine ((regSessMulti_pot s _ hbk (cka.receive γ Tn).2 h1).mono
              (fun _ => le_rfl) hm1).bind fun ⟨sIdx, h2⟩ m2 hm2 => ?_
            simp only [StateT.run_pure]; exact PotBound.pure hm2
        · simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  fsSend_pot ctx Pt _ ssv hdr m pair h rem := by
    dsimp only [hooksFSMulti]
    rcases ssv with ss | sIdx
    · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only; omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hs : sIdx = s
      · subst hs
        split
        · next hcond =>
          have hsCorr : ((h.book sIdx).getD {}).sCorr = false := by
            revert hcond; cases ((h.book sIdx).getD {}).sCorr <;> simp
          have hpot : potMulti sIdx h = 1 := by simp [potMulti, hsCorr]
          cases la with
          | true =>
            simp only [↓reduceIte, StateT.run_pure, Bool.not_false]
            exact PotBound.pure (by dsimp only; omega)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
            refine ((liftFSMulti_query_eq sIdx _ h (rem + 1)).mono (fun _ => le_rfl)
              (by omega)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
            rcases o with _ | _
            · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
              exact PotBound.pure (by dsimp only [potMulti] at hm1 ⊢; split <;> omega)
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact (fsSendTailMulti_le_one sIdx sIdx hdr m pair _ rem).mono (fun _ => le_rfl)
                (by simp only [potMulti, Function.update_self, Option.getD_some, ↓reduceIte]; omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact fsSendTailMulti_le_one sIdx sIdx hdr m pair h rem
      · split
        · split
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only; omega)
          · simp only [StateT.run_bind]
            refine (liftFSMulti_query_ne hs _ h (rem + 1)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
            rcases o with _ | _
            · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
              exact PotBound.pure (by dsimp only at hm1 ⊢; omega)
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact (fsSendTailMulti_ne hs hdr m pair _ rem).mono (fun _ => le_rfl) (by
                simp only [potMulti, Function.update_of_ne (Ne.symm hs)] at hm1 ⊢
                omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsSendTailMulti_ne hs hdr m pair h rem).mono (fun _ => le_rfl) (by omega)
  fsRecv_pot ctx _ t0 rsv hdr e rec h rem := by
    dsimp only [hooksFSMulti]
    rcases rsv with rs | sIdx
    · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only; omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hs : sIdx = s
      · subst hs
        split
        · next hcond =>
          have hsCorr : ((h.book sIdx).getD {}).sCorr = false := by
            revert hcond; cases ((h.book sIdx).getD {}).sCorr <;> simp
          have hpot : potMulti sIdx h = 1 := by simp [potMulti, hsCorr]
          cases la with
          | true =>
            simp only [↓reduceIte, StateT.run_pure, Bool.not_false]
            exact PotBound.pure (by dsimp only; omega)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
            refine ((liftFSMulti_query_eq sIdx _ h (rem + 1)).mono (fun _ => le_rfl)
              (by omega)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
            rcases o with _ | _
            · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
              exact PotBound.pure (by dsimp only [potMulti] at hm1 ⊢; split <;> omega)
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact (fsRecvTailMulti_le_one sIdx sIdx false _ hdr e rec _ rem).mono (fun _ => le_rfl)
                (by simp only [potMulti, Function.update_self, Option.getD_some, ↓reduceIte]; omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact fsRecvTailMulti_le_one sIdx sIdx la _ hdr e rec h rem
      · split
        · split
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
            exact PotBound.pure (by dsimp only; omega)
          · simp only [StateT.run_bind]
            refine (liftFSMulti_query_ne hs _ h (rem + 1)).bind fun ⟨o, h1⟩ m1 hm1 => ?_
            rcases o with _ | _
            · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
              exact PotBound.pure (by dsimp only at hm1 ⊢; omega)
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact (fsRecvTailMulti_ne hs la _ hdr e rec _ rem).mono (fun _ => le_rfl) (by
                simp only [potMulti, Function.update_of_ne (Ne.symm hs)] at hm1 ⊢
                omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsRecvTailMulti_ne hs la _ hdr e rec h rem).mono (fun _ => le_rfl) (by omega)
  commit_pot _ _ _ new h rem := by
    dsimp only [hooksFSMulti]; simp only [StateT.run_pure]; exact PotBound.pure le_rfl
  reveal_pot _ _ vp h rem := by
    dsimp only [hooksFSMulti]
    rcases hvs : vp.vS with _ | (ss | sIdx)
    · simp only [pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure (by dsimp only; omega)
    · simp only [pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure (by dsimp only; omega)
    · simp only []
      cases la with
      | true =>
        simp only [↓reduceIte, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only; omega)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_query_le_one s sIdx _ h rem).bind fun ⟨o, h1⟩ m1 hm1 => ?_
        rcases o with _ | ss
        · simp only [StateT.run_pure, pure_bind]; exact PotBound.pure hm1
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
          have hm1' : rem + potMulti s
              (let b := (h1.book sIdx).getD {}
               { h1 with book := Function.update h1.book sIdx (some { b with sCorr := true }) }) ≤ m1 := by
            dsimp only [potMulti] at hm1 ⊢
            by_cases hs : sIdx = s
            · subst hs; simp [Function.update_self]; omega
            · simpa only [Function.update_of_ne (Ne.symm hs)] using hm1
          split_ifs <;> simp only [StateT.run_pure] <;> exact PotBound.pure hm1'

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
    PotBound (sessPred s) (fun z : Option ((SS ⊕ ℕ) × E) × FSMultiDFBucketState T Sig K I E => rem + potBucket s z.2)
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
  rcases pair with _ | ⟨m₀, m₁⟩ <;> ·
    simp only [StateT.run_bind, challengeQuery, transmitQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      refine PotBound.pure (by
        dsimp only [potBucket] at hm2 ⊢
        by_cases hs : sIdx = s
        · subst hs; simpa only [Function.update_self, Option.getD_some] using hm2
        · simpa only [Function.update_of_ne (Ne.symm hs)] using hm2)

private theorem fsSendTailBucket_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option ((SS ⊕ ℕ) × E) × FSMultiDFBucketState T Sig K I E => rem + potBucket s z.2)
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
  rcases pair with _ | ⟨m₀, m₁⟩ <;> ·
    simp only [StateT.run_bind, challengeQuery, transmitQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind fun ⟨e?, h2⟩ m2 hm2 => ?_
    rcases e? with _ | e
    · simp only [StateT.run_pure]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PotBound.pure (by dsimp only [potBucket] at hm2 ⊢; simpa only [Function.update_of_ne (Ne.symm hne)] using hm2)

private theorem fsRecvTailBucket_le_one {SS RS T M E Sig K I : Type}
    (s sIdx : ℕ) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiDFBucketState T Sig K I E => rem + potBucket s z.2)
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
            let drop := (matched.map Prod.fst).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + 1 + potBucket s h) := by
  rcases matched with _ | ⟨c0, h0, e0⟩ <;> ·
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, deliverQuery, injectQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_le_one (SS := SS) (RS := RS) (M := M) s sIdx _ h rem).bind fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hbk_eq : ∀ b' : FSMultiBook T E, b'.sCorr = ((h1.book sIdx).getD {}).sCorr →
            potBucket s { h1 with book := Function.update h1.book sIdx (some b') } = potBucket s h1 := fun b' hb' => by
          by_cases hs : sIdx = s
          · subst hs; simp [potBucket, Function.update_self, hb']
          · simp [potBucket, Function.update_of_ne (Ne.symm hs)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1; rfl)
        · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1; rfl)

private theorem fsRecvTailBucket_ne {SS RS T M E Sig K I : Type}
    {s sIdx : ℕ} (hne : sIdx ≠ s) (la : Bool) (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (sessPred s) (fun z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiDFBucketState T Sig K I E => rem + potBucket s z.2)
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
            let drop := (matched.map Prod.fst).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h)
      (rem + potBucket s h) := by
  rcases matched with _ | ⟨c0, h0, e0⟩ <;> ·
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, deliverQuery, injectQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne (SS := SS) (RS := RS) (M := M) hne _ h rem).bind fun ⟨res, h1⟩ m1 hm1 => ?_
    rcases res with _ | (_ | ⟨i, mo'⟩)
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_pure]; exact PotBound.pure hm1
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PotBound.pure (by dsimp only [potBucket] at hm1 ⊢; exact hm1)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hbk_eq : ∀ b' : FSMultiBook T E, potBucket s { h1 with book := Function.update h1.book sIdx (some b') } = potBucket s h1 :=
          fun _ => by simp [potBucket, Function.update_of_ne (Ne.symm hne)]
        rcases mo' with _ | m
        · rcases rec with _ | r <;> simp only [StateT.run_pure] <;>
            exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)
        · simp only [StateT.run_pure]; exact PotBound.pure (by dsimp only at hm1 ⊢; rw [hbk_eq]; exact hm1)

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
            exact (fsRecvTailBucket_le_one sIdx sIdx la _ hdr e rec _ rem).mono (fun _ => le_rfl)
              (by simp only [potBucket, Function.update_self, Option.getD_some, ↓reduceIte]; omega)
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
            exact (fsRecvTailBucket_ne hs la _ hdr e rec _ rem).mono (fun _ => le_rfl) (by
              simp only [potBucket, Function.update_of_ne (Ne.symm hs)] at hm1 ⊢
              omega)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsRecvTailBucket_ne hs la _ hdr e rec h rem).mono (fun _ => le_rfl) (by omega)
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

private theorem initFSMultiRaw_pot {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) (s n : ℕ) :
    PotBound (sessPred s) (fun _ => n) (initFSMultiRaw cka prng fs lam mo b) n := by
  unfold initFSMultiRaw
  refine (sampleT_pot (fun _ => rfl) KR (f := fun _ => n) (fun _ => le_rfl)).bind fun kr m1 hm1 => ?_
  refine ((sampleT_pot (fun _ => rfl) KC (f := fun _ => n) (fun _ => le_rfl)).mono
    (fun _ => le_rfl) hm1).bind fun kc m2 hm2 => ?_
  refine ((rootFSMulti_pot (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo 0 lam
    (prng.init kr) s (fun _ => n) (fun _ _ _ => rfl) ({} : FSMultiState T RSt K I E)).mono
    (fun _ => le_rfl) hm2).bind fun ⟨⟨σ, k, sid⟩, h1⟩ m3 hm3 => ?_
  refine ((regSessOptMulti_pot (SS := SS) (RS := RS) (M := M) s (fun _ => n) (fun _ _ _ => rfl)
    sid h1).mono (fun _ => le_rfl) hm3).bind fun ⟨optIdx, h2⟩ m4 hm4 => ?_
  exact PotBound.pure hm4

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

/-- Per-session `min (2 * q) (q + 2)` query bound on `redFSAuthDFShiftedPaperMultiGen`. -/
theorem redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) := by
  suffices h : (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => sessPred s x = true) (min (2 * q) (q + 2)) by
    convert h using 1; funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  have hq' := hq_to_isInrQuery hq
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  rw [bind_assoc]
  let hk := hooksFSMulti cka prng fs Δcka ⟨authH, some (l - 1), t⟩ false la
  let impl := implEDFShiftedPaperGen (!authH) l hk (2 + Δcka) qep fs.maxSkip t
    (⟨true, some (l - 1), t⟩ : Mode).cfg (⟨true, some (l - 1), t⟩ : Mode).policy
  have hkPot := hooksFSMulti_shallowHooksPot cka prng fs Δcka ⟨authH, some (l - 1), t⟩ false la s
  rcases q with _ | q'
  · refine (isQueryBoundP_bind (m := 0)
      (initFSMultiRaw_pot cka prng fs lam _ false s 0).to_isQueryBoundP
      fun es₀ _ => ?_).mono (by omega)
    exact isQueryBoundP_bind
      (isQueryBoundP_simulateQ_run_of_zero_inr (sessPred s) impl
        (fun u st => (coinsE_pot (pot := fun _ => 0) (fun _ => rfl) u st 0).to_isQueryBoundP)
        A hq' es₀)
      fun _ _ => isQueryBoundP_pure _ _ 0
  · have hInit := (initFSMultiRaw_pot cka prng fs lam ⟨authH, some (l - 1), t⟩ false s (q' + 2)).mono
      (fun es₀ => show (q' + 1) + potMulti s es₀.h ≤ q' + 2 by dsimp [potMulti]; split <;> omega)
      le_rfl
    have hAll : PotBound (sessPred s) (fun _ => 0)
        (initFSMultiRaw cka prng fs lam ⟨authH, some (l - 1), t⟩ false >>= fun es₀ =>
          (simulateQ impl A).run es₀ >>= fun (_, es) =>
            pure (if la then es.h.lfWin else authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy es))
        (q' + 2) :=
      hInit.bind fun es₀ m hm =>
        ((potBound_simulateQ_run (sessPred s) (fun es => potMulti s es.h) impl
          (fun u st rem => coinsE_pot (fun _ => rfl) u st rem)
          (fun qr st rem => implEDFShiftedPaperGen_inr_pot hkPot (!authH) l (2 + Δcka) qep
            fs.maxSkip t _ _ qr st rem)
          (q' + 1) A hq' es₀).mono (fun _ => Nat.zero_le _) hm).bind fun (_, _) m2 _ =>
          PotBound.pure (Nat.zero_le m2)
    exact hAll.to_isQueryBoundP.mono (by omega)

/-- Per-session `2 * q` query bound on `redFSAuthDFShiftedPaperMultiGen`. -/
theorem redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min cka prng fs lam q Δcka qep l t
    authH la A hq s).mono (Nat.min_le_left _ _)

/-- Per-session `min (2 * q) (q + 2)` query bound on `redFSAuthDFPaperMulti`. -/
theorem redFSAuthDFPaperMulti_sess_isQueryBoundP_min
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) := by
  suffices h : (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => sessPred s x = true) (min (2 * q) (q + 2)) by
    convert h using 1; funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  have hq' := hq_to_isInrQuery hq
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper
  rw [bind_assoc]
  let hk := hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la
  let impl := implEDFPaper hk (2 + Δcka) qep fs.maxSkip
    (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy
  have hkPot := hooksFSMulti_shallowHooksPot cka prng fs Δcka ⟨true, tL, t⟩ false la s
  rcases q with _ | q'
  · refine (isQueryBoundP_bind (m := 0)
      (initFSMultiRaw_pot cka prng fs lam _ false s 0).to_isQueryBoundP
      fun es₀ _ => ?_).mono (by omega)
    exact isQueryBoundP_bind
      (isQueryBoundP_simulateQ_run_of_zero_inr (sessPred s) impl
        (fun u st => (coinsE_pot (pot := fun _ => 0) (fun _ => rfl) u st 0).to_isQueryBoundP)
        A hq' es₀)
      fun _ _ => isQueryBoundP_pure _ _ 0
  · have hInit := (initFSMultiRaw_pot cka prng fs lam ⟨true, tL, t⟩ false s (q' + 2)).mono
      (fun es₀ => show (q' + 1) + potMulti s es₀.h ≤ q' + 2 by dsimp [potMulti]; split <;> omega)
      le_rfl
    have hAll : PotBound (sessPred s) (fun _ => 0)
        (initFSMultiRaw cka prng fs lam ⟨true, tL, t⟩ false >>= fun es₀ =>
          (simulateQ impl A).run es₀ >>= fun (_, es) =>
            pure (if la then es.h.lfWin else authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es))
        (q' + 2) :=
      hInit.bind fun es₀ m hm =>
        ((potBound_simulateQ_run (sessPred s) (fun es => potMulti s es.h) impl
          (fun u st rem => coinsE_pot (fun _ => rfl) u st rem)
          (fun qr st rem => implEDFPaper_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ _ qr st rem)
          (q' + 1) A hq' es₀).mono (fun _ => Nat.zero_le _) hm).bind fun (_, _) m2 _ =>
          PotBound.pure (Nat.zero_le m2)
    exact hAll.to_isQueryBoundP.mono (by omega)

/-- Per-session `2 * q` query bound on `redFSAuthDFPaperMulti`. -/
theorem redFSAuthDFPaperMulti_sess_isQueryBoundP
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (redFSAuthDFPaperMulti_sess_isQueryBoundP_min cka prng fs lam q Δcka qep tL t
    la A hq s).mono (Nat.min_le_left _ _)

/-- Per-session `min (2 * q) (q + 2)` query bound on `redFSAuthDFPaperMultiBucketGen`. -/
theorem redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucket L cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) := by
  suffices h : (redFSAuthDFPaperMultiBucket L cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => sessPred s x = true) (min (2 * q) (q + 2)) by
    convert h using 1; funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  have hq' := hq_to_isInrQuery hq
  unfold redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen engRunDFPaperBucket
    implEDFPaperBucket
  rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDF (fun c => c.1.1) (fun es => es.g.win) rawImpl
  have hkPot := hooksFSMultiDFBucketPaper_shallowHooksPot L cka prng fs Δcka Δbucket qep tL par la s
  rcases q with _ | q'
  · refine (isQueryBoundP_bind (m := 0)
      (initFSMultiDFBucketPaper_pot L cka prng fs lam Δbucket qep tL par s 0).to_isQueryBoundP
      fun ⟨vs, h⟩ _ => ?_).mono (by omega)
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact isQueryBoundP_pure _ _ 0
    · simp only [bind_assoc]
      exact isQueryBoundP_bind
        (isQueryBoundP_simulateQ_run_of_zero_inr (sessPred s) impl
          (fun u st => (withWinEpDF_pot (pot := fun _ => 0) (rem := 0) _ _ rawImpl (.inl u) st
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
        (fun u st rem => withWinEpDF_pot (pot := fun es => potBucket s es.h) (rem := rem) _ _
          rawImpl (.inl u) st (coinsE_pot (fun _ => rfl) u st.1 rem))
        (fun qr st rem => withWinEpDF_pot (pot := fun es => potBucket s es.h) (rem := rem) _ _
          rawImpl (.inr qr) st (implEDFPaperBucketRaw_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ qr st.1 rem))
        (q' + 1) A hq' (es₀, none)).mono (fun _ => Nat.zero_le _) hm).bind fun _ m2 _ =>
        PotBound.pure (Nat.zero_le m2)

/-- Per-session `2 * q` query bound on `redFSAuthDFPaperMultiBucketGen`. -/
theorem redFSAuthDFPaperMultiBucket_sess_isQueryBoundP
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucket L cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min L cka prng fs lam q Δcka Δbucket qep
    tL par la A hq s).mono (Nat.min_le_left _ _)

end

end Computational.Proofs.E2E.SessionAuthMultiPot
